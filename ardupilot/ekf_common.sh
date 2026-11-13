# Shared by the EKF translation scripts (sourced; ROOT must be set): the reference build's flags
# (ardupilot/ref_flags.py), the reference build's libraries (RL: byte-identical to ArduPilot's checkout
# except the board header guard of reference/patches, which only the build copy has), the unity check.
REF="${CPP2LEAN_REF:-$ROOT/build/reference/ap}"
RL="$REF/libraries"
AP="${AP:-$ROOT/ardupilot/src}"

# ekf_flags SOURCE: EKF_FLAGS (the AST flags of SOURCE's unit in the reference build) and EKF_CA (as
# --clang-arg options for cpp2lean)
ekf_flags() {
  EKF_FLAGS=()
  while IFS= read -r a; do EKF_FLAGS+=("$a"); done < <(python3 "$ROOT/ardupilot/ref_flags.py" --ast "$1")
  EKF_CA=()
  for a in "${EKF_FLAGS[@]}"; do EKF_CA+=("--clang-arg=$a"); done
}

# ekf_check_unity UNITY SRC...: every SRC (relative to libraries/) is the unmodified file of ArduPilot's
# checkout; preprocessed alone, it gives the same text with the unity's flags (EKF_FLAGS) as with the
# flags of its own unit in the reference build; and it preprocesses in the unity exactly as alone (an
# argument --rename=SRC:OLD=NEW is passed to check_unity.py: a file-static name the unity renames)
ekf_check_unity() {
  local unity="$1"; shift
  local srcs=() own=() a
  for s in "$@"; do
    case "$s" in --rename=*) srcs+=("--rename=$RL/${s#--rename=}"); continue;; esac
    cmp -s "$RL/$s" "$AP/libraries/$s" || { echo "$s differs from ArduPilot's checkout" >&2; exit 1; }
    srcs+=("$RL/$s")
    own=()
    while IFS= read -r a; do own+=("$a"); done < <(python3 "$ROOT/ardupilot/ref_flags.py" --ast "$s")
    if ! cmp -s <(clang++ "${own[@]}" -E -P "$RL/$s" 2>/dev/null) <(clang++ "${EKF_FLAGS[@]}" -E -P "$RL/$s" 2>/dev/null); then
      echo "$s preprocesses differently with the unity's flags than in its own unit" >&2; exit 1
    fi
  done
  local check=(python3 "$ROOT/ardupilot/check_unity.py" "$unity" "${srcs[@]}" -- "${EKF_FLAGS[@]}")
  "${check[@]}" > /dev/null || { "${check[@]}" | grep -v "the same"; exit 1; }
}
