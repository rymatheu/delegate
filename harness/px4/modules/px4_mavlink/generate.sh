#!/usr/bin/env bash
# What PX4's build generates for the mavlink module, with PX4's own tools (src/modules/mavlink/
# CMakeLists.txt, src/lib/version/CMakeLists.txt, src/lib/component_information/CMakeLists.txt),
# written into $GEN; nothing is written under $PX4_ROOT.
#   $GEN/mavlink/{development,uAvionix,...}   mavgen.py --lang C --wire-protocol 2.0 over the
#        dialects PX4 uses (CONFIG_MAVLINK_DIALECT "development", and uAvionix), from PX4's mavlink
#        submodule at the commit PX4 pins (33af200d), fetched into build/src/mavlink because the
#        submodule is not checked out in deps/px4 (see MAVLINK_SRC below)
#   $GEN/version/build_git_version.h          px_update_git_header.py, run in $PX4_ROOT
#   $GEN/component_information/checksums.h    generate_component_general.py and generate_crc.py,
#        over this module's parameter metadata and PX4's events metadata (common + enums)
set -euo pipefail
MAVLINK_SRC="$HARNESS/build/src/mavlink"
COMMIT=33af200d25ec6f0925b49b1ba82bbf1294ea5f72
[ "$(git -C "$MAVLINK_SRC" rev-parse HEAD)" = "$COMMIT" ] || { echo "need mavlink $COMMIT in $MAVLINK_SRC"; exit 1; }
rm -rf "$GEN/mavlink" "$GEN/version" "$GEN/component_information" "$GEN/platforms"
mkdir -p "$GEN/mavlink" "$GEN/version" "$GEN/component_information"
# reproducible headers (as ardupilot/gen_mavlink.sh): the build date mavgen writes is the mavlink commit's date,
# and Python's string hash, from which mavgen makes each dialect's XML hash, is seeded (PYTHONHASHSEED=0)
DATE="$(TZ=UTC git -C "$MAVLINK_SRC" log -1 --date=format-local:'%a %b %d %Y' --format=%cd HEAD)"
for d in uAvionix development; do
  PYTHONHASHSEED=0 "$PY" -c '
import os, runpy, sys, time
strftime, date = time.strftime, sys.argv[1]
time.strftime = lambda fmt, *t: date if fmt == "%a %b %d %Y" else strftime(fmt, *t)
tool = sys.argv[2]
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(tool)))))
sys.argv = sys.argv[2:]
runpy.run_path(tool, run_name="__main__")
' "$DATE" "$MAVLINK_SRC/pymavlink/tools/mavgen.py" --lang C --wire-protocol 2.0 --output "$GEN/mavlink" \
    "$MAVLINK_SRC/message_definitions/v1.0/$d.xml"
done
(cd "$PX4_ROOT" && "$PY" src/lib/version/px_update_git_header.py "$GEN/version/build_git_version.h" --git_tag v1.17.0)
# what px_update_git_header.py adds when the mavlink submodule is checked out
printf '\n#define MAVLINK_LIB_GIT_VERSION_STR  "%s"\n#define MAVLINK_LIB_GIT_VERSION_BINARY 0x%s\n' \
  "$COMMIT" "${COMMIT:0:16}" >> "$GEN/version/build_git_version.h"
# the posix build's builtin-app table header (platforms/posix/cmake/px4_impl_os.cmake copies it)
mkdir -p "$GEN/platforms/posix"
cp "$PX4_ROOT/platforms/common/apps.h.in" "$GEN/platforms/posix/apps.h"
# and the table itself, as px4_posix_generate_builtin_commands configures apps.cpp.in: here the
# only builtin is the module of this process
sed -e 's/\${builtin_apps_decl_string}/int mavlink_main(int argc, char *argv[]);/' \
    -e 's/\${builtin_apps_string}/apps["mavlink"] = mavlink_main;/' \
    "$PX4_ROOT/platforms/common/apps.cpp.in" > "$GEN/platforms/posix/apps.cpp"
xz -kc "$GEN/parameters/parameters.json" > "$GEN/parameters.json.xz"
xz -kc "$HARNESS/build/gen/px4/events/common_with_enums.json" > "$GEN/all_events.json.xz"
S3=https://px4-travis.s3.amazonaws.com/Firmware/{version}
"$PY" "$PX4_ROOT/src/lib/component_information/generate_component_general.py" "$GEN/component_general.json" \
  --compress --version-file "$GEN/version/build_git_version.h" \
  --type "1,$GEN/parameters.json.xz,$S3/px4_sitl_default/parameters.json.xz,$S3/_general/parameters.json.xz," \
  --type "4,$GEN/all_events.json.xz,$S3/px4_sitl_default/all_events.json.xz,$S3/_general/all_events.json.xz,"
"$PY" "$PX4_ROOT/src/lib/component_information/generate_crc.py" "$GEN/component_general.json" \
  "$GEN/all_events.json.xz" --output "$GEN/component_information/checksums.h"
echo "mavlink $COMMIT, $(git -C "$MAVLINK_SRC/pymavlink" rev-parse HEAD) (pymavlink)" > "$GEN/mavlink/source.txt"
