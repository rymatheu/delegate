#!/usr/bin/env bash
# compile_one.sh SRC: one source (relative to $ARDUPILOT_ROOT, or absolute) with $OUT/flags.rsp
src="$1"; base="$(basename "$(dirname "$src")")_$(basename "$src" .cpp)"
case "$src" in /*) path="$src" ;; *) path="$ARDUPILOT_ROOT/$src" ;; esac
if (cd "$OUT/obj" && "$CXX" @"$OUT/flags.rsp" -c "$path" -o "$OUT/obj/$base.o") > "$OUT/log/$base.log" 2>&1
then echo "ok   $src"; else rm -f "$OUT/obj/$base.o"; echo "FAIL $src"; fi
