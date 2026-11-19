#!/usr/bin/env bash
# preprocess_one.sh SRC: the preprocessed text of one probe source, with line markers, to $OUT/ii
src="$1"; base="$(basename "$(dirname "$src")")_$(basename "$src" .cpp)"
mkdir -p "$OUT/ii"
"$CXX" @"$OUT/flags.rsp" -E "$ARDUPILOT_ROOT/$src" -o "$OUT/ii/$base.ii" 2>/dev/null || echo "FAIL $src"
