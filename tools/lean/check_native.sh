#!/bin/bash
# Check Lean files whose `native_decide` evaluations are long, with compiled code loaded.
#
# `native_decide` evaluates with Lean's interpreter, which calls compiled code for every definition of a module
# whose code is loaded.  This script compiles the shared library (tools/lean, TM.*) and the given modules of DIR to
# C, then to one shared library with `leanc` (part of the Lean toolchain), and checks the files CHECK... with it
# loaded (`lean --load-dynlib`).  The proofs are the same as without it; only the evaluation is faster (about 10x).
#
# usage: LEAN=/path/to/lean LEANLIB=/path/to/lib/lean tools/lean/check_native.sh DIR "MODULE.lean..." CHECK.lean...
#   DIR      the directory the files' module names are relative to (as for check.sh)
#   MODULE   the modules to compile (in dependency order, the ones CHECK imports); quoted, space separated
#   CHECK    the files to check with the library loaded
set -e
HERE="$(cd "$(dirname "$0")" && pwd)"
LEAN=${LEAN:-lean}
if [ -z "$LEANLIB" ]; then LEANLIB="$(dirname "$(command -v "$LEAN")")/../lib/lean"; fi
LEANC="$(dirname "$(command -v "$LEAN")")/leanc"
DIR="$(cd "$1" && pwd)"; shift
MODS="$1"; shift
# the .olean files first (check.sh compiles the library and the modules)
"$HERE/check.sh" "$DIR" $MODS > /dev/null
NAT="$DIR/out/native"
rm -rf "$NAT"; mkdir -p "$NAT"
export LEAN_PATH="$LEANLIB:$HERE/out:$DIR/out"
cc() {  # cc SRC_DIR FILE NAME
  (cd "$1" && $LEAN "$2" -c "$NAT/$3.c")
  "$LEANC" -c -O3 -DLEAN_EXPORTING -fvisibility=default "$NAT/$3.c" -o "$NAT/$3.o"
}
for f in Basic Fin CTL ListFrame Sync Insert Resync Rounds RLE RSim; do cc "$HERE" "TM/$f.lean" "TM_$f"; done
cc "$HERE" TM.lean TM_all
for f in $MODS; do cc "$DIR" "$f" "M_${f%.lean}"; done
"$LEANC" -shared -o "$NAT/lib.so" "$NAT"/*.o -Wl,--no-gc-sections
for f in "$@"; do
  echo "== $f (compiled code loaded)"
  start=$(date +%s)
  (cd "$DIR" && $LEAN --load-dynlib="$NAT/lib.so" "$f")
  echo "   $(( $(date +%s) - start )) s"
done
echo "ALL CHECKED"
