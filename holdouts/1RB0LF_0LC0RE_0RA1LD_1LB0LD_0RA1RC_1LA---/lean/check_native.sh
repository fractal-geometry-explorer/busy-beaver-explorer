#!/bin/bash
# Check FILE.lean (whose `native_decide` runs the excursion checker of ResetExc.lean for many phases) with that
# checker compiled to native code, as Lake's `precompileModules` would do it: C code for every module ResetExc.lean
# uses, one shared library, loaded into lean with --load-dynlib.  The trust is that of native_decide (the Lean
# compiler); the interpreter is about 12 times slower on these checks.  Run check.sh first (it builds the .olean
# files this needs).   usage: check_native.sh FILE.lean...
set -e
cd "$(dirname "$0")"
LEAN=${LEAN:-lean}
LEANBIN="$(dirname "$(readlink -f "$(command -v "$LEAN")")")"
if [ -z "$LEANLIB" ]; then LEANLIB="$LEANBIN/../lib/lean"; fi
TOOLS="$(cd ../../../tools/lean && pwd)"
HERE="$(pwd)"
export LEAN_PATH="$LEANLIB:$TOOLS/out:$HERE/out"
C="$HERE/out/c"
mkdir -p "$C"
for f in Basic Fin CTL ListFrame Sync Insert Resync Rounds RLE MapOrbit RSim; do
  (cd "$TOOLS" && "$LEAN" TM/$f.lean -c "$C/TM_$f.c")
done
(cd "$TOOLS" && "$LEAN" TM.lean -c "$C/TM.c")
for f in Machine Twin29537 ResetMapRuns ResetMap ExcSim ResetExc SymSim TailHash; do
  "$LEAN" $f.lean -c "$C/$f.c"
done
for f in "$C"/*.c; do
  "$LEANBIN/leanc" -c -O2 -fvisibility=default "$f" -o "${f%.c}.o"
done
"$LEANBIN/leanc" -shared -Wl,--no-gc-sections -o "$C/libTailHash.so" "$C"/*.o
for f in "$@"; do
  echo "== $f (native checker)"
  start=$(date +%s)
  "$LEAN" --load-dynlib="$C/libTailHash.so" "$f"
  echo "   $(( $(date +%s) - start )) s"
done
