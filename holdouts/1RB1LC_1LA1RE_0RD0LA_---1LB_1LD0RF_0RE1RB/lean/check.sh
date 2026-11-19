#!/bin/bash
# Check this machine's Lean files with the shared library (tools/lean). LEAN, LEANLIB as for tools/lean/check.sh.
# Long.lean evaluates the certificate cert.txt with native_decide.  The checker (TM.*, Machine, Tick, Cert) is first
# compiled to a shared library with the toolchain's C compiler and loaded into Lean, about 4 minutes in all; NO_DYNLIB=1
# (or a failed build) leaves the evaluation to Lean's interpreter (much slower).
set -e
cd "$(dirname "$0")"
../../../tools/lean/check.sh . Machine.lean Blank.lean Edge.lean EdgeHalt.lean Tick.lean Cert.lean
HERE="$(pwd)"
T="$(cd ../../../tools/lean && pwd)"
LEAN=${LEAN:-lean}
BIN="$(dirname "$(command -v "$LEAN")")"
if [ -z "$LEANLIB" ]; then LEANLIB="$BIN/../lib/lean"; fi
export LEAN_PATH="$LEANLIB:$T/out:$HERE/out"
DYN=()
build() {
  mkdir -p "$HERE/out/c"
  local C="$HERE/out/c"
  (cd "$T" && $LEAN TM.lean -c "$C/TM.c" > /dev/null)
  # every module of the shared library, in the order tools/lean/check.sh compiles them
  local MODS; MODS=$(sed -n 's/^for f in \(.*\); do$/\1/p' "$T/check.sh" | head -1)
  for m in $MODS; do (cd "$T" && $LEAN TM/$m.lean -c "$C/TM_$m.c" > /dev/null); done
  for m in Machine Tick Cert; do $LEAN $m.lean -c "$C/$m.c" > /dev/null; done
  for f in "$C"/*.c; do "$BIN/leanc" -c -fPIC -O2 -DLEAN_EXPORTING -o "${f%.c}.o" "$f"; done
  "$BIN/clang" -shared -o "$C/libcert.so" "$C"/*.o
}
if [ -z "$NO_DYNLIB" ]; then
  echo "== compiling the checker"
  if build; then DYN=(--load-dynlib="$HERE/out/c/libcert.so"); else echo "(build failed: interpreter)"; fi
fi
echo "== Long.lean"
$LEAN "${DYN[@]}" ./Long.lean -o out/Long.olean
echo "ALL CHECKED"
