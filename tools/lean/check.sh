#!/bin/bash
# Compile Lean files in the order given, with a lean binary and its library (no Lake).  The shared library in
# tools/lean (TM.*) is always compiled first, into tools/lean/out, which every later file can import.
#
# usage: LEAN=/path/to/lean LEANLIB=/path/to/lib/lean tools/lean/check.sh [DIR FILE...]
#   DIR    the directory the files' module names are relative to (their .olean files go to DIR/out)
#   FILE   paths relative to DIR, in dependency order
# With no arguments it checks only the library and its tests.
set -e
HERE="$(cd "$(dirname "$0")" && pwd)"
LEAN=${LEAN:-lean}
if [ -z "$LEANLIB" ]; then LEANLIB="$(dirname "$(command -v "$LEAN")")/../lib/lean"; fi
mkdir -p "$HERE/out/TM"
export LEAN_PATH="$LEANLIB:$HERE/out"
for f in Basic Fin; do
  echo "== tools/lean/TM/$f.lean"
  (cd "$HERE" && $LEAN TM/$f.lean -o out/TM/$f.olean)
done
(cd "$HERE" && $LEAN TM.lean -o out/TM.olean)
if [ $# -eq 0 ]; then
  mkdir -p "$HERE/out/Test"
  for f in BB2 BB4 Examples; do
    echo "== tools/lean/Test/$f.lean"
    (cd "$HERE" && $LEAN Test/$f.lean -o out/Test/$f.olean)
  done
  echo "ALL CHECKED"
  exit 0
fi
DIR="$(cd "$1" && pwd)"; shift
mkdir -p "$DIR/out"
export LEAN_PATH="$LEAN_PATH:$DIR/out"
for f in "$@"; do
  mod="${f%.lean}"
  mkdir -p "$DIR/out/$(dirname "$mod")"
  echo "== $f"
  (cd "$DIR" && $LEAN "$f" -o "out/$mod.olean")
done
echo "ALL CHECKED"
