#!/bin/bash
# Check the Lean files of many holdout folders in parallel, compiling the shared library once.
# usage: holdouts/check_all.sh [JOBS] [FOLDER ...]      (default: 4 jobs, every folder in holdouts/)
# Prints FAIL lines for the folders that do not check; the log of each is its lean/out/check.log.
set -e
HERE="$(cd "$(dirname "$0")" && pwd)"
LEAN=${LEAN:-lean}
if [ -z "$LEANLIB" ]; then LEANLIB="$(dirname "$(command -v "$LEAN")")/../lib/lean"; fi
export LEAN LEANLIB
J=${1:-4}; shift || true
"$HERE/../tools/lean/check.sh" > /dev/null
one() {
  d="$1"; cd "$d/lean"
  mkdir -p out
  export LEAN_PATH="$LEANLIB:$HERE/../tools/lean/out:$PWD/out"
  files=$(sed -n 's/.*check.sh \. //p' check.sh)
  for f in $files; do
    mod="${f%.lean}"; mkdir -p "out/$(dirname "$mod")"
    $LEAN "$f" -o "out/$mod.olean" >> out/check.log 2>&1 || { echo "FAIL $d"; return 0; }
  done
  echo "ok $d"
}
export -f one; export HERE
if [ $# -gt 0 ]; then printf '%s\n' "$@"; else ls -d "$HERE"/1RB*/ | sed 's:/$::'; fi | xargs -P "$J" -I{} bash -c 'one {}'
