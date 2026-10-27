#!/bin/bash
# Check the evaluated theorems of this folder (run ../lean/check.sh and ../lean/check_end.sh first, which build
# ../lean/out and the shared library ../lean/cbuild/so/libBB6all.so that native_decide runs).
# usage: LEAN=/path/to/lean LEANLIB=/path/to/lib/lean ./check.sh
set -e
cd "$(dirname "$0")/../lean"
LEAN=${LEAN:-lean}
export LEAN_PATH="$LEANLIB:$PWD/out"
s=$(date +%s)
$LEAN --load-dynlib=cbuild/so/libBB6all.so ../integ/SpineCount.lean
echo "== integ/SpineCount.lean ($(( $(date +%s) - s )) s)"
