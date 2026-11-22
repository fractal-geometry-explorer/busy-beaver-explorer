#!/bin/bash
# The C++ list machine of holdouts/1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF/c/listmachine.cpp, started from the first
# right turn of the Pascal table started in D (1RB1RA_1LC0RF_1LD1LC_1LE0LB_0LF---_1RA1RB) or C
# (1RB1RC_1RC1RB_1LD0RA_1LE1LD_1LF0LC_0LA---) instead of A; the start states are those of lean/Mirror.lean.
#   usage: c/mirror_lm.sh D|C K      (K list steps)
set -e
HERE="$(cd "$(dirname "$0")" && pwd)"
SRC="$HERE/../../1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF/c/listmachine.cpp"
case "$1" in
  D) START='St st{2,V{1,0,1,0,0,0},V(),V(),0,0,0};' ;;   # EO [b, a, b, a, a, a] none 0, step 46
  C) START='St st{2,V{1,0,1,0},V(),V(),1,0,0};' ;;       # EO [b, a, b, a] none 1, step 26
  *) echo "usage: $0 D|C K"; exit 1 ;;
esac
T="$(mktemp -d)"
grep -q 'St st{2,V{1,0},V(),V(),1,0,0};' "$SRC"
sed "s/St st{2,V{1,0},V(),V(),1,0,0};/$START/" "$SRC" > "$T/lm.cpp"
g++ -O2 -o "$T/lm" "$T/lm.cpp"
"$T/lm" "$2"
