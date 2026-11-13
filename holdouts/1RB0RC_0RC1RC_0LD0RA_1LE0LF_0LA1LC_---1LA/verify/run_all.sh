#!/bin/bash
# Re-runs every check reported in README.md (about 3 minutes on one core, excluding the optional -nonest cross-check).
set -u
cd "$(dirname "$0")"
g++ -O2 -o sim3 sim3.cpp && g++ -O2 -o plain plain.cpp || exit 1
C65s=$(python3 -c "print('0'+'1011001'*59+'1011'+'00000'+'1101100110110'+'011'*16+'001101100110'+'011'*65)")
C65="E 0 1011001^59 1011 00000 1101100110110 011^16 001101100110 011^65"
echo "== validation against plain cell-by-cell simulation =="
for T in 1000 123456789 3000000000 ${BIG:-10000000000}; do ./plain $T 3 > p.txt; ./sim3 $T > s.txt 2>/dev/null; ./sim3 -1 $([ $T -gt 3000000000 ] && echo 3000000000 || echo $T) > s1.txt 2>/dev/null
  echo "blank tape, step $T: $(python3 cmp.py plain:p.txt sim:s.txt | tail -1)"; done
for T in 777777 2000000000; do ./plain $T 3 E $C65s > p.txt; ./sim3 $T $C65 > s.txt 2>/dev/null; echo "C(65), step $T: $(python3 cmp.py plain:p.txt sim:s.txt | tail -1)"; done
echo "== claim (b) =="
./sim3 1818198163340705 > b.txt 2>/dev/null; head -1 b.txt; python3 cmp.py sim:b.txt C:16797709 | tail -1
echo "== claim (a) =="
for r in 65 67 16797709 ${EXTRA_A:-}; do ./check_a.sh $r; done
echo "== claim (c) =="
for r in 64 66 ${EXTRA_C:-}; do ./check_c.sh $r; done
