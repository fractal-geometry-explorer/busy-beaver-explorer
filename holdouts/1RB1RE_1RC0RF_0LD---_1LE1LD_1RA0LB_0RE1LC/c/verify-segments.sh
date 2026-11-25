#!/bin/bash
# plain-simulate each consecutive pair of kept checkpoints (keep/ck_*.txt, keep/ck_500000000000.snap) and compare.
# used in /tmp/claude-0/s/r6 next to the fixed run (keep/ holds its kept checkpoints, plainfrom and tapecmp.py are copied there).
# results in vres/; worker W of NW handles pairs with index % NW == W. idempotent.
cd /tmp/claude-0/s/r6; mkdir -p vres vtmp
W=$1; NW=$2; M=1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE1LC
while true; do
  mapfile -t F < <(ls keep/ | grep '^ck_' | sed 's/ck_\([0-9]*\)\..*/\1 &/' | sort -n | awk '{print $2}')
  did=0
  for ((i=0;i+1<${#F[@]};i++)); do
    (( i % NW == W )) || continue
    a=${F[$i]}; b=${F[$((i+1))]}; sa=${a//[^0-9]/}; sb=${b//[^0-9]/}
    [ -e vres/$sa-$sb ] && continue
    ./plainfrom $M keep/$a $((sb-sa)) vtmp/p$W.txt > vtmp/o$W.txt 2>/dev/null
    r=$(python3 tapecmp.py vtmp/p$W.txt keep/$b | cut -c1-5); echo "$r $(cat vtmp/o$W.txt)" > vres/$sa-$sb; did=1
  done
  [ $did = 0 ] && sleep 120
done
