#!/bin/bash
# RepWL grid for one machine: rwsweep.sh MACHINE  (needs ./repwl: g++ -O2 -I tools/c -o repwl tools/c/repwl.cpp)
# block length L x threshold T, 300,000 configurations, 2,000 steps per block for L > 16, 20 s, 2.5 GB per run
m=$1; out=""
for L in 1 2 3 4 5 6 7 8 9 10 11 12 14 16 20 24 28 32 40 48; do for T in 2 3 4; do
  r=$(bash -c "ulimit -v 2500000; timeout 20 ./repwl $m $L $T 300000 2000" 2>/dev/null || echo "TIMEOUT/OOM")
  out="$out $L,$T:${r%% *}"
  if [[ $r == NONHALT* ]]; then echo "$m DECIDED $L $T $r"; exit; fi
done; done
echo "$m none$out"
