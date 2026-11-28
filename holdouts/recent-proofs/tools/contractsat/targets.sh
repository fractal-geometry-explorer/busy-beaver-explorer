#!/bin/bash
# structured (run-length) classes on the four targets; window at the right end (leftward trips)
O=$1
for M in 1RB---_1LC0RF_1RF0LD_0LE1LC_0RC0LC_1RB0RA 1RB0LA_0RC1LF_0RD0LA_1LD0LE_1RB1LF_---1LA 1RB0RE_1LC0RD_1LD0LD_1RA0LC_1RA1RF_1RA--- 1RB0LB_1RC1LE_1LD0RF_---1LB_0LA0LC_1LB1RA; do
for W in 8 16; do for b in 0 1; do for Z in 2 4; do for D in 2 3 4 5; do
  timeout 150 python3 -u contractsat.py $M R 0 $W --runs $b,$Z,$D --tlimit 90 --out $O.$M.$W.$b.$Z.$D.json 2>&1 | grep -E "^(CERT|NONE|TIMEOUT)" | sed "s/\$/ runs=$b,$Z,$D/" >> $O
done; done; done; done; done
