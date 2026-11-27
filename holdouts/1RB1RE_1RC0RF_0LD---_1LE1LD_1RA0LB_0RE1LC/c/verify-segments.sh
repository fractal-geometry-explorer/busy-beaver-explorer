#!/bin/bash
# The plain check as it now runs (a longrun job, /mnt/project-files/tools/longrun): $LR_CKPT is the job's checkpoint directory,
# plainfrom (c/plainfrom.c) and tapecmp.py (py/tapecmp.py) sit in the working directory. Usage: verify-segments.sh W NW
# longrun program: plain-simulation check of the fixed accelerated run of 1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE1LC.
# Takes consecutive kept checkpoints in $KEEP (written once by the accelerator job), runs plainfrom from one to the
# next and compares tape, head and state (tapecmp.py). Worker $1 of $2 does the pairs whose index % $2 == $1.
# Results: one small file per pair in $LR_CKPT/vres/ (written by rename). Never finishes by itself.
# A long pair saves its plain state every 300 s to $LR_CKPT/part/<a>-<b> (tape, then steps done), so a chunk end resumes mid-pair.
W=$1; NW=$2; M=1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE1LC
KEEP=/mnt/project-files/lead16-0RE1LC/keep; C=$LR_CKPT; mkdir -p $C/vres $C/part
trap 'kill $P 2>/dev/null; exit 143' TERM
while true; do
  mapfile -t F < <(ls $KEEP | grep -E '^ck_[0-9]+\.(txt|snap)$' | sed 's/ck_\([0-9]*\)\..*/\1 &/' | sort -n | awk '{print $2}')
  did=0
  for ((i=0;i+1<${#F[@]};i++)); do
    (( i % NW == W )) || continue
    a=${F[$i]}; b=${F[$((i+1))]}; sa=${a//[^0-9]/}; sb=${b//[^0-9]/}
    [ -e $C/vres/$sa-$sb ] && continue
    pf=$C/part/$sa-$sb; src=$KEEP/$a; d=0
    if [ -s $pf ] && d=$(sed -n 3p $pf) && [ -n "$d" ]; then cp $pf resume.txt; src=resume.txt; else d=0; fi
    ./plainfrom $M $src $((sb-sa-d)) p.txt $pf 300 $d > o.txt 2>/dev/null & P=$!; wait $P
    grep -qE "HALT|no halt" o.txt || { sleep 5; continue; }
    r=$(python3 tapecmp.py p.txt $KEEP/$b | cut -c1-5)
    echo "$r $(cat o.txt)" > $C/vres/$sa-$sb.tmp && mv $C/vres/$sa-$sb.tmp $C/vres/$sa-$sb; rm -f $pf
    echo "worker $W/$NW: last $sa-$sb $r; $(ls $C/vres | wc -l) results" > $C/PROGRESS.tmp && mv $C/PROGRESS.tmp $C/PROGRESS
    did=1
  done
  [ $did = 0 ] && { sleep 120 & P=$!; wait $P; }
done
