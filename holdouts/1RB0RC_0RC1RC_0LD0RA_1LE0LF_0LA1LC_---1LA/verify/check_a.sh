#!/bin/bash
# usage: check_a.sh r [extra sim3 options]   -- checks claim (a) for one odd r
r=$1; shift
T=$(python3 -c "print(650373336347246654 + 4382930856*($r-65))")
./sim3 "$@" $T E 0 1011001^59 1011 00000 1101100110110 011^16 001101100110 011^$r > a_$r.txt 2> a_$r.log
echo "r=$r T=$T : $(head -1 a_$r.txt)"; python3 cmp.py sim:a_$r.txt C:$((r+321042928)) | tail -1
