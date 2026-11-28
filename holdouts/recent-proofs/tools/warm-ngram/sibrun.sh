#!/bin/bash
read h m d p <<< "$1"; set -- $p
for simT in 1001 10000 100000 1000000 10000000; do
 case $d in CPS_LRU) k=CPS;; RWL_mod) k=RWL;; esac
 r=$(timeout 120 ./wblk $h $k $simT $4 $5 $6 $7 $8 $9 -S $3 -C 5000000 || echo TIMEOUT)
 echo "$h $m $d $simT $r"
done
