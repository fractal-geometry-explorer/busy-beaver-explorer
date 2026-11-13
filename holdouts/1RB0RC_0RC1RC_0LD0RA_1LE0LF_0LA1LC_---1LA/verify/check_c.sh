#!/bin/bash
# usage: check_c.sh r   -- checks claim (c) for one even r (runs with a huge step limit; reports halting step)
r=$1; shift
T=$(python3 -c "print(21481836136725388 + 804932736*($r-64))")
./sim3 "$@" 100000000000000000000000 E 0 1011001^59 1011 00000 1101100110110 011^16 001101100110 011^$r > c_$r.txt 2> c_$r.log
echo "r=$r claimed halt step $T : $(head -1 c_$r.txt)"
