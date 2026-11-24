"""Is what a long trip beyond X brings back a function of what the head leaves near X?  (trusted computation)

usage: ./returns 400000000 100000000 4500 20 | python3 py/returns.py

Reads c/returns.c.  For the trips longer than 1,000 steps (the ones that reach the right end), the key is the
state the head leaves X in and the cells X-8 .. X+K-1 at that moment, the value the state it comes back in.
Prints the number of distinct keys and how many of them come back in more than one way.
"""
import collections
import sys

seen = collections.defaultdict(set)
for line in sys.stdin:
    f = line.split()
    if len(f) == 8 and f[0] == "OUT" and int(f[5]) > 1000:
        seen[(f[2], f[3])].add(f[6])
amb = sum(1 for v in seen.values() if len(v) > 1)
print(f"{len(seen)} keys, {amb} come back in more than one state")
