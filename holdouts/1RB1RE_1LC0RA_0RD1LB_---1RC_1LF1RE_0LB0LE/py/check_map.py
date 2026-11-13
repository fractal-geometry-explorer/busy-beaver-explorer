"""Compare the map with the machine: c/samples.c prints the samples W p 0 r (`0 (10)^p 0 1^r E> 0`) of a run from
blank tape; check that they are the orbit of (2, 1) under the map of orbit.py.

usage: gcc -O2 -o /tmp/samples holdouts/<M>/c/samples.c && /tmp/samples 1000000000 | python3 holdouts/<M>/py/check_map.py
"""
import sys


def f(p, r):
    if r >= p + 2:
        return (2 * p + 2, r - p - 1)
    if r == p + 1:
        return None
    if r == p:
        return (2, 4 * p + 1)
    return (p - r, 4 * r + 2)


samples = []
for line in sys.stdin:
    a = line.split()
    if a[0].isdigit():
        samples.append((int(a[1]), int(a[2])))
    else:
        print(line.strip())
x, orbit = (2, 1), []
for _ in samples:
    orbit.append(x)
    x = f(*x)
print(len(samples), 'samples; equal to the orbit of (2, 1):', samples == orbit)
print('first:', samples[:8])
