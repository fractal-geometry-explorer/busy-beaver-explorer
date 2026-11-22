"""All words of up to NB blocks with lengths from LENS (separated by single 0s, then the tail TAIL), each run for
one phase from `X>0 1 0 W` (phase_probe.phase): print the ones whose phase halts.

usage: python3 halt_words.py MACHINE NB LENS TAIL      e.g. ... 4 1,3,5,7,9 '1 1'
"""
import itertools
import sys
import phase_probe as pp
from clockx import clock

m, NB = sys.argv[1], int(sys.argv[2])
lens = [int(x) for x in sys.argv[3].split(",")]
tail = list(pp.parse(sys.argv[4])) if len(sys.argv) > 4 and sys.argv[4] else []
tot = h = 0
for nb in range(0, NB + 1):
    for ls in itertools.product(lens, repeat=nb):
        W = []
        for x in ls:
            W += [1] * x + [0]
        W = bytes(W + tail) if tail else bytes(W[:-1])
        tot += 1
        r = pp.phase(m, W, 1, limit=10 ** 30)
        if r[0] == "HALT":
            h += 1
            print(clock.rle(W), r[1], flush=True)
print("halting", h, "of", tot)
