"""Words at the first and last visit of each phase (exact accelerated run).

usage: python3 phase_words.py MACHINE LOG10STEPS [CELLS]"""
import sys
import clockx  # noqa: F401
from clockx import clock
m = sys.argv[1]
n = int(sys.argv[3]) if len(sys.argv) > 3 else 80
h = clock.Hybrid(m)
prev = None
for t, L, W in h.visits(10 ** int(sys.argv[2])):
    if t == "HALT":
        print("HALT", L)
        break
    if prev is None or L != prev[1] + h.c.g:
        if prev:
            print("  end  ", clock.sci(prev[0]), "L=%d" % prev[1], "|W|=%d" % len(prev[2]), clock.rle(prev[2][:n]))
        print("start", clock.sci(t), "L=%d" % L, "|W|=%d" % len(W), clock.rle(W[:n]), flush=True)
    prev = (t, L, W)
