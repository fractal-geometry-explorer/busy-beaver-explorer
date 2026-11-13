"""Run a two-counters machine with the tick jumps of counters.py and print every change of counter layout (a new
header or a new width of V: the resets).

usage: python3 run_counters.py MACHINE [MAX_STEPS] [SECONDS]
"""
import sys, time, signal
from counters import make

M = sys.argv[1]
maxs = float(sys.argv[2]) if len(sys.argv) > 2 else 1e300
secs = float(sys.argv[3]) if len(sys.argv) > 3 else 600
t0 = time.time()
c = make(M)
last = [None]


class Timeout(Exception):
    pass


def on_tick(c, lc, key, V, nb):
    if time.time() - t0 > secs:
        raise Timeout
    if (key, nb) != last[0]:
        G, H = key
        Vs = str(V) if nb < 64 else f"2^{nb} - {2 ** nb - V}" if 2 ** nb - V < 2 ** 40 else f"~2^{V.bit_length()}"
        print(f"steps~10^{len(str(c.steps)) - 1} ({c.steps if c.steps < 10 ** 30 else '...'})  gap={G} header={H}  "
              f"U: {lc[0]} digits  V: {nb} digits, V={Vs}  width={c.hi - c.lo + 1}  t={time.time() - t0:.0f}s",
              flush=True)
        last[0] = (key, nb)


try:
    r = c.run(maxs, max_direct=10 ** 10, on_tick=on_tick)
    print(r, "after", c.steps, "steps")
except Timeout:
    print(f"time limit: no halt in the first {c.steps} steps (~10^{len(str(c.steps)) - 1})")
