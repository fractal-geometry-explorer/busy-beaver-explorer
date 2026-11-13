"""Tape (tokenized) at the last N side switches of a tmrun records log, and the cost of a switch.

usage: python3 switches.py LOG [WORDS] [N]
A side switch is a tape extension on the other side from the previous one.  Also prints, for the switches after step
5*10^8, the mean number of steps between switches (and that over w^2, w the last width) and the mean width gain.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from shape import cells_of, tokenize
words = dict(kv.split("=") for kv in sys.argv[2].split(",")) if len(sys.argv) > 2 and sys.argv[2] else {}
N = int(sys.argv[3]) if len(sys.argv) > 3 else 20
prev, out = None, []
for l in open(sys.argv[1]):
    p = l.split(None, 3)
    if len(p) < 4 or not p[0].isdigit() or p[1] not in "LR":
        continue
    if p[1] != prev:
        c, h = cells_of(p[3])
        out.append((p[0], p[1], p[2], h[0] if h else "", tokenize(c, words)))
    prev = p[1]
print("side switches:", len(out))
for o in out[-N:]:
    print(*o)
last = [(int(o[0]), int(o[2])) for o in out if int(o[0]) > 5 * 10**8]
if len(last) > 1:
    dt = (last[-1][0] - last[0][0]) / (len(last) - 1)
    w = last[-1][1]
    dw = (last[-1][1] - last[0][1]) / (len(last) - 1)
    print(f"after step 5*10^8: {len(last)} switches, {dt:.0f} steps per switch = {dt / w**2:.3f} w^2 (w = {w}),"
          f" width gain {dw:.2f} per switch")
