"""Tests of chain.py against the direct run (python3 py/test_chain.py [max_visit]; about a minute)."""
import sys
from chain import *

MAXV = int(sys.argv[1]) if len(sys.argv) > 1 else 6000
D = direct(MAXV)

# 1. every visit cell by cell (no jumps), through the events at 97 and 1481: n, R and the step count
v, n, R, steps = 2, D[2][1], D[2][2], D[2][0]
cmp, bad, events = 0, 0, []
def log(v_, n_, R_, s_, what, data):
    global cmp, bad
    if what == "visit" and v_ in D:
        cmp += 1
        bad += (s_, n_, R_) != D[v_]
LIM = min(MAXV, 2200)
while v < LIM:
    r = run(v, n, R, steps, max_pass=(LIM - v) // 2 + 1, log=log, use_jump=False)
    if r[0] == "EVENT":
        fresh, tail = r[3]
        events.append(r[1] - 1)
        v, n, R, steps = r[1], r[2], b"\x00\x01" * fresh + tail, r[4]
        cmp += 1
        bad += (steps, n, R) != D[v]
    else:
        v, n, R, steps = r[1], r[2], r[3], r[4]
print(f"cell-by-cell visits compared with the direct run (step, n, R): {cmp}, mismatches {bad}, events after "
      f"visits {events}")
assert bad == 0 and events[-2:] == [97, 1481]

# 2. with jumps, from visit 100 (epoch 2) and from visit 1488 (epoch 3): everything logged is compared
for v0 in (100, 1488):
    if v0 >= MAXV:
        continue
    cmp, bad, jumps = 0, 0, 0
    def log2(v_, n_, R_, s_, what, data):
        global cmp, bad, jumps
        if what in ("jump", "visit") and v_ in D:
            cmp += 1
            bad += (s_, n_, R_) != D[v_]
            jumps += what == "jump"
    lim = 1481 if v0 == 100 else MAXV
    r = run(v0, D[v0][1], D[v0][2], D[v0][0], max_visit=lim, log=log2)
    print(f"with jumps from visit {v0} to {r[1]}: {cmp} configurations compared, {jumps} of them after a jump, "
          f"mismatches {bad}")
    assert bad == 0 and jumps > 0

# 3. the chain arithmetic alone, epoch 3: the state after every number of double visits from visit 1488
if MAXV > 1500:
    n0, R0 = D[1488][1], D[1488][2]
    st, bad, cmp = parse_chain(R0), 0, 0
    for v in range(1490, MAXV, 2):
        arr = arrivals(st, (v - 1488) // 2)
        Rv = set_chain(R0, [(st[j] + arr[j]) % 4 for j in range(len(st))])
        cmp += 1
        bad += (D[1488][0] + jump_steps(st, arr, n0), n0 + 2 * (v - 1488), Rv) != D[v]
    print(f"closed form after k double visits from visit 1488 (chain of {len(st)} counters): {cmp} compared, "
          f"mismatches {bad}")
    assert bad == 0
print("ALL OK")
