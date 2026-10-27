"""Left halving runs during the longest cascade of a cycle: start position p, predicted length v2(p) - 1,
actual length; and halving rounds per cascade meeting."""
import sys, tracecycle as T
from fuel import run
def v2(x):
    c = 0
    while x and x % 2 == 0: x //= 2; c += 1
    return c
def analyse(n, verbose=False):
    starts, best = run(n)
    r0, r1 = best[0][0], best[-1][0]
    runs = []; cur = None; halving_rounds = 0
    for i in range(max(0, r0 - 12), r1 + 1):
        w, ms = starts[i]
        lead = ms[1] if len(ms) > 1 else None
        is_halving = lead is not None and lead[0] == "M" and lead[1] % 4 == 0 and lead[1] > 4
        if lead is not None and lead[0] == "M":
            p = lead[1]
            if cur is None or p * 2 != cur["last"]:
                if cur: runs.append(cur)
                cur = dict(start=p, round=i, pred=v2(p) - 1, actual=0, last=p)
            else:
                cur["last"] = p
            if p % 4 == 0: cur["actual"] += 1
        else:
            if cur: runs.append(cur); cur = None
        if i >= r0 and is_halving: halving_rounds += 1
    if cur: runs.append(cur)
    return best, runs, halving_rounds
for n in map(int, sys.argv[1:]):
    best, runs, hr = analyse(n)
    ok = all(r["pred"] == r["actual"] for r in runs if r["round"] + r["actual"] <= best[-1][0])
    print(f"n = {n}: cascade {len(best)} meetings; halving rounds during it {hr} ({hr / len(best):.2f} per meeting); "
          f"runs (start trailing-zeros → length): {[(v2(r['start']), r['actual']) for r in runs]}; length = v2(p) - 1 for completed runs: {ok}")
