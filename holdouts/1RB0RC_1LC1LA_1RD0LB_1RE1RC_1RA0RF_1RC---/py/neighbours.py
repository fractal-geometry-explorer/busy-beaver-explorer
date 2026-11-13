"""Do tapes next to the real run halt?  Take the configuration at block-end turns of the run from blank tape, change
it a little, and run the block-level law on the result.

usage (from the repository root): python3 holdouts/MACHINE/py/neighbours.py [EVENTS] [RULES_PER_TRIAL]

Changes tried (each on one run of equal gaps of the gap list, chosen at random):
  count+1, count-1   one more / one fewer gap in the run (this flips the parity of the run)
  count+2, count-2   the same with the parity kept
  small              every run of 2s longer than 8 cut down to 6 or 7 with its parity kept
  swap               a gap 1 changed into a gap 4 or back
"""
import os
import random
import sys
from collections import Counter

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from law import Law, Halt  # noqa: E402


def rle(g):
    out = []
    for x in g:
        if out and out[-1][0] == x:
            out[-1][1] += 1
        else:
            out.append([x, 1])
    return out


def unrle(r):
    return [x for x, n in r for _ in range(n)]


def trial(q, o, g, gaps, budget):
    m = Law(0, 0)
    m.q, m.o, m.g, m.G = q, o, g, gaps[::-1]
    big = 0
    try:
        for _ in range(budget):
            m.step()
            if m.rule in ("c_turn5", "d_turn4", "d_turn3") and (m.z != float("inf")):
                big += 1
    except Halt:
        return "halt", m.steps
    return ("odd" if big else "run"), m.steps


def main(events, budget):
    random.seed(7)
    m = Law()
    snaps = []
    want = set(random.sample(range(200, 2200), events))
    ev = 0
    while len(snaps) < events:
        was = m.q
        m.step()
        if was == "B" and m.q != "B" and not m.L:
            ev += 1
            if ev in want:
                snaps.append((m.steps, m.q, m.o, m.g, m.G[::-1]))
    res = {k: Counter() for k in ("unchanged", "count+1", "count-1", "count+2", "count-2", "small", "swap")}
    first = {}
    for steps, q, o, g, gaps in snaps:
        res["unchanged"][trial(q, o, g, gaps, budget)[0]] += 1
        r = rle(gaps)
        for kind, d in (("count+1", 1), ("count-1", -1), ("count+2", 2), ("count-2", -2)):
            for _ in range(12):
                i = random.randrange(len(r))
                if r[i][1] + d < 0:
                    continue
                r2 = [list(x) for x in r]
                r2[i][1] += d
                out = trial(q, o, g, unrle(r2), budget)
                res[kind][out[0]] += 1
                if out[0] == "halt" and kind not in first:
                    first[kind] = (steps, i, r[i], out[1])
        r2 = [[x, (6 + n % 2 if (x == 2 and n > 8) else n)] for x, n in r]
        out = trial(q, o, g, unrle(r2), budget)
        res["small"][out[0]] += 1
        if out[0] == "halt" and "small" not in first:
            first["small"] = (steps, None, None, out[1])
        for _ in range(12):
            idx = [i for i, x in enumerate(gaps) if x in (1, 4)]
            if not idx:
                break
            i = random.choice(idx)
            g2 = list(gaps)
            g2[i] = 5 - g2[i]
            out = trial(q, o, g, g2, budget)
            res["swap"][out[0]] += 1
            if out[0] == "halt" and "swap" not in first:
                first["swap"] = (steps, i, gaps[i], out[1])
    print(f"{events} block-end turns of the run from blank tape (between the 200th and the 2200th), {budget} rules per trial")
    print("  halt: the law reaches the halting configuration; odd: no halt, but a rule the real run never uses inside the")
    print("  tape was used (c_turn5, d_turn3, d_turn4); run: neither")
    for k, c in res.items():
        print(f"  {k:10} trials {sum(c.values()):5}  halt {c['halt']:5}  odd {c['odd']:5}  run {c['run']:5}")
    for k, v in first.items():
        print(f"  first halt for {k}: turn at step {v[0]}, run index {v[1]} {v[2]}, halts {v[3]} steps later")


if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 40, int(sys.argv[2]) if len(sys.argv) > 2 else 20000)
