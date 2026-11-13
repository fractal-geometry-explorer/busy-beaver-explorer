"""Rounds of 1RB0LA_0RC---_0RD0RF_1LD0LE_0LA1LE_0RA0LA.

usage (from the repo root):
  python3 holdouts/1RB0LA_0RC---_0RD0RF_1LD0LE_0LA1LE_0RA0LA/py/rounds.py LOG
      LOG is the output of `tmrun M STEPS at E L K` (tools/c/tmrun.c): the tape each time the head is at the left
      end in state E.  Prints how many round starts have single holes only, the number of blocks, the first block
      mod 4, and checks every round from an even first block against the proved formula (lean/Round.lean):
      [4K, a, b, ...] -> [a+K, 3K+3+b, ...],  [4K+2, a, b, ...] -> [a+K, 3K+6+b, ...]  (b = 0 if absent).
  python3 holdouts/1RB0LA_0RC---_0RD0RF_1LD0LE_0LA1LE_0RA0LA/py/rounds.py trace X A ...
      one round from blocks [X, A, ...] (plain simulation), the tape each time the head turns right.
"""
import collections
import sys

M = "1RB0LA_0RC---_0RD0RF_1LD0LE_0LA1LE_0RA0LA"


def table(m):
    t = {}
    for i, g in enumerate(m.split("_")):
        for b in (0, 1):
            x = g[3 * b:3 * b + 3]
            t[(i, b)] = None if x[0] == "-" else (int(x[0]), 1 if x[1] == "R" else -1, ord(x[2]) - 65)
    return t


def blocks(body):
    """'1^5 0 1^3' -> [5, 3] if the tape is blocks of 1s separated by single 0s, else None."""
    bl, cur = [], 0
    for k in body.split():
        if k.startswith("1"):
            cur += int(k[2:]) if "^" in k else 1
        elif k == "0":
            bl.append(cur)
            cur = 0
        else:
            return None
    bl.append(cur)
    return None if 0 in bl else bl


def predict(b):
    x, K = b[0], b[0] // 4
    rest = b[2:] or [0]
    return [b[1] + K, 3 * K + (3 if x % 4 == 0 else 6) + rest[0]] + rest[1:]


def stats(path):
    rows, bad = [], []
    for line in open(path):
        if not line[:1].isdigit():
            continue
        step, body = line.split(None, 1)
        if not body.startswith("E>0 "):
            continue
        bl = blocks(body[4:])
        (rows.append((int(step), bl)) if bl else bad.append(int(step)))
    print(f"round starts (E>0 at the left end): {len(rows) + len(bad)}; not single holes at steps {bad}")
    print("number of blocks:", dict(sorted(collections.Counter(len(b) for _, b in rows).items())))
    print("first block mod 4:", dict(sorted(collections.Counter(b[0] % 4 for _, b in rows).items())))
    ok = wrong = 0
    gain = collections.Counter()
    for (_, b), (_, b2) in zip(rows, rows[1:]):
        gain[(b[0] % 4, sum(b2) - sum(b))] += 1
        if b[0] % 2 == 0:
            if predict(b) == b2:
                ok += 1
            else:
                wrong += 1
                print("MISMATCH", b, b2, predict(b))
    print(f"even rounds following the formula: {ok}, not: {wrong}")
    print("ones gained per round, by first block mod 4:",
          {r: sorted((g, n) for (q, g), n in gain.items() if q == r) for r in range(4)})


def trace(bl):
    t = table(M)
    cells = []
    for i, b in enumerate(bl):
        cells += ([0] if i else []) + [1] * b
    tape = {i + 1: c for i, c in enumerate(cells)}
    pos, s, lo, hi, prev = -1, 0, -1, len(cells), 1
    show = lambda: "".join(str(tape.get(i, 0)) for i in range(-5, hi + 5))
    print(f"{0:7d} {show()}")
    for n in range(1, 10 ** 8):
        w, d, s2 = t[(s, tape.get(pos, 0))]
        tape[pos] = w
        pos += d
        s = s2
        if d != prev and d == 1:
            print(f"{n:7d} {show()}")
        prev, hi = d, max(hi, pos)
        if pos < lo:
            print(f"{n:7d} {show()}  {'ABCDEF'[s]} at the left end")
            return


if __name__ == "__main__":
    if sys.argv[1] == "trace":
        trace([int(x) for x in sys.argv[2:]])
    else:
        stats(sys.argv[1])
