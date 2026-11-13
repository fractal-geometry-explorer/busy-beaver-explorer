"""The law of a cursor crossing runs, checked on the exact engine (py/engine.py).

A cursor enters a run of length b in one of two modes and leaves it of length
    mode A:  b odd -> 3b      (next run entered in mode B),   b even -> 3b + 4  (next: mode A)
    mode B:  b even -> 3b + 4 (next: mode B),                 b odd  -> 3b + 8  (next: mode A)
taking one round per pair it moves, each round costing the first run one pair.
Test: random run lists  m | b1 | b2 | ... | bk | 60  with a fresh cursor at the start of b1 (mode A: `| 1 "1" b1-1`).
"""
import random, sys
from engine import Eng


def predict(bs):
    mode, out = 'A', []
    for b in bs:
        if mode == 'A':
            out.append(3 * b if b % 2 else 3 * b + 4); mode = 'B' if b % 2 else 'A'
        else:
            out.append(3 * b + 8 if b % 2 else 3 * b + 4); mode = 'A' if b % 2 else 'B'
    return out


def trial(rng, k):
    bs = [rng.randrange(3, 40) for _ in range(k)]
    m = 4 * sum(bs) + 50
    cells = '01' * m + '00110' + '01' + '1' + '01' * (bs[0] - 1)
    for b in bs[1:] + [60]:
        cells += '00110' + '01' * b
    e = Eng([int(c) for c in cells])
    want = [str(x) for x in predict(bs)]
    for _ in range(m - 5):
        assert e.run_event()
        t = e.tokens()
        # the cursor has entered the last run when the k runs before it are final
        runs = [x for x in t if x.isdigit()]
        if runs[1:k + 1] == want and t[2 * k + 1] == '|' and len(t) > 2 * k + 3:
            return True
    return False


if __name__ == '__main__':
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    rng = random.Random(1)
    bad = sum(not trial(rng, rng.randrange(1, 6)) for _ in range(n))
    print(f'{n} random run lists: {n - bad} follow the law, {bad} do not')
    sys.exit(1 if bad else 0)
