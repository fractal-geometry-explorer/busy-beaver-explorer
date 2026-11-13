"""The run of 1RB1LB_1LC1LA_1RD0LB_1RA1RE_1RF0RD_---1RD as a map on epochs (see ../README.md).

An epoch starts at   0^inf 1 B> 1 01 0101 1^5 (01)^Y T      (a = 01; T = digits (d, e) = 1^(5d) (01)^e ..., end 1^4 01)
Its rounds (Lean: round_a, round_b, epoch) turn the Y a's into 5Y or 5Y+5 ones; then a reset sweep rewrites the
front of T and starts the next epoch with Y' = 5*floor(Y/2) + c, c in {0, 5, 10}.  The reset is run here with the
exact accelerated simulator tsim.py (it does not depend on Y, only on T); the rounds are skipped by the formula.

usage: python3 epochs.py N            N epochs from blank tape: epoch, Y mod 2, digits of Y, len(T), carry depth
       python3 epochs.py --check K    compare the first K epochs with a plain accelerated run from blank tape
"""
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tsim import TRun, head_cells  # noqa: E402

M = "1RB1LB_1LC1LA_1RD0LB_1RA1RE_1RF0RD_---1RD"
PREF = [1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1]       # 1 a^3 1^5: the left end of an epoch start (head on the 0 left of it)
END = "111101"                                    # 1^4 a, the right end of the tape


def parse_tail(s):
    digs, i = [], 0
    while True:
        m = re.match(r"((?:11111)+)((?:01)*)", s[i:])
        if not m:
            break
        digs.append((len(m.group(1)) // 5, len(m.group(2)) // 2))
        i += m.end()
        rest = s[i:]
        if not rest or (rest.startswith("1") and not rest.startswith("11111")):
            break
    return digs, s[i:]


def finish(r):
    """read (Y, T, end) off an epoch start (tape all on the right stack)"""
    tot = sum(len(w) * c for w, c in r.R)
    big = max(range(len(r.R)), key=lambda j: r.R[j][1] if r.R[j][0] in ((0, 1), (1, 0)) else -1)
    cells = []
    for j, (w, c) in enumerate(r.R):
        if j == big and c > 40:
            cells.append("".join(map(str, w)) * 3)
            break
        cells.append("".join(map(str, w)) * c)
    s = "".join(reversed(cells))
    if len(s) == tot:
        s = s[12:]
        s = s[re.match(r"(?:01)*", s).end():]
        i = 0
    else:
        i = s.index("011111") + 2
    T = s[i:]
    Y = (tot - 12 - len(T)) // 2
    assert 12 + 2 * Y + len(T) == tot
    digs, end = parse_tail(T)
    return Y, digs, end


def at_epoch_start(r):
    return r.d == -1 and not r.L and r.q == 0 and head_cells(r.R, 12) == PREF


def reset(Tp, end=END, j=10 ** 6):
    """run the reset from 0^inf 1 B> 1 01 1^(10j+5) 01 T' ; return (c, T'') with Y' = 5j + c, or None on a halt"""
    r = TRun(M)
    r.L = [[(1,), 1]]
    rr = [[(1,), 1], [(0, 1), 1], [(1,), 10 * j + 5], [(0, 1), 1]]
    for d, e in Tp:
        rr.append([(1,), 5 * d])
        if e:
            rr.append([(0, 1), e])
    for ch in end:
        rr.append([(int(ch),), 1])
    r.R = list(reversed(rr))
    r.q, r.d = 1, 1
    while True:
        if not r.step():
            return None
        if at_epoch_start(r):
            Y, digs, en = finish(r)
            return Y - 5 * j, digs, en


def epoch(Y, T, end=END):
    """one epoch: (Y, T) -> (Y', T')"""
    if Y % 2 == 0:
        Tp = [(1 + T[0][0], T[0][1])] + T[1:]
    else:
        Tp = [(1, 1)] + T
    res = reset(Tp, end)
    if res is None:
        return None
    c, T2, en = res
    return 5 * (Y // 2) + c, T2, en, Tp


def first():
    """the first epoch start from blank tape: Y = 5, T = (1, 8), end 1^4 a"""
    return 5, [(1, 8)], END


def check(K):
    r = TRun(M)
    got = []
    while len(got) < K:
        r.step()
        if at_epoch_start(r):
            x = finish(r)
            if x[0] >= 5:                 # (an earlier, smaller shape at step 65 is not an epoch start)
                got.append(x)
    Y, T, end = first()
    assert got[0] == (Y, T, end), got[0]
    for k in range(1, K):
        Y, T, end, _ = epoch(Y, T, end)
        assert got[k] == (Y, T, end), (k, got[k], (Y, T, end))
        print("epoch", k, "agrees: Y =", Y, "T =", T, "after", r.steps if k == K - 1 else "", flush=True)


def main(argv):
    if argv and argv[0] == "--check":
        check(int(argv[1]))
        return
    N = int(argv[0]) if argv else 100
    Y, T, end = first()
    for k in range(N):
        res = epoch(Y, T, end)
        if res is None:
            print("HALT in epoch", k)
            return
        Y2, T2, end2, Tp = res
        a, b, j = Tp[::-1], T2[::-1], 0
        while j < min(len(a), len(b)) and a[j] == b[j]:
            j += 1
        print(k, Y % 2, len(str(Y)), len(T2), len(T2) - j, " ".join(f"{d}:{e}" for d, e in T2[:8]), flush=True)
        Y, T, end = Y2, T2, end2


if __name__ == "__main__":
    main(sys.argv[1:])
