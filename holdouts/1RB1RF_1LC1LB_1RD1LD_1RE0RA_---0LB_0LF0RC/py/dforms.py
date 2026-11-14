"""The visits of the left end in the accelerated macro run (accel.py), written as run lists for runlist.py.

At a sample of the accelerator with the head at the left end the tape is converted to the lengths of its runs of 1s
(big block counts stay symbolic: `3^103352228710`).  The samples fall on block boundaries, 3 or 4 steps after the
visit in state D when the state is B or C; those are stepped back (the line then carries the state, and runlist.py
subtracts the steps).

usage: python3 dforms.py LIMIT_EXP OUT        lines "steps STATE 0 runs..." up to 10^LIMIT_EXP steps
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "../../../tools/py"))
from bbtools.cycles import Accelerator  # noqa: E402
from ctxmacro import M, CtxMacroRun  # noqa: E402
import accel  # noqa: E402


def minimal_period(L):
    n = len(L)
    for d in range(1, n + 1):
        if n % d == 0 and L == L[:d] * (n // d):
            return L[:d], n // d


def runlist(r, unstep):
    """[(pattern, count)] of the run lengths of the tape right of the head; `unstep` rewrites the first block."""
    segs = [("".join(map(str, x)), c) for x, c in reversed(r.right[1:])]
    toks, cur = [], 0

    def emit(pat, c):
        pat = tuple(pat)
        if toks and toks[-1][0] == pat:
            toks[-1] = (pat, toks[-1][1] + c)
        else:
            toks.append((pat, c))

    def feed(w):
        nonlocal cur
        out = []
        for ch in w:
            if ch == "1":
                cur += 1
            else:
                out.append(cur)
                cur = 0
        return out

    for i, (w, c) in enumerate(segs):
        if i == 0 and unstep:
            if c > 1:
                raise ValueError("a repeated block at the head")
            w = unstep(w)
        if "0" not in w:
            cur += len(w) * c
            continue
        for v in feed(w):
            emit((v,), 1)
        if c >= 2:
            per = feed(w)                   # the runs one more copy adds: the same for every further copy
            if c == 2:
                for v in per:
                    emit((v,), 1)
            else:
                p, k = minimal_period(per)
                emit(p, k * (c - 1))
    emit((cur,), 1)
    out = []
    for p, c in toks:
        if len(p) > 1 and c <= 2:
            out.extend(((v,), 1) for _ in range(c) for v in p)
        else:
            out.append((p, c))
    res = []
    for p, c in out:
        if res and res[-1][0] == p:
            res[-1] = (p, res[-1][1] + c)
        else:
            res.append((p, c))
    return res


def fmt(toks):
    return " ".join((str(p[0]) if len(p) == 1 else "(" + " ".join(map(str, p)) + ")") + ("" if c == 1 else f"^{c}")
                    for p, c in toks)


def dform(r):
    """(state, run list) at a sample with the head at the left end, stepped back to the visit in state D; or None."""
    if r.dir != -1 or len(r.left) != 1:
        return None
    st = "ABCDEF"[r.state]
    w = "".join(map(str, r.right[-1][0]))
    if st == "D":
        un = None
    elif st == "B" and w.startswith("10"):          # D> 0 1 x..  ->(3 steps)  B> 0 1 0 x..
        un = lambda w: "1" + w[2:]
    elif st == "C" and w.startswith("110"):         # ... ->(1 more step)  C> 0 1 1 0 x..
        un = lambda w: "1" + w[3:]
    else:
        return None
    try:
        return st, "0 " + fmt(runlist(r, un))
    except ValueError:
        return None


if __name__ == "__main__":
    if len(sys.argv) != 3:
        sys.exit(__doc__)
    out = open(sys.argv[2], "w")
    a = Accelerator(CtxMacroRun(M, 12))
    for r in accel.sampled(a, 10 ** int(sys.argv[1])):
        d = dform(r)
        if d:
            out.write(f"{r.steps} {d[0]} {d[1]}\n")
            out.flush()
    out.write("END halted\n" if a.run_.halted else f"END running {a.run_.steps}\n")
