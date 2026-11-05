"""The wall-building loop, for the symbolic runs of `top.py`: whole runs of rounds at once.

When the counter's walk meets a level `0 (10)^X` with a single pair to its left, the head shuttles between the left
end of the tape and that level, one pair out of the level and two into the first block per round
(`lean/Wall.lean`).  At the start of each round the head is in C at the left end, blank tape to its left, and

    C> 0 (10)^(2a+1)  0 (10)^(2t1+2) ... 0 (10)^(2tm+2)  0 0 (10)^X  R                                   (Rd a ts X R)

`wall_loop` in Wall.lean proves that this becomes `Rd (a+X) ts 0 R` (X rounds) for all values.  `run` here is
`symtm.run` with one more move: when the configuration is in that form with X symbolic (a linear expression with
variables), it jumps over the whole loop.  The jumps are recorded, so that `lean/top_gen.py` can prove the run as
symbolic pieces between the jumps, chained with `wall_loop`.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "tools", "py"))
from bbtools.symtm import Blank, Config, Ctx, Lin, Rep, lin, run as sym_run  # noqa: E402

C = 2
MIN_X = 4           # a constant level shorter than this is run round by round


def rstream(right):
    """symtm right tokens as cells and ('B', n, parts) for (10)^n, the last item the context (Ctx or Blank); parts
    are the repeats and literal pairs it is made of, a repeat of `01`s re-bracketed as one of `10`s of the same
    period (so that the sweeps still cross it whole)."""
    out = []
    for t in right:
        if isinstance(t, (Ctx, Blank)):
            out.append(t)
        elif isinstance(t, int):
            out.append(t)
        elif isinstance(t, Rep):
            w = "".join(map(str, t.word))
            h = len(w) // 2
            if len(w) % 2 == 0 and w == "10" * h:
                out.append(("B", h * t.n, t))
            elif len(w) % 2 == 0 and w == "01" * h:
                out.append(("A", h * t.n, Rep((1, 0) * h, t.n)))
            else:
                return None
        else:
            return None
    while any(isinstance(t, tuple) and t[0] == "A" for t in out):    # (01)^n 0 = 0 (10)^n, 1 (01)^n = (10)^n 1
        i = next(i for i, t in enumerate(out) if isinstance(t, tuple) and t[0] == "A")
        if i + 1 < len(out) and out[i + 1] == 0:
            out[i:i + 2] = [0, ("B",) + out[i][1:]]
        elif i >= 1 and out[i - 1] == 1:
            out[i - 1:i + 1] = [("B",) + out[i][1:], 1]
        else:
            return None
    # literal pairs into blocks, adjacent blocks merged; each block keeps its parts (repeats and literal pairs), so
    # that the tape after it can be written back with its literal cells as they were
    res, i = [], 0
    while i < len(out):
        t = out[i]
        if isinstance(t, tuple) or (t == 1 and i + 1 < len(out) and out[i + 1] == 0):
            n, parts = lin(0), []
            while i < len(out) and (isinstance(out[i], tuple) or (out[i] == 1 and i + 1 < len(out)
                                                                    and out[i + 1] == 0)):
                if isinstance(out[i], tuple):
                    n, i = n + out[i][1], i + 1
                    parts.append(out[i - 1][2])
                else:
                    n, i = n + 1, i + 2
                    parts += [1, 0]
            res.append(("B", n, parts))
        else:
            res.append(t)
            i += 1
    return res


def _odd(n):
    return n.k % 2 == 1 and all(a % 2 == 0 for a in n.c.values()) and all(a >= 0 for a in n.c.values())


def _even2(n):
    return n.k % 2 == 0 and n.k >= 2 and all(a % 2 == 0 and a >= 0 for a in n.c.values())


def _half(n, r):
    """(n - r) / 2 as a Lin."""
    return Lin((n.k - r) // 2, {v: a // 2 for v, a in n.c.items()})


class Round:
    """A configuration `blank C> Rd a ts X rest`: a, ts (Lin), X (Lin), rest (symtm right tokens)."""

    def __init__(self, a, ts, X, rest):
        self.a, self.ts, self.X, self.rest = a, ts, X, rest

    def tokens(self, a=None, X=None):
        """The right tokens of `Rd a ts X rest`, written as Wall.lean's `Rd` unfolds."""
        a = self.a if a is None else a
        X = self.X if X is None else X
        out = [0, Rep((1, 0, 1, 0), a), 1, 0]
        for t in self.ts:
            out += [0, 1, 0, Rep((1, 0, 1, 0), t), 1, 0]
        out += [0, 0, Rep((1, 0), X)]
        return [t for t in out if not (isinstance(t, Rep) and t.n.is_zero())] + list(self.rest)

    def __repr__(self):
        return f"Rd({self.a}, {self.ts}, {self.X})"


def match(cfg):
    """The Round if cfg is at the start of a round with a symbolic level X >= 1, else None."""
    if cfg.state != C or cfg.left != [Blank()]:
        return None
    s = rstream(cfg.right)
    if not s or len(s) < 5 or s[0] != 0 or not (isinstance(s[1], tuple) and _odd(s[1][1])):
        return None
    a, i, ts = _half(s[1][1], 1), 2, []
    while i + 1 < len(s) and s[i] == 0 and isinstance(s[i + 1], tuple):
        if not _even2(s[i + 1][1]):
            return None
        ts.append(_half(s[i + 1][1], 2))
        i += 2
    if not (i + 2 < len(s) and s[i] == 0 and s[i + 1] == 0 and isinstance(s[i + 2], tuple)):
        return None
    X = s[i + 2][1]
    if (X.is_const() and X.k < MIN_X) or not X.surely_ge(1) or any(c < 0 for c in X.c.values()):
        return None
    rest = []
    for t in s[i + 3:]:
        rest += t[2] if isinstance(t, tuple) else [t]
    if rest and isinstance(rest[0], int) and rest[0] == 1 and len(rest) > 1 and rest[1] == 0:
        return None         # cannot happen after a greedy read; kept as a guard
    return Round(a, ts, X, rest)


class Jump:
    """A whole loop jumped over: the configuration before (as the run reached it), the round, and after."""

    def __init__(self, before, rnd, after):
        self.before, self.rnd, self.after = before, rnd, after


def run(m, cfg, stop, max_moves=2000, jumps=None):
    """`symtm.run` with loop jumps.  `jumps`: a list to which the parts are appended: (start, end) of each plain
    symbolic stretch and Jump objects in between."""
    cur = cfg
    while True:
        hit = []

        def st(c):
            if stop(c):
                return True
            if not c.steps.is_zero():
                r = match(c)
                if r is not None:
                    hit.append(r)
                    return True
            return False

        start = cur.copy()
        fin = sym_run(m, cur, st, max_moves=max_moves)
        if jumps is not None:
            jumps.append((start, fin.copy()))
        if not hit:
            return fin
        r = hit[0]
        after = Config([Blank()], C, r.tokens(a=r.a + r.X, X=lin(0)), fin.steps)
        if jumps is not None:
            jumps.append(Jump(fin.copy(), r, after.copy()))
        cur = after
