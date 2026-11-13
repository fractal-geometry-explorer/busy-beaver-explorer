"""Event rules found and proved automatically (shared by the batch-5 folders of G11).

`event(M, name, start, S)`: run the symbolic machine of `bbtools.symtm` from `start` (a tape string such as
`L 1000 (1010)^i D> 0001 0000 R`) until the head is back on the start cell in state S (the left part has the same
length in cells as at the start, as a linear expression in the variables) and return the Lean theorem of that
run (proved along the trace by `bbtools.symtm.prove`, with re-bracketing) and the end configuration.

`regex(side)`: the ERE of a tape string's side (for the coverage tool `c/evcov.c`): `(w)^n` -> `(w)*`, contexts and
`0^inf` dropped / `$`.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "py"))
from bbtools import symtm  # noqa: E402
from bbtools.symtm import Config, Rep, Ctx, Blank, Lin, run, prove, Machine  # noqa: E402


def left_len(cfg):
    n = Lin(0)
    for t in cfg.left:
        if isinstance(t, Rep):
            n = n + len(t.word) * t.n
        elif isinstance(t, int):
            n = n + 1
    return n


def event(m, name, start, state, doc=None, max_moves=200000):
    M = Machine.parse(m)
    c0 = Config.parse(start)
    S = symtm.STATES.index(state)
    L0 = left_len(c0)
    fin = run(M, c0.copy(), lambda c: not c.steps.is_zero() and c.state == S and left_len(c) == L0,
              max_moves=max_moves, rotate=True)
    end = repr(fin)
    th, _ = prove(m, name, start, end, doc=doc, rotate=True, count_first=True, max_seg=40, max_moves=max_moves)
    return th, end, fin.steps


def regex(side, left):
    out = []
    for p in side.split():
        if p == "0^inf":
            out.append("0*$" if not left else "")
            if left:
                out.insert(0, "^0*")
        elif p.startswith("("):
            w, e = p[1:].split(")^")
            out.append(f"({w})*")
        elif p.isdigit():
            out.append(p)
    return "".join(out) or "-"


def cov_line(name, start):
    i = start.split().index(next(p for p in start.split() if p.endswith(">") and len(p) == 2))
    parts = start.split()
    return f"{name} {regex(' '.join(parts[:i]), True)} {regex(' '.join(parts[i + 1:]), False)}"
