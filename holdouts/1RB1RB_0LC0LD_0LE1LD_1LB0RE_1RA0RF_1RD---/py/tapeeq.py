"""Lean proofs that two symbolic tapes are equal (for every value of the variables), by re-bracketing repeats.

A side of the tape is written *outward* (from the head away): literal cells and repeats `Rep(word, n)` (the word in
outward order), ending in a context or blank tape.  `normal` pushes literal cells inward (toward the head) past a repeat
while the cell equals the repeat's first cell (`(x y)^n x = x (y x)^n`, `TM.rep_rotate`), absorbs a literal copy of
the word in front of a repeat (`w (w)^n = (w)^(n+1)`, `TM.rep_succ`) and merges neighbouring repeats of one word
(`TM.rep_add`), recording each move.  `eq_proof(a, b)` normalizes both sides; if the normal forms agree it returns a
Lean term proving `term(a) = term(b)`, a chain of `congrArg`ed instances of those lemmas, each checked by `show`.
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "../../../tools/py"))
from bbtools import symtm
from bbtools.symtm import Rep, Ctx, Blank, Lin, lin

B = {0: "false", 1: "true"}


def word(w):
    return "[" + ", ".join(B[x] for x in w) + "]"


def term(toks, base=None):
    """Lean tape of an outward token list (the last token a Ctx or Blank, unless `base` is given)."""
    if base is None:
        last = toks[-1]
        base = last.name if isinstance(last, Ctx) else "blank"
        toks = toks[:-1]
    acc = base
    for t in reversed(toks):
        if isinstance(t, int):
            acc = f"cons {B[t]} ({acc})"
        else:
            acc = f"rep ({t.n.lean()}) {word(t.word)} ({acc})"
    return acc


def outward_right(cfg):
    return list(cfg.right)


def outward_left(cfg):
    out = []
    for t in reversed(cfg.left):
        out.append(Rep(tuple(reversed(t.word)), t.n) if isinstance(t, Rep) else t)
    return out


def normal(toks):
    """(normal form, moves): each move (i, kind, data, tokens before) rewrites the list at position i.
    Literal cells after a repeat move inward (toward the head) past it while they equal its first cell
    (`(x y)^n x = x (y x)^n`, `TM.rep_rotate` read backwards), a literal copy of the word in front of a repeat is
    absorbed (`w (w)^n = (w)^(n+1)`, `TM.rep_succ`), neighbouring repeats of one word are merged (`TM.rep_add`)."""
    toks = [t for t in toks if not (isinstance(t, Rep) and t.n.is_zero())]
    moves = []
    changed = True
    while changed:
        changed = False
        for i, t in enumerate(toks):
            if not isinstance(t, Rep):
                continue
            if i + 1 < len(toks) and isinstance(toks[i + 1], int) and toks[i + 1] == t.word[0]:
                x = toks[i + 1]
                w2 = t.word[1:] + (x,)
                moves.append((i, "rotin", (t.n, (x,), w2, t.word), toks[:]))
                toks[i:i + 2] = [x, Rep(w2, t.n)]
                changed = True
                break
            L = len(t.word)
            prv = toks[max(0, i - L):i]
            if i >= L and all(isinstance(y, int) for y in prv) and tuple(prv) == t.word:
                moves.append((i - L, "absorb", (t.n, t.word), toks[:]))
                toks[i - L:i + 1] = [Rep(t.word, t.n + 1)]
                changed = True
                break
            if i + 1 < len(toks) and isinstance(toks[i + 1], Rep) and toks[i + 1].word == t.word:
                moves.append((i, "merge", (t.n, toks[i + 1].n, t.word), toks[:]))
                toks[i:i + 2] = [Rep(t.word, t.n + toks[i + 1].n)]
                changed = True
                break
    return toks, moves


def _step_proof(i, kind, data, before):
    """A Lean term: term(before) = term(after) for one move at position i."""
    pre = before[:i]
    ctx = "fun t => " + term(pre, base="t") if pre else None
    if kind == "rotin":           # (x y)^n x  =  x (y x)^n : rep_rotate with x, y = (y x), y' = (x y), reversed
        n, x, y, y2 = data
        rest = term(before[i + 2:])
        core = f"(rep_rotate ({n.lean()}) {word(x)} {word(y)} {word(y2)} rfl ({rest})).symm"
    elif kind == "absorb":
        n, w = data
        rest = term(before[i + 1 + len(w):])
        core = f"(rep_succ ({n.lean()}) {word(w)} ({rest})).symm"
    else:
        a, b, w = data
        rest = term(before[i + 2:])
        core = f"(rep_add ({a.lean()}) ({b.lean()}) {word(w)} ({rest})).symm"
    return f"congrArg ({ctx}) ({core})" if ctx else core


def after_move(kind, i, data, before):
    t = before[:]
    if kind == "rotin":
        n, x, y, y2 = data
        t[i:i + 2] = [x[0], Rep(y, n)]
    elif kind == "absorb":
        n, w = data
        t[i:i + 1 + len(w)] = [Rep(w, n + 1)]
    else:
        a, b, w = data
        t[i:i + 2] = [Rep(w, a + b)]
    return t


def chain(toks):
    """(normal form, list of (lhs tokens, rhs tokens, proof))."""
    nf, moves = normal(toks)
    out = []
    for (i, kind, data, before) in moves:
        out.append((before, after_move(kind, i, data, before), _step_proof(i, kind, data, before)))
    return nf, out


def same(a, b):
    def key(ts):
        return [("r", t.word, tuple(sorted(t.n.c.items())), t.n.k) if isinstance(t, Rep) else t for t in ts]
    return key(a) == key(b)


def eq_proof(a, b):
    """A Lean proof term of `term(a) = term(b)`, or raise ValueError."""
    na, ca = chain(a)
    nb, cb = chain(b)
    if not same(na, nb):
        raise ValueError(f"normal forms differ:\n {na}\n {nb}")
    parts = [f"(show {term(l)} = {term(r)} from {p})" for (l, r, p) in ca]
    parts += [f"(show {term(l)} = {term(r)} from {p}).symm" for (l, r, p) in reversed(cb)]
    if not parts:
        return "rfl"
    pf = parts[-1]
    for p in reversed(parts[:-1]):
        pf = f"{p}.trans ({pf})"
    return pf
