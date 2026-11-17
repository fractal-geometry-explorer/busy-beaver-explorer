"""Every trip of the accelerated run (`accel.py`) as an instance of a theorem, far past the plain simulators.

`top.py check` puts each trip the counter theorems do not cover through the families (lean/TopFam.lean), the wall
trips (lean/Rework.lean) and the shapes (lean/Top.lean, lean/TopWall*.lean), on the plain macro run to 10^12 steps.
This program does the same along `accel.run`: the bulk steps are counter trips by construction (accel.py), and every
concrete trip, including those with cycle jumps inside, is checked here:

* `counter`: `counter.predict` covers it (no cycle jump in it);
* `family`, `wall`, `proved`: the trip is an instance of a family, a wall trip or a listed shape, and the tape the
  theorem gives is the tape accel.py reached;
* `pending`: the shape closes and gives the right tape, and is listed in lean/top_shapes_pending.txt: shapes whose
  Lean proofs are not written yet (too large for the generator as it is);
* `unlisted`: the shape closes and gives the right tape, but is in neither list (a theorem to add);
* `long` (no piece closes), `WRONG` (a theorem gives another tape): would be gaps.

The tapes here are far too long to write out cell by cell, so everything is compared as token lists
(`counter.blocks`): blocks of pairs `10` and single cells.  The trips are classified in JOBS worker processes.

usage: python3 coverage.py STEPS [JOBS]          e.g. 1e18 4; prints the tally and each unlisted shape
"""
import collections
import multiprocessing
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..", "..", "tools", "py"))
import accel  # noqa: E402
import counter  # noqa: E402
import family  # noqa: E402
import rework  # noqa: E402
import top  # noqa: E402
from bbtools import seqtm  # noqa: E402
from bbtools.symtm import Blank, Ctx, Rep  # noqa: E402

MAX_LITERAL = 10_000     # a repeat of a word other than `10`/`01` is written out cell by cell up to this many cells


# ---------------------------------------------------------------- token lists
def items_of(toks):
    """counter.py tokens (ints: pairs `10`, '0'/'1': cells) as items for counter.blocks."""
    return [("P", t) if isinstance(t, int) else int(t) for t in toks]


def norm(toks):
    return counter.blocks(items_of(toks))


def _rep_items(word, n):
    w = "".join(map(str, word))
    if n == 0 or not w:
        return []
    if w == "10" * (len(w) // 2):
        return [("P", n * len(w) // 2)]
    if w == "01" * (len(w) // 2):
        m = n * len(w) // 2
        return [0] + ([("P", m - 1)] if m > 1 else []) + [1]
    if n * len(w) > MAX_LITERAL:
        raise ValueError(f"a long repeat of {w}")
    return [int(c) for c in w * n]


def sym_items(toks, env, elems, ctx):
    """family.cells, as items: symtm/seqtm left tokens with the variables from env, the sequences' elements from
    elems (first element nearest the head) and the context ctx (items)."""
    out = []
    for t in toks:
        if isinstance(t, Blank):
            continue
        if isinstance(t, Ctx):
            out += ctx
        elif isinstance(t, int):
            out.append(t)
        elif isinstance(t, Rep):
            out += _rep_items(t.word, t.n.subs(env))
        elif isinstance(t, seqtm.Seq):
            blocks = [sym_items(list(t.elem), {**env, **ev}, None, None) for ev in elems]
            for b in (blocks if t.rev else reversed(blocks)):
                out += b
        else:
            raise ValueError(t)
    return out


def drop_cells(its, n):
    """its without its last n cells."""
    its = list(its)
    while n:
        x = its.pop()
        if isinstance(x, tuple):
            if x[1] * 2 > n:
                rest = x[1] - (n + 1) // 2
                if rest:
                    its.append(("P", rest))
                if n % 2:
                    its.append(1)       # half a pair `10` left: its 1
                return its
            n -= 2 * x[1]
        else:
            n -= 1
    return its


def family_predict(fams, before):
    """family.predict, as a token list (normalised), or None."""
    bs, ss = top.norm(before)
    k, j = top.walk(bs, ss)
    items = top.piece_tokens(bs, ss, k, j, 0)
    for f in fams:
        if f.turn != (k > 0):
            continue
        m = family.match(f.pat, items)
        if m is None:
            continue
        env, elems, L = m
        ctx = items_of(L) if L is not None else None
        start = sym_items(f.cfg.left, env, elems, ctx)
        if counter.blocks(start) != counter.blocks(items_of(items)):
            continue
        end = sym_items(f.fin.left, env, elems, ctx)
        if f.turn:
            end = drop_cells(end, 3)
        out = end
        for lvl in range(k):
            g, w = bs[j + 1 + 2 * lvl], bs[j + 2 + 2 * lvl]
            last = lvl == k - 1
            out += [1, ("P", g + 1), 1, ("P", w + 1 if last else w - 1)]
        return counter.blocks(out + [0, ("P", 1)])
    return None


# ---------------------------------------------------------------- one trip
_FAMS = _PROVED = _PENDING = None
PENDING = os.path.join(HERE, "..", "lean", "top_shapes_pending.txt")


def _init():
    global _FAMS, _PROVED, _PENDING
    _FAMS = [family.Family(t) for t in family.load()]
    _PROVED = set(top.load_shapes())
    with open(PENDING) as f:
        _PENDING = {ln.rstrip("\n") for ln in f if ln.strip() and not ln.startswith("#")}


def classify(job):
    """(kind, start of the shape or None) for the trip from token list a to token list b."""
    a, b = job
    a, b = norm(a), norm(b)
    fp = family_predict(_FAMS, a)
    if fp is not None:
        return ("family" if fp == b else "WRONG"), None
    try:
        wp = rework.predict(a)
    except RecursionError:      # rounds that go on past the recursion limit: not a wall trip of Rework.lean here
        wp = None
    if wp is not None:
        return ("wall" if norm(wp) == b else "WRONG"), None
    c = top.cut(a)
    if "long" in c:
        return "long", None
    if norm(top.predict(c)) != b:
        return "WRONG", c["start"]
    if c["start"] in _PROVED:
        return "proved", c["start"]
    return ("pending" if c["start"] in _PENDING else "unlisted"), c["start"]


def trips(steps, tally):
    """The concrete trips of accel.run that counter.predict does not cover, as (steps, before, after)."""
    prev, nj = None, 0
    for s, _, t, kind in accel.run(steps):
        jumps = len(accel.JUMPS)
        if kind != "bulk" and prev is not None:
            if kind == "proved" and jumps == nj:
                tally["counter"] += 1
            else:
                yield s, prev, t
        if kind == "bulk":
            tally["bulk steps"] += 1
        prev, nj = t, jumps


def main(argv):
    if not 1 <= len(argv) <= 2:
        sys.exit(__doc__)
    steps, jobs = int(float(argv[0])), int(argv[1]) if len(argv) > 1 else 1
    tally, new, last = collections.Counter(), {}, 0
    gen = trips(steps, tally)
    meta = []

    def jobs_of():
        for s, a, b in gen:
            meta.append(s)
            yield a, b

    with multiprocessing.Pool(jobs, initializer=_init) as pool:
        for i, (kind, start) in enumerate(pool.imap(classify, jobs_of(), chunksize=1)):
            tally[kind] += 1
            last = meta[i]
            if kind in ("unlisted", "WRONG", "long") and (kind, start) not in new:
                new[(kind, start)] = last
                print(f"{kind} at {float(last):.3e} steps: {start}", flush=True)
            if (i + 1) % 500 == 0:
                print(f"{float(last):.3e} steps: " + ", ".join(f"{k} {v}" for k, v in sorted(tally.items())),
                      flush=True)
    print(f"trips to {steps:.3g} steps: " + ", ".join(f"{k} {v}" for k, v in sorted(tally.items())))
    return 0 if not any(k in tally for k in ("unlisted", "WRONG", "long")) else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
