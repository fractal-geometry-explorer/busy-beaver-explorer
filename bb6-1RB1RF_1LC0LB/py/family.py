"""Families of top shapes: one shape with a list of blocks of any length, proved once by induction on the list.

Many shapes of `lean/top_shapes.txt` are one rule with a different number of copies of some blocks between the
left end and the turn: the "ladders" `0^inf (1010)^x0 1 10 10 (1010)^x1 1 10 10 (1010)^x2 ... 1 10 10 10 ...`, for
example, with one rung `1 10 10 (1010)^t` more each time.  A *family* writes the copies as a sequence
`[ 1 10 10 (1010)^a ]^ts` (`bbtools.seqtm`): every list `ts`, of any length and any values.  Its symbolic run crosses
the whole list at once each time the head meets it (one block run on its own, then induction on the list,
`lean/Seq.lean`), so one run, and one Lean theorem (`fam_i` in `lean/TopFam.lean`), covers the shape with any
number of rungs.

A trip is an instance of a family when its piece (`top.cut`), read as blocks and seps, is the family's start with
some values and some list: `match` finds them, and `predict` writes the tape after the trip from the family's end;
`top.check` compares that with the run, cell by cell.

usage: python3 family.py find          the families among the shapes of top_shapes.txt (written to top_families.txt)
       python3 family.py show          the families of lean/top_families.txt, each with its run's end
"""
import os
import random
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "tools", "py"))
sys.path.insert(0, HERE)
import counter  # noqa: E402
import top  # noqa: E402
from bbtools import seqtm  # noqa: E402
from bbtools.symtm import Blank, Ctx, Lin, Rep, lin  # noqa: E402

FAMILIES = os.path.join(HERE, "..", "lean", "top_families.txt")
VAR = re.compile(r"\^(?!inf\b)(x\d+|[a-z]\w*)\b")


def load():
    """The families `lean/TopFam.lean` proves (one start per line)."""
    if not os.path.exists(FAMILIES):
        return []
    with open(FAMILIES) as f:
        return [ln.rstrip("\n") for ln in f if ln.strip() and not ln.startswith("#")]


# ---------------------------------------------------------------- the start as blocks
def _items(parts):
    """Shape-syntax tokens (no context, no head) as alternating blocks and seps, starting and ending with a block:
    a block is a Lin (its length in pairs), a sep '0' or '1'."""
    out, cur = [], None
    for p in parts:
        if p in ("0", "1"):
            out.append(cur if cur is not None else lin(0))
            out.append(p)
            cur = None
            continue
        if p == "10":
            n = lin(1)
        elif p.startswith("(10)^"):
            n = lin(int(p[5:]))
        elif p.startswith("(1010)^"):
            n = 2 * lin(p[7:])
        else:
            raise ValueError(f"token {p}")
        cur = n if cur is None else cur + n
    out.append(cur if cur is not None else lin(0))
    return out


class Pattern:
    """A family's start as blocks: `blank` (it starts at the left end) or not (an `L` and a sep first); the items
    before the sequence, the sequence's element (seps and blocks, starting with a sep, ending with a block), and
    the items after."""

    def __init__(self, text):
        parts = text.split()
        head = next(k for k, p in enumerate(parts) if p.endswith(">") and len(p) == 2)
        self.blank = parts[0] == "0^inf"
        body = parts[1:head]
        i, j = body.index("["), next(k for k, p in enumerate(body) if p.startswith("]^"))
        pre, elem, post = body[:i], body[i + 1:j], body[j + 1:]
        if not elem or elem[0] not in ("0", "1") or not (not post or post[0] in ("0", "1")):
            raise ValueError("the sequence's element must start at a sep and end before one")
        self.elem = _items(elem)[1:]                      # [sep, block, ..., sep, block]
        self.pre = _items(pre) if pre else [lin(0)]       # [block, sep, ..., block]
        self.post = _items(post)[1:] if post else []      # [sep, block, ...]
        if not self.blank and self.pre[0] != lin(0):
            raise ValueError("a family not at the left end starts `L` and a sep")
        self.params = sorted(set(VAR.findall(" ".join(elem))))


def _fit(p, v, env):
    """Match the pattern length p (a Lin, at most one variable) against the value v; updates env; False if not."""
    if p.is_const():
        return p.k == v
    (x, a), = p.c.items()
    r = v - p.k
    if r < 0 or r % a:
        return False
    if x in env:
        return env[x] == r // a
    env[x] = r // a
    return True


def _fit_all(pats, vals, env):
    for p, v in zip(pats, vals):
        if isinstance(p, str):
            if p != v:
                return False
        elif not (isinstance(v, int) and _fit(p, v, env)):
            return False
    return True


def match(pat, items):
    """Values for pattern `pat` on the piece `items` ([b0, s1, b1, ..., sj, bj]): (env, element values (first
    element nearest the head), L items or None) or None."""
    e = len(pat.elem)
    for n in range(0, len(items) // e + 1):
        full = pat.pre + pat.elem * n + pat.post
        if pat.blank:
            if len(full) != len(items):
                continue
            off, L = 0, None
        else:
            off = len(items) - len(full)        # items[off] is the last block of L
            if off < 0:
                break
            L = items[:off + 1]
        env, elems = {}, []
        i = off + len(pat.pre)
        if not _fit_all(pat.pre[0 if pat.blank else 1:], items[off + (0 if pat.blank else 1):i], env):
            continue
        ok = True
        for m in range(n):
            ev = {}
            if not _fit_all(pat.elem, items[i:i + e], ev):
                ok = False
                break
            elems.append(ev)
            i += e
        if ok and _fit_all(pat.post, items[i:], env):
            return env, list(reversed(elems)), L
    return None


# ---------------------------------------------------------------- concrete tapes
def cells(toks, env, elems, ctx):
    """symtm/seqtm left tokens as a cell string, the variables from env, each sequence's elements from elems
    (first element nearest the head), the context from ctx (a cell string)."""
    out = []
    for t in toks:
        if isinstance(t, Blank):
            continue
        if isinstance(t, Ctx):
            out.append(ctx)
        elif isinstance(t, int):
            out.append(str(t))
        elif isinstance(t, Rep):
            out.append("".join(map(str, t.word)) * t.n.subs(env))
        elif isinstance(t, seqtm.Seq):
            blocks = [cells(list(t.elem), {**env, **ev}, None, None) for ev in elems]
            # left of the head: `sq` has the first element nearest the head (rightmost), `sqr` the last
            out.append("".join(blocks if t.rev else reversed(blocks)))
        else:
            raise ValueError(t)
    return "".join(out)


class Family:
    """A family: its start, whether it ends at a turn, its symbolic run's end, its pattern."""

    def __init__(self, text):
        self.text = text
        self.turn = text.endswith(top.TURN_TAIL)
        self.cfg = seqtm.parse(text)
        self.fin = seqtm.run(top.M, self.cfg.copy(), top._at_end(self.turn), max_moves=top.MOVES)
        self.pat = Pattern(text)
        if self.turn and self.fin.left[-4:] != [0, 1, 1, 0]:
            raise ValueError("a turn family must end with `0 1 1 0` left of the head")

    def apply(self, items):
        """(start cells, end cells) of the piece `items` if it is an instance, else None.  The end is the tape left
        of the head with the turn's `1 1 0` dropped (turn) or the whole left tape (last); the start the same without
        the walk's two pairs given back."""
        m = match(self.pat, items)
        if m is None:
            return None
        env, elems, L = m
        ctx = piece_cells(L) if L is not None else None
        start = cells(self.cfg.left, env, elems, ctx)
        end = cells(self.fin.left, env, elems, ctx)
        if self.turn:
            end = end[:-3]
        return start, end


def piece_cells(items):
    return "".join("10" * t if isinstance(t, int) else t for t in items)


def predict(fams, before):
    """The tape after the trip (cells, as counter.tape_str writes it) through the first family it is an instance
    of: (family index, cells), or None."""
    bs, ss = top.norm(before)
    k, j = top.walk(bs, ss)
    items = top.piece_tokens(bs, ss, k, j, 0)
    for i, f in enumerate(fams):
        if f.turn != (k > 0):
            continue
        r = f.apply(items)
        if r is None:
            continue
        start, end = r
        if start.lstrip("0") != piece_cells(items).lstrip("0"):
            continue            # not the same tape (cannot happen when the pattern is read right)
        out = [end]
        for lvl in range(k):
            g, w = bs[j + 1 + 2 * lvl], bs[j + 2 + 2 * lvl]
            last = lvl == k - 1
            out += ["1", g + 1, "1", w + 1 if last else w - 1]
        if not k:
            return i, (end + "01").lstrip("0")
        return i, counter.tape_str(out + ["0", 1])
    return None


# ---------------------------------------------------------------- finding families
def candidates(shape):
    """Families made from one shape: a stretch of its start from a sep to just before a sep (or the head), with
    one or two variables, and the copies of it right after it, as a sequence."""
    parts = shape.split()
    head = next(k for k, p in enumerate(parts) if p.endswith(">") and len(p) == 2)
    seps = [k for k in range(1, head) if parts[k] in ("0", "1")] + [head]
    out = []
    for a in range(len(seps) - 1):
        for b in range(a + 1, min(len(seps), a + 9)):
            i, j = seps[a], seps[b]
            seg = parts[i:j]
            vs = [p for p in seg if VAR.search(p)]
            if not 1 <= len(vs) <= 2:
                continue
            names, g = {}, []
            for p in seg:
                m = VAR.search(p)
                if m:
                    names.setdefault(m.group(1), "ab"[len(names)])
                    p = VAR.sub("^" + names[m.group(1)], p)
                g.append(p)
            k = j
            while k + len(seg) <= head and [VAR.sub("^v", p) for p in parts[k:k + len(seg)]] == \
                    [VAR.sub("^v", p) for p in g] and (k + len(seg) == head or parts[k + len(seg)] in ("0", "1")):
                k += len(seg)
            out.append(" ".join(parts[:i] + ["["] + g + ["]^ts"] + parts[k:]))
    return out


def instances(sh, rng, n=3):
    """Concrete pieces of a shape (items) with random values, and the end its own run predicts (cells)."""
    out = []
    for _ in range(n):
        vals = {v: rng.randint(0, 4) for v in sh.vars}
        lhs = [t for t in top.subst(sh.lhs, vals, [])]
        rhs = top.subst(sh.rhs, vals, [])
        out.append((lhs, rhs))
    return out


def covers(f, st, rng):
    """Whether family f covers shape st (on random instances, the same end)."""
    sh = top.shape(st)
    if sh.turn != f.turn:
        return False
    for _ in range(3):
        vals = {v: rng.randint(0, 4) for v in sh.vars}
        if sh.lhs and isinstance(sh.lhs[0], Ctx):
            ctxi = [3, "1", 2]
        else:
            ctxi = []
        lhs, rhs = top.subst(sh.lhs, vals, ctxi), top.subst(sh.rhs, vals, ctxi)
        bs, ss = top.norm(lhs + ["0", 1]) if lhs else ([0], [])
        items = [bs[0]]
        for s, b in zip(ss, bs[1:]):
            items += [s, b]
        r = f.apply(items)
        if r is None:
            return False
        if r[0].lstrip("0") != piece_cells(items).lstrip("0"):
            return False
        if r[1].lstrip("0") != piece_cells(rhs).lstrip("0"):
            return False
    return True


def find(shapes=None):
    """Families that close and cover two or more shapes, chosen greedily; [(family, [shape indices])]."""
    shapes = shapes if shapes is not None else top.load_shapes()
    plain = [i for i, s in enumerate(shapes) if not top.shape(s).wall]
    found = {}
    for i in plain:
        for fam in candidates(shapes[i]):
            if fam in found:
                continue
            try:
                f = Family(fam)
            except Exception:   # noqa: BLE001  (a candidate that does not close)
                found[fam] = []
                continue
            rng = random.Random(1)
            found[fam] = [k for k in plain if covers(f, shapes[k], rng)]
    chosen, done = [], set()
    while True:
        best = max(found.items(), key=lambda kv: (len(set(kv[1]) - done), -len(kv[0])), default=None)
        if not best or len(set(best[1]) - done) < 2:
            break
        chosen.append((best[0], sorted(best[1])))
        done |= set(best[1])
    return chosen


HEADER = """# families of top shapes: a shape with a list `[ ... ]^ts` of blocks of any length and any values (written by
# `python3 py/family.py find` from the shapes then in top_shapes.txt, which drop the shapes a family covers);
# lean/top_gen.py proves each one by induction on the list (TopFam.lean, `fam_i`)
"""


def write(fs):
    """Add the families fs to top_families.txt (keeping those there) and drop the shapes they cover from
    top_shapes.txt."""
    old = load()
    with open(FAMILIES, "w") as f:
        f.write(HEADER)
        for fam in old + [fam for fam, _ in fs if fam not in old]:
            f.write(fam + "\n")
    drop = {top.load_shapes()[i] for _, cov in fs for i in cov}
    with open(top.SHAPES) as f:
        lines = f.readlines()
    with open(top.SHAPES, "w") as f:
        f.writelines(ln for ln in lines if ln.rstrip("\n") not in drop)


def main(argv):
    if argv == ["find"]:
        fs = find()
        for fam, cov in fs:
            print(f"{fam}\n    covers {len(cov)}: {cov}")
        write(fs)
    elif argv == ["show"]:
        for fam in load():
            f = Family(fam)
            print(fam, "\n   ->", f.fin)
    else:
        sys.exit(__doc__)


if __name__ == "__main__":
    main(sys.argv[1:])
