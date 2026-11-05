"""The top of the counter: the right-end trips that `counter.py` does not predict, as maps on block lengths.

`counter.predict` covers a trip when it borrows through standard digit-0 levels and turns at a standard digit-2 or
digit-1 level (`lean/Counter.lean`).  The other trips (`left` and `short`) are cut here into

* the standard part: the walk over the last level and the digit-0 levels `zs` (`walk_all` in Counter.lean) and the
  sweep back that resets them (`sweepN`, `sweepLast`), as for any borrow, and
* one *top piece*: what the head does between arriving, in the walk's phase, at the first level the walk does not
  cross (the tape to the left of it called T) and leaving to the right again in the sweep's phase.  When the last
  level itself is not standard the piece is the whole trip.

The piece is run with `bbtools.symtm` on the smallest stretch of T it needs (the rest of the tape a context `L`, or
blank tape when it reaches the left end), and generalised: every block whose length can be made symbolic,
`2x + r` with the run still closing, is.  The result is a *shape*: a map from the block lengths of the start to
those of the end, valid for every value of the variables (the symbolic run is a proof sketch; `lean/top.py` turns
each shape into a Lean theorem).  A few trips do not close within the move budget: those are the trips in which a
new wall is built (the left end replays the run from blank tape for millions of steps); they are listed as `long`.

usage: python3 top.py events STEPS     each left/short trip: the walk length, the piece and its shape
       python3 top.py shapes STEPS     the distinct shapes, with how often each occurs (`lean/top_shapes.txt`)
       python3 top.py check STEPS      every trip that is not a counter trip, through its shape, against the run
"""
import collections
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "tools", "py"))
sys.path.insert(0, HERE)
import counter  # noqa: E402
import wall  # noqa: E402
from bbtools.machine import Machine  # noqa: E402
from bbtools.symtm import Blank, Config, Ctx, Lin, Rep, TouchContext, lin, run  # noqa: E402

M = Machine.parse(counter.M)
SHAPES = os.path.join(HERE, "..", "lean", "top_shapes.txt")
TURN_TAIL = "C> 1 1 0 0 1 0 1 R"        # the walk's phase: `W5 (0 1 R)` in Counter.lean
LAST_TAIL = "C> 0 1 0^inf"              # the right end
MOVES = 2000                            # move budget for a piece (more: `long`)
WALL_MOVES = 6000                       # the same for a piece with copy loops jumped over
GEN_MOVES = 2000                        # move budget for a symbolic trial


# ---------------------------------------------------------------- cutting a trip
def norm(t):
    """A token list of `counter.blocks` (ending `0 1`) as blocks b0..bn and seps s1..sn (`b0 s1 b1 ... sn bn`), with
    blocks of length 0 between two adjacent seps."""
    if len(t) < 2 or t[-2] != "0" or t[-1] != 1:
        raise ValueError("not at the right end")
    bs, ss, want_block = [], [], True
    for x in t[:-2]:
        if isinstance(x, int):
            bs.append(x)
            want_block = False
        else:
            if want_block:
                bs.append(0)
            ss.append(x)
            want_block = True
    if want_block:
        bs.append(0)
    return bs, ss


def walk(bs, ss):
    """(k, j): the walk from the right crosses k standard digit-0 levels (`first0`, then `walk0`), each with at
    least two pairs in the block before it; bs[j] is the block left of the last level crossed (or the last W, k=0)."""
    j, k = len(bs) - 1, 0
    while j >= 2:
        g, w = bs[j - 1], bs[j]
        if not (ss[j - 2] == "0" and ss[j - 1] == "0" and g % 2 == 0 and g >= 2 and w % 2 == 0
                and w >= (2 if k == 0 else 4) and bs[j - 2] >= 2):
            break
        k, j = k + 1, j - 2
    return k, j


def piece_tokens(bs, ss, k, j, frm):
    """The piece's tape: blocks frm..j (the last one less the two pairs the walk took), with the sep before
    block frm when frm > 0 (the rest of the tape is the context L)."""
    bb = list(bs[:j + 1])
    if k:
        bb[j] -= 2
    toks = [ss[frm - 1]] if frm > 0 else []
    for i in range(frm, j + 1):
        if i > frm:
            toks.append(ss[i - 1])
        toks.append(bb[i])
    return toks


def start_str(toks, k, frm):
    """The piece's start in symtm syntax.  A block is an int (concrete) or (var, a, b): 2 var + a + b pairs, as
    `(10)^a (1010)^var (10)^b` with the a + b pairs literal."""
    parts = ["0^inf" if frm == 0 else "L"]
    for t in toks:
        if isinstance(t, str):
            parts.append(t)
        elif isinstance(t, tuple):
            v, a, b = t
            parts += ["10"] * a + [f"(1010)^{v}"] + ["10"] * b
        elif t >= 8:                    # a long concrete block in units the sweeps cross whole
            parts += [f"(1010)^{t // 2}"] + ["10"] * (t % 2)
        elif t:
            parts.append(f"(10)^{t}")
    return " ".join(parts) + " " + (TURN_TAIL if k else LAST_TAIL)


def _at_end(turn):
    if turn:
        return lambda c: (c.state == 2 and len(c.right) == 1 and c.right[0] == Ctx("R") and not c.steps.is_zero())
    return lambda c: (c.state == 2 and len(c.right) == 3 and c.right[:2] == [0, 1] and isinstance(c.right[2], Blank)
                      and not c.steps.is_zero())


def run_piece(start, turn, moves=MOVES, jumps=None, walls=True):
    """The configuration where the piece ends (raises TouchContext, NeedSplit, Halted or RuntimeError).  Loops that
    build a wall are jumped over (`wall.run`); with `jumps` a list, the parts of the run are appended to it."""
    if not walls:
        return run(M, Config.parse(start), _at_end(turn), max_moves=moves)
    return wall.run(M, Config.parse(start), _at_end(turn), max_moves=moves, jumps=jumps)


def find_piece(bs, ss, k, j, walls=False):
    """(frm, toks): the smallest stretch of the tape the piece runs on; (None, reason) if it does not close."""
    for frm in range(j, -1, -1):
        toks = piece_tokens(bs, ss, k, j, frm)
        try:
            run_piece(start_str(toks, k, frm), k > 0, WALL_MOVES if walls else MOVES, walls=walls)
            return frm, toks
        except TouchContext:
            continue
        except Exception as e:     # noqa: BLE001  (a run that does not close: reported, not raised)
            return None, type(e).__name__
    return None, "TouchContext"


def generalize(toks, k, frm, walls=False):
    """Make blocks symbolic, longest first, `2x + r` with the smallest r that keeps the symbolic run closing (the r
    literal pairs all on one side of `(1010)^x`, or all but one; for a wall trip, split in any way).
    Returns (toks, values) with values[var] the variable's value in this trip."""
    toks = list(toks)
    order = sorted((i for i, t in enumerate(toks) if isinstance(t, int) and t >= 2), key=lambda i: -toks[i])
    vals = {}
    for i in order:
        n = toks[i]
        done = False
        for r in sorted({n % 2 + 2 * m for m in (0, 1, 2, 3, 4, 6, 8)}):
            if r > n or done:
                break
            splits = [(r, 0), (0, r), (1, r - 1), (r - 1, 1)]
            if walls:       # a wall trip may need its literal pairs anywhere around the repeat
                splits += [(a, r - a) for a in range(r + 1)]
            for a, b in dict.fromkeys(splits):
                if a < 0 or b < 0:
                    continue
                v = f"v{len(vals)}"
                trial = list(toks)
                trial[i] = (v, a, b)
                try:
                    run_piece(start_str(trial, k, frm), k > 0, WALL_MOVES if walls else GEN_MOVES, walls=walls)
                except Exception:   # noqa: BLE001
                    continue
                toks, vals[v], done = trial, (n - r) // 2, True
                break
    # rename the variables in order of appearance
    names, out = {}, []
    for t in toks:
        if isinstance(t, tuple):
            names[t[0]] = f"x{len(names)}"
            t = (names[t[0]], t[1], t[2])
        out.append(t)
    return out, {names[v]: x for v, x in vals.items()}


# ---------------------------------------------------------------- symbolic tapes as blocks
def stream(left):
    """symtm left tokens as cells and ('B', n) for (10)^n, the first item the context (Blank or Ctx)."""
    out = [left[0]]
    for t in left[1:]:
        if isinstance(t, int):
            out.append(t)
        elif isinstance(t, Rep):
            w = "".join(map(str, t.word))
            h = len(w) // 2
            if w == "10" * h:
                out.append(("B", h * t.n))
            elif w == "01" * h:
                out.append(("A", h * t.n))
            else:
                raise ValueError(f"repeat of {w}")
        else:
            raise ValueError(f"token {t}")
    while any(isinstance(t, tuple) and t[0] == "A" for t in out):     # 1 (01)^n = (10)^n 1, (01)^n 0 = 0 (10)^n
        i = next(i for i, t in enumerate(out) if isinstance(t, tuple) and t[0] == "A")
        if i + 1 < len(out) and out[i + 1] == 0:
            out[i:i + 2] = [0, ("B", out[i][1])]
        elif i >= 2 and out[i - 1] == 1:
            out[i - 1:i + 1] = [("B", out[i][1]), 1]
        else:
            raise ValueError("(01)^n with no neighbour to rotate with")
    return out


def blocks(left):
    """symtm left tokens as [context, then seps '0'/'1' and blocks Lin], blocks read greedily as in
    `counter.blocks` (runs of (10)^n and literal pairs 1 0)."""
    s = stream(left)
    out, i = [s[0]], 1

    def pair(i):
        return i + 1 < len(s) and s[i] == 1 and s[i + 1] == 0

    while i < len(s):
        if isinstance(s[i], tuple) or pair(i):
            n = lin(0)
            while i < len(s) and (isinstance(s[i], tuple) or pair(i)):
                if isinstance(s[i], tuple):
                    n, i = n + s[i][1], i + 1
                else:
                    n, i = n + 1, i + 2
            out.append(n)
        else:
            out.append(str(s[i]))
            i += 1
    if isinstance(out[0], Blank):
        while len(out) > 1 and out[1] == "0":
            out.pop(1)
    return out


def show(bl):
    """Blocks as text: `0^inf` or `L`, then seps and lengths."""
    out = []
    for t in bl:
        if isinstance(t, Blank):
            out.append("0^inf")
        elif isinstance(t, Ctx):
            out.append(t.name)
        else:
            out.append(str(t))
    return " ".join(out)


class Shape:
    """A generalised top piece: `start` in symtm syntax; `turn` (after a walk) or last (the whole trip); the start
    and end tapes as blocks; the step count (a linear expression)."""

    def __init__(self, start):
        self.start = start
        self.turn = start.endswith(TURN_TAIL)
        cfg = Config.parse(start)
        self.jumps = []
        try:                                    # a plain run if there is one, else with the loops jumped over
            fin = run(M, cfg.copy(), _at_end(self.turn), max_moves=MOVES)
            self.jumps = [(cfg.copy(), fin.copy())]
        except Exception:   # noqa: BLE001
            self.jumps = []
            fin = wall.run(M, cfg.copy(), _at_end(self.turn), max_moves=WALL_MOVES, jumps=self.jumps)
        self.wall = any(isinstance(j, wall.Jump) for j in self.jumps)
        self.steps = fin.steps
        self.lhs = blocks(cfg.left)
        self.rhs = blocks(fin.left)
        if self.turn:
            if self.rhs[-2:] != ["1", lin(1)]:
                raise ValueError(f"turn piece ends without `1 1 0` before the head: {show(self.rhs)}")
            self.rhs = self.rhs[:-2]
        self.vars = sorted(cfg.vars(), key=lambda v: int(v[1:]))

    def __repr__(self):
        return f"{'turn' if self.turn else 'last'}: {show(self.lhs)}  ->  {show(self.rhs)}"


def subst(bl, vals, ctx):
    """Concrete tokens (as `counter.blocks` writes them) from blocks with variables; ctx: the tokens of L."""
    out = []
    for t in bl:
        if isinstance(t, Blank):
            continue
        if isinstance(t, Ctx):
            out += ctx
        elif isinstance(t, Lin):
            n = t.subs(vals)
            if n < 0:
                raise ValueError("negative length")
            if n:
                out.append(n)
        else:
            out.append(t)
    return out


# ---------------------------------------------------------------- trips
_SHAPES = {}


def shape(start):
    if start not in _SHAPES:
        _SHAPES[start] = Shape(start)
    return _SHAPES[start]


def cut(before):
    """A trip from the token list before it: dict with k (levels walked), j, frm, the generalised start, values;
    or with 'long' set when the piece does not close."""
    bs, ss = norm(before)
    k, j = walk(bs, ss)
    walls = False
    frm, toks = find_piece(bs, ss, k, j)
    if frm is None:                     # a trip that builds a wall: the copy loops jumped over (`wall.py`)
        walls = True
        frm, toks = find_piece(bs, ss, k, j, walls=True)
    if frm is None:
        return {"k": k, "j": j, "long": toks}
    gt, vals = generalize(toks, k, frm, walls=walls)
    return {"k": k, "j": j, "frm": frm, "start": start_str(gt, k, frm), "vals": vals, "bs": bs, "ss": ss}


def predict(c):
    """The token list after the trip, from the shape (the piece) and the reset of the walked levels."""
    bs, ss, k, j, frm = c["bs"], c["ss"], c["k"], c["j"], c["frm"]
    sh = shape(c["start"])
    ctx = []
    for i in range(frm):
        if i:
            ctx.append(ss[i - 1])
        if bs[i]:
            ctx.append(bs[i])
    out = subst(sh.rhs, c["vals"], ctx)
    for lvl in range(k):                          # the walked levels, left to right, reset to digit 2
        g, w = bs[j + 1 + 2 * lvl], bs[j + 2 + 2 * lvl]
        last = lvl == k - 1
        out += ["1", g + 1, "1", w + 1 if last else w - 1]
    return out + ["0", 1]


def trips(steps):
    """(step, why, before, after) for each trip `counter.predict` does not cover."""
    ev = []
    counter.check(steps, ev)
    return ev


def load_shapes():
    """The shapes `lean/Top.lean` proves (one start per line)."""
    with open(SHAPES) as f:
        return [ln.rstrip("\n") for ln in f if ln.strip() and not ln.startswith("#")]


def check(steps):
    """Each non-counter trip through its shape, compared with the run: 'proved' (the shape is in
    lean/top_shapes.txt and the prediction is the run's tape), 'unlisted' (correct but the shape is not in the
    list), 'long', 'wrong'."""
    proved = set(load_shapes())
    tally = collections.Counter()
    for s, why, a, b in trips(steps):
        c = cut(a)
        if "long" in c:
            tally["long"] += 1
            continue
        ok = counter.tape_str(predict(c)) == counter.tape_str(b)
        tally[("proved" if c["start"] in proved else "unlisted") if ok else "wrong"] += 1
    return tally


def main(argv):
    if len(argv) != 2:
        sys.exit(__doc__)
    cmd, steps = argv[0], int(float(argv[1]))
    if cmd == "events":
        for s, why, a, b in trips(steps):
            c = cut(a)
            print(f"{s} {why} walk {c['k']}")
            print(f"   {' '.join(map(str, a))}")
            print(f"   {' '.join(map(str, b))}")
            if "long" in c:
                print(f"   long: the piece at block {c['j']} does not close in {MOVES} moves ({c['long']})")
            else:
                sh = shape(c["start"])
                vals = " ".join(f"{v}={x}" for v, x in c["vals"].items())
                print(f"   {sh}   [{vals}]")
    elif cmd == "shapes":
        n = collections.Counter()
        for s, why, a, b in trips(steps):
            c = cut(a)
            if "long" not in c:
                n[c["start"]] += 1
        print(f"# the top pieces of the trips to {steps:.3g} steps that counter.py does not cover, by frequency")
        print("# (generated by `python3 py/top.py shapes STEPS`; lean/top_gen.py proves each one)")
        for st, x in n.most_common():
            print(st)
    elif cmd == "check":
        t = check(steps)
        print(f"{sum(t.values())} trips to {steps:.3g} steps: " + ", ".join(f"{k} {v}" for k, v in sorted(t.items())))
    else:
        sys.exit(__doc__)


if __name__ == "__main__":
    main(sys.argv[1:])
