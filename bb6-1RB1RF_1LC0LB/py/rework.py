"""The rework rounds of a wall trip, as a function on lists of blocks, and the cases `lean/rework_gen.py` proves.

A wall trip (`top.py`, `wall.py`) starts at

    0^inf  [L]  1 10  0 (10)^(2x+2)  0 (10)^(2w+2)  C> 1 1 0 0 1 0 1 R          (or `C> 0 1 0^inf` at the right end)

with `L` a list of blocks `(s, b)`: a separator cell `s` and `b` pairs `10`, nearest first, the last one on blank
tape.  After a short start (`trig`) the head turns left at the level it copies,

    0^inf  [L]  1 B> (10)^X  0 (10)^(2w+3) ...                                          (Bturn L X)

and from there each *round* works on the blocks next to the level and comes back to the next turn with one pair of
the level less, until the level is one pair; the end (`FIN`) takes the last pair, makes every separator a 1 and
leaves the head at the right.  How the head handles a block in a round depends on what it carries from the block
before, and a round may sweep part of the list, or all of it, more than once.  So a round is computed as the machine
walks:

* a *left mode* `(q, lc, u)` (the head in state q on the cell u, the cells lc between it and the list) crosses the
  nearest block: it turns back inside it (`refl`: the block becomes some blocks and the head goes right in a *right
  mode* `(q, c)`, the cells c between the list and the head), or comes out on its far side in a new left mode, the
  block turned into a piece of tape `g` right of the head (`cont`);
* a right mode crosses a piece back to the right over the nearest block `(s, E)` of the list (`pass`: that block
  becomes some blocks), or turns left again at the list (`bounce`: a new left mode, the rest of the piece to its
  right); the level is a piece too, crossing it ends the round at the next turn.

Each case is a symbolic run of the machine (`symtm`) on a block of any length `2t+1` or `2t+2` (small values of `t`
apart, `con`, when the run needs them) or a piece with its parameter, so each is a lemma about every value; the round
is `sweep`/`rx` below, by recursion on the list, and `lean/ReworkCore.lean` proves by induction that the machine does
what the function says, from the case lemmas of `lean/Rework.lean`.  The cases are found on demand (`Cases`, not
frozen) by running the function on the wall shapes and on random lists, and saved to `lean/rework_cases.txt`; the
check of the trips and the Lean proof both use that saved table (frozen: a case not in it is `Stuck`).

usage: python3 rework.py check [n]     the round function against the plain simulator on n random lists
       python3 rework.py find [n]      find the cases (wall shapes, n random lists), write lean/rework_cases.txt
"""
import json
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "tools", "py"))
sys.path.insert(0, HERE)
from bbtools.machine import Machine  # noqa: E402
from bbtools.symtm import (Blank, Config, Ctx, Halted, Lin, NeedSplit, Rep, TouchContext, lin, parse_lin, step,  # noqa: E402
                           tokens, try_cross, try_rotate)

M = Machine.parse("1RB1RF_1LC0LB_1RE0LD_1LB0RF_0RA0RC_1RE---")
CASES = os.path.join(HERE, "..", "lean", "rework_cases.txt")
SHAPES = os.path.join(HERE, "..", "lean", "rework_shapes.txt")     # the wall shapes the cases were found from
B_, C_ = 1, 2
T4 = (1, 0, 1, 0)
START = (B_, (), (1,))                  # the left mode a round starts in (after one step from the turn)
TURN_MODE = (B_, (1,))                  # the right mode of a turn
END_MODE = (C_, ())                     # the right mode of the end
LEVEL = ("lv", (0, 0, 1, 0))            # the level after the first step of a round (then (10)^(X-2))
FIN = {"turn": ("ft", (0, 0, 0, Rep((1, 0), lin("t")), 0, 1, 0, 1)),        # the end, t = 2w + 3
       "last": ("fl", (0, 0, 0, Rep((1, 0), lin("t")), 1, 0, 1, 0, 0, 0, 0))}
TAIL_START = {"turn": [1, 1, 0, 0, 1, 0, 1, Ctx("R")], "last": [0, 1, Blank()]}
TAIL_TURN = {"turn": [0, 1, 0, 1], "last": [1, 0, 1]}    # after the W block at a turn
MAXJ = 4
MAXT = 6


class Stuck(Exception):
    """The function has no case for this (the list is not covered)."""


# ---------------------------------------------------------------- runs between two contexts
def _dir(c):
    h = c.right[0] if c.right else None
    if isinstance(h, Rep):
        h = h.word[0] if h.n.surely_ge(1) else None
    if not isinstance(h, int):
        return None
    tr = M.table[c.state][h]
    return None if tr is None else tr[1]


def _move(c):
    """One move as `symtm.run(rotate=True)` makes it."""
    if try_cross(M, c) is None:
        c2 = c.copy()
        if try_rotate(c2) is not None and try_cross(M, c2) is not None:
            c.left, c.right, c.steps = c2.left, c2.right, c2.steps
            return
        step(M, c)


def _stream(toks):
    """Cells and Reps as ('c', bit) and ('B', n) (n pairs `10`, literal pairs merged)."""
    out = []
    for t in toks:
        if isinstance(t, int):
            out.append(("c", t))
        elif isinstance(t, Rep):
            if t.n.is_zero():
                continue
            w = "".join(map(str, t.word))
            h = len(w) // 2
            if len(w) % 2 == 0 and w == "10" * h:
                out.append(("B", h * t.n))
            elif len(w) % 2 == 0 and w == "01" * h:
                out.append(("A", h * t.n))
            else:
                raise ValueError("repeat " + w)
        else:
            raise ValueError(str(t))
    while any(x[0] == "A" for x in out):          # (01)^n 0 = 0 (10)^n ; 1 (01)^n = (10)^n 1
        i = next(i for i, x in enumerate(out) if x[0] == "A")
        if i + 1 < len(out) and out[i + 1] == ("c", 0):
            out[i:i + 2] = [("c", 0), ("B", out[i][1])]
        elif i >= 1 and out[i - 1] == ("c", 1):
            out[i - 1:i + 1] = [("B", out[i][1]), ("c", 1)]
        else:
            raise ValueError("(01)^n")
    res, i = [], 0
    while i < len(out):
        if out[i] == ("c", 1) and i + 1 < len(out) and out[i + 1] == ("c", 0):
            res.append(("B", lin(1)))
            i += 2
        else:
            res.append(out[i])
            i += 1
    merged = []
    for x in res:
        if x[0] == "B" and merged and merged[-1][0] == "B":
            merged[-1] = ("B", merged[-1][1] + x[1])
        else:
            merged.append(x)
    return merged


def blocks(toks):
    """Left tokens (after the context) as blocks [(sep, Lin)] far first, and the cells after the last one (a lone
    last cell is a carry, not a block's separator)."""
    st = _stream(toks)
    its, i = [], 0
    while i < len(st):
        x = st[i]
        if x[0] != "c":
            raise ValueError("a block without a separator")
        if i == len(st) - 1:
            return its, (x[1],)
        n, j = lin(0), i + 1
        while j < len(st) and st[j][0] == "B":
            n, j = n + st[j][1], j + 1
        its.append((x[1], n))
        i = j
    return its, ()


def item_tokens(s, par, u, var, last):
    """The block (s, 2u + par) as left tokens; with var, u = t + u (t a variable): `(1010)^t` then the literal
    pairs.  The last block (on blank tape) has no separator token."""
    pairs = 2 * u + par
    out = [] if last else [s]
    if var:
        out.append(Rep(T4, lin("t")))
    return out + [1, 0] * pairs


def left_start(m, s, par, u, var, last):
    q, lc, um = m
    return Config(([Blank()] if last else [Ctx("L")]) + item_tokens(s, par, u, var, last) + list(lc), q,
                  list(um) + [Ctx("R")])


def left_run(m, s, par, u, var, last):
    c = left_start(m, s, par, u, var, last)
    start = c.copy()
    for _ in range(5000):
        if c.right and c.right[0] == Ctx("R"):
            its, cr = blocks(([0] if last else []) + c.left[1:])
            return ("refl", (c.state, cr), its), start, c
        if c.left and c.left[-1] == Ctx("L") and _dir(c) == -1:
            v = c.right[:-1]
            if not v or not isinstance(v[0], int):
                raise ValueError("cont on a repeat")
            return ("cont", (c.state, (), (v[0],)), tuple(v[1:])), start, c
        _move(c)
    raise RuntimeError("budget")


def subst_t(toks, t0, var):
    """Piece tokens with t := t + t0 (var) or t := t0."""
    out = []
    for x in toks:
        if isinstance(x, Rep) and "t" in x.n.c:
            a = x.n.c["t"]
            n = Lin(x.n.k + a * t0, {k: v for k, v in x.n.c.items() if k != "t"})
            if var:
                n = n + Lin(0, {"t": a})
            out.append(Rep(x.word, n))
        else:
            out.append(x)
    return tuple(out)


def rx_start(r, s, J, g):
    q, cc = r
    return Config([Ctx("L"), s, Rep((1, 0), lin("e"))] + [1, 0] * J + list(cc), q, list(g) + [Ctx("R")])


def rx_run(r, s, J, g, kind):
    """The right mode r at the piece g (kind 'g' a block's piece, 'lv' the level, 'ft'/'fl' the end of a trip that
    turns / that ends at the right end) over the open block s (10)^(e+J)."""
    c = rx_start(r, s, J, g)
    start = c.copy()
    for _ in range(8000):
        if kind == "fl" and c.state == C_ and c.right == [0, 1, 0, 0, 0, 0, Ctx("R")]:
            its, cr = blocks(c.left[1:])
            return ("pass", (c.state, cr), its), start, c
        if c.right and c.right[0] == Ctx("R"):
            if kind in ("lv", "fl") or (kind == "ft" and c.state != C_):
                raise ValueError("crossed the end")
            its, cr = blocks(c.left[1:])
            return ("pass", (c.state, cr), its), start, c
        if _dir(c) == -1:
            try:
                its, cr = blocks(c.left[1:])
            except ValueError:
                its = None
            if its is not None:
                if kind == "lv" and c.state == B_ and cr == (1,) and c.right == [1, 0, Ctx("R")]:
                    return ("pass", (c.state, cr), its), start, c
                if len(its) == 1 and its[0][1].c.get("e", 0) == 1 and isinstance(c.right[0], int) and len(cr) <= 1:
                    return ("bounce", (c.state, cr, (c.right[0],)), its, tuple(c.right[1:-1])), start, c
        _move(c)
    raise RuntimeError("budget")


def trig_start(tail, s, par, u, var, last):
    left = (([Blank()] if last else [Ctx("L")]) + item_tokens(s, par, u, var, last) + [1, 1, 0, 0]
            + [Rep(T4, lin("x")), 1, 0, 1, 0, 0, Rep(T4, lin("w")), 1, 0, 1, 0])
    return Config(left, C_, TAIL_START[tail])


def _turn_right(tail):
    toks = [Rep((1, 0), 2 * lin("x") + 3), 0, Rep((1, 0), 2 * lin("w") + 3)] + TAIL_TURN[tail]
    return _stream(toks)


def trig_run(tail, s, par, u, var, last):
    """The start of a wall trip, to the first turn: the first block replaced by blocks (far first)."""
    c = trig_start(tail, s, par, u, var, last)
    start = c.copy()
    want = _turn_right(tail)
    for _ in range(5000):
        if c.state == B_ and _dir(c) == -1:
            right = list(c.right[:-1])
            if tail == "last":
                while right and right[-1] == 0:
                    right.pop()
            try:
                ok = _stream(right) == want
            except ValueError:
                ok = False
            if ok:
                its, cr = blocks(([0] if last else []) + c.left[1:])
                if cr != (1,) or any(v in n.c for _, n in its for v in "xw"):
                    raise ValueError("turn without the carry")
                return its, start, c
        _move(c)
    raise RuntimeError("budget")


# ---------------------------------------------------------------- the table of cases
def _tok_str(toks):
    return " ".join(str(t) for t in toks)


def _str_tok(s):
    return tuple(tokens(s)) if s else ()


def _news_str(news):
    return [[sp, str(n)] for sp, n in news]


def _str_news(ns):
    return [(sp, parse_lin(n)) for sp, n in ns]


class Cases:
    """The cases.  Left modes `lms`, right modes `rms`, pieces `gs` (kind, tokens) are numbered by first use.

    left[(mi, s, par, last)] = {"off": o, "gen": outcome or None, "con": {u: outcome}}: the block (s, 2u + par) (last:
    the last block, on blank tape) in left mode mi; `gen` for u = t + o (t the run's variable), `con` for smaller u.
    Outcome ('refl', ri, news) or ('cont', mi', gi) (the piece's parameter is t, 0 for a `con` case).

    rx[(ri, s, gi)] = {"t0": t0, "gen": (J, outcome) or None, "con": {T: (J, outcome)}}: the piece gi with parameter
    T = t + t0 (gen) or T (con), over the open block (s, e + J).  Outcome ('pass', ri', news) or ('bounce', mi, news,
    gi') (the new piece's parameter t, 0 for con).

    trig[(tail, s, par, last)]: as left, outcome the news.  news: [(sep, Lin)] far first, in t and e."""

    def __init__(self, frozen=False):
        self.frozen = frozen
        self.lms, self.rms, self.gs = [START], [TURN_MODE, END_MODE], [LEVEL, FIN["turn"], FIN["last"]]
        self.left, self.rx, self.trig = {}, {}, {}

    def _idx(self, lst, x):
        if x not in lst:
            if self.frozen:
                raise Stuck(("new", x))
            lst.append(x)
        return lst.index(x)

    def lm(self, m):
        return self._idx(self.lms, m)

    def rm(self, r):
        return self._idx(self.rms, r)

    def gi(self, kind, toks):
        return self._idx(self.gs, (kind, tuple(toks)))

    # -- left
    def _left_out(self, o):
        if o[0] == "cont":
            return ("cont", self.lm(o[1]), self.gi("g", o[2]))
        return ("refl", self.rm(o[1]), o[2])

    def _off(self, par):
        return 1 if par == 0 else 0     # even blocks: u >= 1 (a block of 0 pairs is its own case)

    def left_case(self, mi, s, par, last):
        key = (mi, s, par, last)
        if key not in self.left:
            if self.frozen:
                raise Stuck(("L", key))
            ent = {"off": None, "gen": None, "con": {}}
            for t0 in range(MAXT):
                o = self._off(par) + t0
                try:
                    out = left_run(self.lms[mi], s, par, o, True, last)[0]
                except NeedSplit:
                    continue
                except (TouchContext, Halted, RuntimeError, ValueError):
                    break
                ent["off"], ent["gen"] = o, self._left_out(out)
                break
            self.left[key] = ent
        return self.left[key]

    def left_at(self, mi, s, b, last):
        """(outcome, t) for the block (s, b) in left mode mi."""
        if last and s != 0:
            raise Stuck(("last sep", mi, s, b))
        par, u = b % 2, b // 2
        ent = self.left_case(mi, s, par, last)
        if ent["gen"] is not None and u >= ent["off"]:
            return ent["gen"], u - ent["off"]
        if u not in ent["con"]:
            if self.frozen or (ent["off"] is not None and u >= ent["off"]):
                raise Stuck(("L", mi, s, par, last, u))
            try:
                ent["con"][u] = self._left_out(left_run(self.lms[mi], s, par, u, False, last)[0])
            except (NeedSplit, TouchContext, Halted, RuntimeError, ValueError):
                ent["con"][u] = None
        if ent["con"][u] is None:
            raise Stuck(("L", mi, s, par, last, u))
        return ent["con"][u], 0

    # -- right
    def _rx_out(self, o, kind):
        if o[0] == "bounce":
            return ("bounce", self.lm(o[1]), o[2], self.gi(kind, o[3]))
        return ("pass", self.rm(o[1]), o[2])

    def _rx_try(self, r, s, g, kind):
        for J in range(MAXJ):
            try:
                o = rx_run(r, s, J, g, kind)[0]
            except NeedSplit as ex:
                if "e" in str(ex):
                    continue
                return "split"
            except (TouchContext, Halted, RuntimeError, ValueError):
                return None
            return J, self._rx_out(o, kind)
        return None

    def rx_case(self, ri, s, gi):
        key = (ri, s, gi)
        if key not in self.rx:
            if self.frozen:
                raise Stuck(("R", key))
            ent = {"t0": 0, "gen": None, "con": {}}
            kind, g = self.gs[gi]
            hasvar = any(isinstance(x, Rep) and "t" in x.n.c for x in g)
            for t0 in (range(MAXT) if hasvar else [0]):
                res = self._rx_try(self.rms[ri], s, subst_t(g, t0, True) if hasvar else g, kind)
                if res == "split":
                    continue
                ent["t0"], ent["gen"] = t0, res
                break
            self.rx[key] = ent
        return self.rx[key]

    def rx_at(self, ri, s, gi, T):
        """(J, outcome, t) for the piece gi with parameter T over a block with separator s, from right mode ri."""
        ent = self.rx_case(ri, s, gi)
        if ent["gen"] is not None and T >= ent["t0"]:
            J, o = ent["gen"]
            return J, o, T - ent["t0"]
        if T not in ent["con"]:
            if self.frozen or (ent["gen"] is None and T >= ent["t0"]):
                raise Stuck(("R", ri, s, gi, T))
            kind, g = self.gs[gi]
            res = self._rx_try(self.rms[ri], s, subst_t(g, T, False), kind)
            ent["con"][T] = None if res == "split" else res
        if ent["con"][T] is None:
            raise Stuck(("R", ri, s, gi, T))
        J, o = ent["con"][T]
        return J, o, 0

    # -- start of a trip
    def trig_case(self, tail, s, par, last):
        key = (tail, s, par, last)
        if key not in self.trig:
            if self.frozen:
                raise Stuck(("T", key))
            ent = {"off": None, "gen": None, "con": {}}
            for t0 in range(MAXT):
                o = self._off(par) + t0
                try:
                    out = trig_run(tail, s, par, o, True, last)[0]
                except NeedSplit:
                    continue
                except (TouchContext, Halted, RuntimeError, ValueError):
                    break
                ent["off"], ent["gen"] = o, out
                break
            self.trig[key] = ent
        return self.trig[key]

    def trig_at(self, tail, s, b, last):
        par, u = b % 2, b // 2
        ent = self.trig_case(tail, s, par, last)
        if ent["gen"] is not None and u >= ent["off"]:
            return ent["gen"], u - ent["off"]
        if u not in ent["con"]:
            if self.frozen or (ent["off"] is not None and u >= ent["off"]):
                raise Stuck(("T", tail, s, par, last, u))
            try:
                ent["con"][u] = trig_run(tail, s, par, u, False, last)[0]
            except (NeedSplit, TouchContext, Halted, RuntimeError, ValueError):
                ent["con"][u] = None
        if ent["con"][u] is None:
            raise Stuck(("T", tail, s, par, last, u))
        return ent["con"][u], 0

    # -- saving
    def _out_json(self, o):
        if o is None:
            return None
        if o[0] in ("refl", "pass"):
            return [o[0], o[1], _news_str(o[2])]
        if o[0] == "cont":
            return list(o)
        return [o[0], o[1], _news_str(o[2]), o[3]]

    def _json_out(self, j):
        if j is None:
            return None
        if j[0] in ("refl", "pass"):
            return (j[0], j[1], _str_news(j[2]))
        if j[0] == "cont":
            return tuple(j)
        return (j[0], j[1], _str_news(j[2]), j[3])

    def save(self, path=CASES):
        def keep(e):
            return e["gen"] is not None or any(v is not None for v in e["con"].values())
        d = {"lms": [[q, list(lc), list(u)] for q, lc, u in self.lms],
             "rms": [[q, list(c)] for q, c in self.rms],
             "gs": [[k, _tok_str(t)] for k, t in self.gs],
             "left": [[list(k), e["off"], self._out_json(e["gen"]),
                       [[u, self._out_json(o)] for u, o in sorted(e["con"].items()) if o is not None]]
                      for k, e in sorted(self.left.items(), key=str) if keep(e)],
             "rx": [[list(k), e["t0"], None if e["gen"] is None else [e["gen"][0], self._out_json(e["gen"][1])],
                     [[T, v[0], self._out_json(v[1])] for T, v in sorted(e["con"].items()) if v is not None]]
                    for k, e in sorted(self.rx.items(), key=str) if keep(e)],
             "trig": [[list(k), e["off"], None if e["gen"] is None else _news_str(e["gen"]),
                       [[u, _news_str(o)] for u, o in sorted(e["con"].items()) if o is not None]]
                      for k, e in sorted(self.trig.items(), key=str) if keep(e)]}
        with open(path, "w") as f:
            f.write("# The cases of the rounds of wall trips (py/rework.py find); lean/rework_gen.py proves each one.\n")
            f.write(json.dumps(d, separators=(",", ":")).replace('],["', '],\n["').replace("]],[", "]],\n["))
            f.write("\n")

    @staticmethod
    def load(path=CASES):
        with open(path) as f:
            d = json.loads("".join(ln for ln in f if not ln.startswith("#")))
        c = Cases(frozen=True)
        c.lms = [(q, tuple(lc), tuple(u)) for q, lc, u in d["lms"]]
        c.rms = [(q, tuple(cc)) for q, cc in d["rms"]]
        c.gs = [(k, _str_tok(t)) for k, t in d["gs"]]
        for k, off, gen, con in d["left"]:
            c.left[tuple(k)] = {"off": off, "gen": c._json_out(gen), "con": {u: c._json_out(o) for u, o in con}}
        for k, t0, gen, con in d["rx"]:
            c.rx[tuple(k)] = {"t0": t0, "gen": None if gen is None else (gen[0], c._json_out(gen[1])),
                              "con": {T: (J, c._json_out(o)) for T, J, o in con}}
        for k, off, gen, con in d["trig"]:
            c.trig[tuple(k)] = {"off": off, "gen": None if gen is None else _str_news(gen),
                                "con": {u: _str_news(o) for u, o in con}}
        return c


_LOADED = None


def cases():
    global _LOADED
    if _LOADED is None:
        _LOADED = Cases.load()
    return _LOADED


# ---------------------------------------------------------------- the function
def _val(n, env):
    v = n.k + sum(a * env[x] for x, a in n.c.items())
    if v < 0:
        raise Stuck("negative")
    return v


def _news(news, env):
    return [(sp, _val(n, env)) for sp, n in news][::-1]


class Depth:
    def __init__(self):
        self.max = 0


def sweep(cs, mi, L, d=1, dp=None):
    """The left mode mi at the list L (nearest first): (right mode, list) when the head is back."""
    if dp is not None:
        dp.max = max(dp.max, d)
    if not L or d > 100000:
        raise Stuck("empty")
    (s, b), last = L[0], len(L) == 1
    o, t = cs.left_at(mi, s, b, last)
    if o[0] == "refl":
        return o[1], _news(o[2], {"t": t}) + L[1:]
    ri, L1 = sweep(cs, o[1], L[1:], d + 1, dp)
    return rx(cs, ri, o[2], t, L1, d + 1, dp)


def rx(cs, ri, gi, T, L, d=1, dp=None):
    if dp is not None:
        dp.max = max(dp.max, d)
    if not L or d > 100000:
        raise Stuck("empty")
    s, E = L[0]
    J, o, t = cs.rx_at(ri, s, gi, T)
    if E < J:
        raise Stuck(("J", ri, s, gi))
    news = _news(o[2], {"e": E - J, "t": t})
    if o[0] == "pass":
        return o[1], news + L[1:]
    ri2, L3 = sweep(cs, o[1], news + L[1:], d + 1, dp)
    return rx(cs, ri2, o[3], t, L3, d + 1, dp)


def round_(cs, L, dp=None):
    """One round from a turn with the level of at least two pairs: the list at the next turn."""
    ri, L1 = sweep(cs, cs.lm(START), L, 1, dp)
    ri2, L2 = rx(cs, ri, cs.gi(*LEVEL), 0, L1, 1, dp)
    if cs.rms[ri2] != TURN_MODE:
        raise Stuck("no turn")
    return L2


def rounds(cs, L, n, dp=None):
    """n rounds; a list on which a round only adds 2 to the last block (the copy loop) is fast-forwarded."""
    while n > 0:
        L2 = round_(cs, L, dp)
        n -= 1
        if L2[:-1] == L[:-1] and L2[-1] == (L[-1][0], L[-1][1] + 2) and L[-1][1] >= 4 * MAXT + 8:
            return L2[:-1] + [(L2[-1][0], L2[-1][1] + 2 * n)]
        L = L2
    return L


def trig(cs, tail, L):
    if not L:
        raise Stuck("empty")
    (s, b), last = L[0], len(L) == 1
    if last and s != 0:
        raise Stuck("last sep")
    news, t = cs.trig_at(tail, s, b, last)
    return _news(news, {"t": t}) + L[1:]


def wall_end(cs, tail, L, x, w, dp=None):
    """The blocks after the wall trip from `L 1 10 0 (10)^(2x+2) 0 (10)^(2w+2) C> tail`: for a trip that turns,
    the tape after `0 1 1` (F3 in Counter.lean) at the head, else the whole tape left of the head."""
    L1 = trig(cs, tail, L)
    L2 = rounds(cs, L1, 2 * x + 2, dp)
    ri, L3 = sweep(cs, cs.lm(START), L2, 1, dp)
    ri2, L4 = rx(cs, ri, cs.gi(*FIN[tail]), 2 * w + 3, L3, 1, dp)
    if cs.rms[ri2] != END_MODE:
        raise Stuck("no end")
    if tail == "turn":
        if not L4 or L4[0] != (1, 1) or len(L4) < 2 or L4[1][1] < 1:
            raise Stuck("end")
        return L4[1:]
    return L4


def predict(before):
    """The token list after a trip (as `top.predict`) when it is a wall trip of `lean/Rework.lean`, else None.

    The piece (`top.piece_tokens`, the walked levels cut off) must be `b0 s1 b1 ... sn bn  1 1  0 X  0 W` with X and
    W even and at least 2: the start of `wall_turn` (the walk over standard levels before it, `counter_borrow_ex`)
    or of `wall_last`, with L the blocks `(0, b0), (s1, b1), ...` nearest first, `X = 2x + 2`, `W = 2w + 2`.  The
    end is `wall_end` (what `wallT`/`wallL` compute), then the walked levels reset as for any borrow."""
    import top
    bs, ss = top.norm(before)
    k, j = top.walk(bs, ss)
    items = top.piece_tokens(bs, ss, k, j, 0)
    if len(items) < 7 or items[-6:-3] != ["1", 1, "0"] or items[-2] != "0":
        return None
    X, W = items[-3], items[-1]
    if X % 2 or W % 2 or X < 2 or W < 2:
        return None
    body = items[:-6]
    L = [(0, body[0])] + [(int(body[i]), body[i + 1]) for i in range(1, len(body), 2)]
    try:
        L2 = wall_end(cases(), "turn" if k else "last", L[::-1], X // 2 - 1, W // 2 - 1)
    except Stuck:
        return None
    out = []
    for i, (sp, b) in enumerate(L2[::-1]):
        out += ([str(sp)] if i else []) + [b]
    for lvl in range(k):                          # the walked levels, left to right, reset to digit 2
        g, w = bs[j + 1 + 2 * lvl], bs[j + 2 + 2 * lvl]
        out += ["1", g + 1, "1", w + 1 if lvl == k - 1 else w - 1]
    return out + ["0", 1]


# ---------------------------------------------------------------- the plain simulator, for checking
T = {(0, 0): (1, 1, 1), (0, 1): (1, 1, 5), (1, 0): (1, -1, 2), (1, 1): (0, -1, 1), (2, 0): (1, 1, 4),
     (2, 1): (0, -1, 3), (3, 0): (1, -1, 1), (3, 1): (0, 1, 5), (4, 0): (0, 1, 0), (4, 1): (0, 1, 2),
     (5, 0): (1, 1, 4)}


def cells_of(L):
    s = ""
    for sp, b in reversed(L):
        s += str(sp) + "10" * b
    return s[1:]


def parse_items(cells):
    """Greedy: pairs `10`, any other cell a separator (the reading the rounds are compared in)."""
    s = cells.lstrip("0")
    out, i, cur, sep = [], 0, 0, 0
    while i < len(s):
        if s[i:i + 2] == "10":
            cur += 1
            i += 2
        else:
            out.append((sep, cur))
            sep, cur = int(s[i]), 0
            i += 1
    out.append((sep, cur))
    return out[::-1]


def sim_turns(L, X, W=5, turns=3, maxsteps=10 ** 6):
    """The lists of the next turns of the plain machine from Bturn L X (as greedy blocks)."""
    left = cells_of(L) + "1"
    right = "10" * X + "0" + "10" * W + "0101"
    tape = {k: int(ch) for k, ch in enumerate(left + right)}
    pos, q, last, out, n = len(left), 1, -1, [], 0
    while n < maxsteps and len(out) < turns:
        tr = T.get((q, tape.get(pos, 0)))
        if tr is None:
            break
        w, d, q2 = tr
        if last == 1 and d == -1 and q == 1:
            hi = max(tape)
            rest = "".join(str(tape.get(k, 0)) for k in range(pos, hi + 1)).rstrip("0")
            lft = "".join(str(tape.get(k, 0)) for k in range(min(tape), pos))
            lv = rest[:len(rest) - 2 * W - 5]
            if rest.endswith("0" + "10" * W + "0101") and lv == "10" * (len(lv) // 2) and lft.endswith("1"):
                out.append((parse_items(lft[:-1]), len(lv) // 2))
        tape[pos] = w
        last, pos, q, n = d, pos + d, q2, n + 1
    return out


def sim_wall(tail, L, x, w, maxsteps=10 ** 8):
    """The plain machine on the wall trip's start: the cells left of the head at its end."""
    left = cells_of(L) + "1" + "10" + "0" + "10" * (2 * x + 2) + "0" + "10" * (2 * w + 2)
    right = "1100101" if tail == "turn" else "01"
    tape = {k: int(ch) for k, ch in enumerate(left + right)}
    pos, q, n = len(left), 2, 0
    end = len(left) + len(right)
    while n < maxsteps:
        if q == 2 and n and (pos == end if tail == "turn" else
                             (tape.get(pos, 0), tape.get(pos + 1, 0)) == (0, 1) and
                             all(tape.get(k, 0) == 0 for k in range(pos + 2, max(tape) + 1))):
            return "".join(str(tape.get(k, 0)) for k in range(min(tape), pos))
        if tail == "turn" and pos >= end:
            return None
        tr = T.get((q, tape.get(pos, 0)))
        if tr is None:
            return None
        wr, d, q2 = tr
        tape[pos] = wr
        pos, q, n = pos + d, q2, n + 1
    return None


def random_list(rng, lo=1, hi=9, n=6):
    return [(rng.choice((0, 1)), rng.randint(lo, hi)) for _ in range(rng.randint(0, n))] + [(0, rng.randint(lo, hi))]


def check(cs, n=300, seed=1, verbose=False):
    """Rounds of random lists against the plain simulator."""
    rng = random.Random(seed)
    ok = stuck = bad = 0
    for _ in range(n):
        L = random_list(rng)
        sims = sim_turns(L, 30, turns=4)
        cur = L
        for k, (Ls, Xs) in enumerate(sims):
            try:
                cur = round_(cs, cur)
            except Stuck as ex:
                stuck += 1
                if verbose:
                    print("stuck", L, k, ex)
                break
            if parse_items(cells_of(cur)) != Ls or Xs != 30 - k - 1:
                bad += 1
                print("MISMATCH", L, k, cur, Ls, Xs)
                break
        else:
            ok += 1
    print(f"rounds: ok {ok}, stuck {stuck}, wrong {bad}")
    return bad == 0


def check_walls(cs, lists, verbose=False):
    """Whole wall trips (tail, L, x, w) against the plain simulator."""
    ok = stuck = bad = 0
    for tail, L, x, w in lists:
        try:
            got = wall_end(cs, tail, L, x, w)
        except Stuck as ex:
            stuck += 1
            if verbose:
                print("stuck", tail, L, x, w, ex)
            continue
        want = sim_wall(tail, L, x, w)
        cells = cells_of(got)
        if tail == "turn":
            cells += "110"
        if want is None or want.lstrip("0") != cells.lstrip("0"):
            bad += 1
            print("MISMATCH", tail, L, x, w, got, want)
        else:
            ok += 1
    print(f"walls: ok {ok}, stuck {stuck}, wrong {bad}")
    return bad == 0


def shape_lists(rng, per=6):
    """Wall trip starts from the wall shapes of lean/rework_shapes.txt with random values: (tail, L, x, w)."""
    import family
    import top
    out = []
    with open(SHAPES) as f:
        shapes = [ln.rstrip("\n") for ln in f if ln.strip() and not ln.startswith("#")]
    for sh in shapes:
        parts = sh.split()
        h = next(k for k, p in enumerate(parts) if p.endswith(">") and len(p) == 2)
        tail = "turn" if sh.endswith(top.TURN_TAIL) else "last" if sh.endswith(top.LAST_TAIL) else None
        try:
            it = family._items(parts[1:h])
        except ValueError:
            continue
        if tail is None or len(it) < 7 or it[-6:-3] != ["1", lin(1), "0"] or it[-2] != "0":
            continue
        vs = sorted({v for x in it if isinstance(x, Lin) for v in x.c})
        for _ in range(per):
            env = {v: rng.randint(0, 6) for v in vs}
            vals = [x if isinstance(x, str) else x.subs(env) for x in it]
            X, W = vals[-3], vals[-1] - (2 if tail == "turn" else 0)
            if X % 2 or W % 2 or X < 2 or W < 2:
                continue
            body = vals[:-6]            # b0 s1 b1 ... sn bn
            L = [(0, body[0])] + [(int(body[k]), body[k + 1]) for k in range(1, len(body), 2)]
            out.append((tail, L[::-1], X // 2 - 1, W // 2 - 1))
    return out


def find(n=400, seed=1):
    """Find the cases: the wall shapes with random values, random lists in rounds and as wall trips."""
    cs = Cases()
    rng = random.Random(seed)
    lists = shape_lists(rng, per=30)
    for _ in range(n):
        if rng.random() < 0.8:
            L = [(1, 2 * rng.randint(0, 5) + 1)] + random_list(rng)
        else:
            L = [(0, 2 * rng.randint(0, 5) + 1)]
        lists.append((rng.choice(("turn", "last")), L, rng.randint(0, 6), rng.randint(0, 6)))
    for tail, L, x, w in lists:
        try:
            wall_end(cs, tail, L, x, w)
        except Stuck:
            pass
    for _ in range(n):
        L = random_list(rng)
        for _ in range(4):
            try:
                L = round_(cs, L)
            except Stuck:
                break
    for _ in range(3):              # the small values below each threshold, and what they lead to
        fill(cs)
        for tail, L, x, w in lists:
            try:
                wall_end(cs, tail, L, x, w)
            except Stuck:
                pass
    return cs, lists


def fill(cs):
    """Run every case's values below its threshold."""
    for (mi, s, par, last), e in list(cs.left.items()):
        for u in range(e["off"] or 0):
            if not (par == 0 and u == 0 and last):
                try:
                    cs.left_at(mi, s, 2 * u + par, last)
                except Stuck:
                    pass
    for (ri, s, gi), e in list(cs.rx.items()):
        for T in range(e["t0"]):
            try:
                cs.rx_at(ri, s, gi, T)
            except Stuck:
                pass
    for (tail, s, par, last), e in list(cs.trig.items()):
        for u in range(e["off"] or 0):
            try:
                cs.trig_at(tail, s, 2 * u + par, last)
            except Stuck:
                pass


def main(argv):
    if argv and argv[0] == "find":
        cs, lists = find(int(argv[1]) if len(argv) > 1 else 400)
        cs.save()
        cs = Cases.load()
        print(f"{len(cs.lms)} left modes, {len(cs.rms)} right modes, {len(cs.gs)} pieces; "
              f"{len(cs.left)} left, {len(cs.rx)} right, {len(cs.trig)} start cases")
        check(cs, 200, seed=7)
        check_walls(cs, lists[:300])
    elif argv and argv[0] == "check":
        cs = cases()
        ok = check(cs, int(argv[1]) if len(argv) > 1 else 300, verbose="-v" in argv)
        ok = check_walls(cs, shape_lists(random.Random(3)), verbose="-v" in argv) and ok
        sys.exit(0 if ok else 1)
    else:
        print(__doc__)


if __name__ == "__main__":
    main(sys.argv[1:])
