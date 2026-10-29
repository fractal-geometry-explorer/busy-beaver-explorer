"""Symbolic simulation of any two-symbol machine, and Lean proofs of the rules it finds.

Generalises `bb6-holdout/rec/symtm.py` and `bb6-holdout/lean/gen_rules.py`, which did this for one machine with three
hand-found cycle lemmas.  Here the machine is a parameter and the cycle lemmas are found as the run needs them.

A configuration is  left-tokens  S>  right-tokens : the head, in state S, reads the first right token.  Tokens are
literal cells 0/1, `Rep(word, n)` for a word repeated n times (n a linear expression in variables that range over
the natural numbers), `Ctx(name)`: an unknown stretch of tape the run may not look at, or `Blank()`: blank tape.
A left token list starts with a Ctx or Blank, a right token list ends with one.

Two kinds of moves:
* a single machine step (expanding a repeat whose count is surely >= 1; a count that might be 0 stops the run with
  `NeedSplit`, and the rule has to be stated with a count like `n + 1`);
* a *shift rule*: if the head is at a repeat `Rep(w, k)` and one copy of `w` takes the head, in the same state, to
  the far side of the copy without looking past it (a word `u` next to the head may travel along), then all k copies
  are crossed at once.  Found by simulating one copy between two contexts.  In Lean these are `TM.cross_r` and
  `TM.cross_l`, applied with the one-copy run proved by `rfl`.

`prove(machine, name, start, end)` runs from `start` until the configuration equals `end` (after re-bracketing
literals into repeats, `canon`) and returns the Lean theorem that the run takes the stated number of steps, with a
proof made only of `rfl` steps, the crossing lemmas and `omega` for the step count.  The theorem states the end
configuration as the run reaches it, which can differ from `end` by re-bracketing (`1 (1)^n` for `(1)^n 1`; Lean
has `TM.rep_rotate` for those), so state `end` the way the run writes it when rules are to be chained.  The theorem is about every value
of the variables and every tape in the contexts.  Lean, not this module, is the judge: a wrong trace fails to check.
"""
from dataclasses import dataclass

from .machine import Machine, STATES


# ---------------------------------------------------------------- linear expressions
class Lin:
    __slots__ = ("c", "k")

    def __init__(self, k=0, c=None):
        if isinstance(k, Lin):
            self.c, self.k = dict(k.c), k.k
            return
        if isinstance(k, str):
            self.c, self.k = {k: 1}, 0
            return
        self.k = k
        self.c = {v: a for v, a in (c or {}).items() if a}

    def __add__(self, o):
        o = lin(o)
        c = dict(self.c)
        for v, a in o.c.items():
            c[v] = c.get(v, 0) + a
        return Lin(self.k + o.k, c)

    __radd__ = __add__

    def __sub__(self, o):
        return self + (-1) * lin(o)

    def __rmul__(self, a):
        return Lin(a * self.k, {v: a * b for v, b in self.c.items()})

    def __mul__(self, a):
        if isinstance(a, Lin):
            if a.is_const():
                return a.k * self
            if self.is_const():
                return self.k * a
            raise ValueError("product of two variables")
        return a * self

    def surely_ge(self, n):
        return all(a >= 0 for a in self.c.values()) and self.k >= n

    def is_zero(self):
        return not self.c and self.k == 0

    def is_const(self):
        return not self.c

    def subs(self, env):
        return self.k + sum(a * env[v] for v, a in self.c.items())

    def vars(self):
        return set(self.c)

    def __eq__(self, o):
        o = lin(o)
        return self.k == o.k and self.c == o.c

    def __hash__(self):
        return hash((self.k, tuple(sorted(self.c.items()))))

    def __repr__(self):
        parts = [(f"{a}*{v}" if a != 1 else v) for v, a in sorted(self.c.items())]
        if self.k or not parts:
            parts.append(str(self.k))
        return "+".join(parts).replace("+-", "-")

    def lean(self):
        if any(a < 0 for a in self.c.values()) or (self.k < 0):
            raise ValueError(f"negative term in {self} has no Nat form")
        parts = [(v if a == 1 else f"{a} * {v}") for v, a in sorted(self.c.items())]
        if self.k or not parts:
            parts.append(str(self.k))
        return " + ".join(parts)


def lin(x):
    return x if isinstance(x, Lin) else Lin(x)


@dataclass(frozen=True)
class Rep:
    word: tuple
    n: Lin

    def __repr__(self):
        return f"({''.join(map(str, self.word))})^{self.n}"


@dataclass(frozen=True)
class Ctx:
    name: str

    def __repr__(self):
        return self.name


@dataclass(frozen=True)
class Blank:
    def __repr__(self):
        return "0^inf"


class TouchContext(Exception):
    pass


class NeedSplit(Exception):
    pass


class Halted(Exception):
    pass


def parse_lin(e):
    total, sign, cur = Lin(0), 1, ""
    for ch in e.replace(" ", "") + "+":
        if ch in "+-":
            if cur:
                if "*" in cur:
                    a, v = cur.split("*")
                    term = int(a) * Lin(v)
                else:
                    term = Lin(int(cur)) if cur.isdigit() else Lin(cur)
                total = total + sign * term
            sign, cur = (1 if ch == "+" else -1), ""
        else:
            cur += ch
    return total


def tokens(s):
    """Parse a tape string: '0^inf 1 0 (10)^n+1 1^k L'.  `(w)^e` and `x^e` are repeats (e an expression in variables),
    digits are cells, '0^inf' is blank tape, any other name is a context."""
    out = []
    for part in s.split():
        if part == "0^inf":
            out.append(Blank())
        elif part.startswith("("):
            w, e = part[1:].split(")^")
            out.append(Rep(tuple(int(ch) for ch in w), parse_lin(e)))
        elif "^" in part and part[0] in "01":
            w, e = part.split("^")
            out.append(Rep(tuple(int(ch) for ch in w), parse_lin(e)))
        elif part.isdigit():
            out.extend(int(ch) for ch in part)
        else:
            out.append(Ctx(part))
    return out


# ---------------------------------------------------------------- configurations
class Config:
    def __init__(self, left, state, right, steps=0):
        self.left, self.state, self.right = list(left), state, list(right)
        self.steps = lin(steps)

    @staticmethod
    def parse(s):
        """'L 1 0 C> 1^n R': the head in state C on the first token after 'C>'."""
        parts = s.split()
        i = next(k for k, p in enumerate(parts) if p.endswith(">") and len(p) == 2)
        return Config(tokens(" ".join(parts[:i])), STATES.index(parts[i][0]), tokens(" ".join(parts[i + 1:])))

    def copy(self):
        return Config(self.left, self.state, self.right, self.steps)

    def __repr__(self):
        return " ".join(map(str, self.left)) + f" {STATES[self.state]}> " + " ".join(map(str, self.right))

    def vars(self):
        vs = set()
        for t in self.left + self.right:
            if isinstance(t, Rep):
                vs |= t.n.vars()
        return vs

    def contexts(self):
        return [t.name for t in self.left + self.right if isinstance(t, Ctx)]


def _unroll_front(seq):
    while seq and isinstance(seq[0], Rep):
        r = seq[0]
        if r.n.is_zero():
            seq.pop(0)
            continue
        if not r.n.surely_ge(1):
            raise NeedSplit(r)
        rest = [Rep(r.word, r.n - 1)] if not (r.n - 1).is_zero() else []
        seq[0:1] = list(r.word) + rest
    if not seq:
        raise TouchContext("end of tape")
    if isinstance(seq[0], Blank):
        seq.insert(0, 0)
    if isinstance(seq[0], Ctx):
        raise TouchContext(seq[0])
    return seq[0]


def _unroll_back(seq):
    while seq and isinstance(seq[-1], Rep):
        r = seq[-1]
        if r.n.is_zero():
            seq.pop()
            continue
        if not r.n.surely_ge(1):
            raise NeedSplit(r)
        rest = [Rep(r.word, r.n - 1)] if not (r.n - 1).is_zero() else []
        seq[-1:] = rest + list(r.word)
    if not seq:
        raise TouchContext("end of tape")
    if isinstance(seq[-1], Blank):
        seq.append(0)
    if isinstance(seq[-1], Ctx):
        raise TouchContext(seq[-1])
    return seq[-1]


def step(m, cfg):
    """One machine step on a symbolic configuration."""
    sym = _unroll_front(cfg.right)
    tr = m.table[cfg.state][sym]
    if tr is None:
        raise Halted(f"{STATES[cfg.state]}{sym}")
    w, d, s = tr
    cfg.right[0] = w
    if d == 1:
        cfg.left.append(cfg.right.pop(0))
    else:
        _unroll_back(cfg.left)
        cfg.right.insert(0, cfg.left.pop())
    cfg.state = s
    cfg.steps = cfg.steps + 1


# ---------------------------------------------------------------- shift rules
MAX_CARRY = 3
MAX_CYCLE = 400


def _one_copy_right(m, q, u, w):
    """L u q> w R  ->  L v u q> R ?  Returns (v, steps) or None."""
    c = Config([Ctx("L")] + list(u), q, list(w) + [Ctx("R")])
    try:
        for n in range(1, MAX_CYCLE + 1):
            step(m, c)
            if (c.state == q and c.right == [Ctx("R")] and len(c.left) == 1 + len(w) + len(u)
                    and c.left[len(c.left) - len(u):] == list(u) and all(isinstance(x, int) for x in c.left[1:])):
                return tuple(c.left[1:1 + len(w)]), n
    except (TouchContext, Halted):
        return None
    return None


def _one_copy_left(m, q, u, w):
    """L w q> u R  ->  L q> u v R ?  Returns (v, steps) or None."""
    c = Config([Ctx("L")] + list(w), q, list(u) + [Ctx("R")])
    try:
        for n in range(1, MAX_CYCLE + 1):
            step(m, c)
            if (c.state == q and c.left == [Ctx("L")] and len(c.right) == len(u) + len(w) + 1
                    and c.right[:len(u)] == list(u) and all(isinstance(x, int) for x in c.right[:-1])):
                return tuple(c.right[len(u):len(u) + len(w)]), n
    except (TouchContext, Halted):
        return None
    return None


@dataclass
class Cross:
    """A shift rule applied: direction 'r' or 'l', carried word u, crossed word w, image v, steps per copy s, count k."""
    d: str
    u: tuple
    w: tuple
    v: tuple
    s: int
    k: Lin


def try_cross(m, cfg):
    """Apply a shift rule if the head is at a repeat that one copy's run crosses. Returns the Cross or None."""
    if cfg.right and isinstance(cfg.right[0], Rep) and not cfg.right[0].n.is_zero():
        rep = cfg.right[0]
        for lu in range(0, MAX_CARRY + 1):
            tail = cfg.left[len(cfg.left) - lu:] if lu else []
            if len(cfg.left) <= lu or not all(isinstance(x, int) for x in tail):
                break
            r = _one_copy_right(m, cfg.state, tuple(tail), rep.word)
            if r:
                v, s = r
                cfg.left = cfg.left[:len(cfg.left) - lu] + [Rep(v, rep.n)] + list(tail)
                cfg.right = cfg.right[1:]
                cfg.steps = cfg.steps + s * rep.n
                return Cross("r", tuple(tail), rep.word, v, s, rep.n)
    if cfg.left and isinstance(cfg.left[-1], Rep) and not cfg.left[-1].n.is_zero():
        rep = cfg.left[-1]
        for lu in range(1, MAX_CARRY + 1):
            head = cfg.right[:lu]
            if len(cfg.right) <= lu or not all(isinstance(x, int) for x in head):
                break
            r = _one_copy_left(m, cfg.state, tuple(head), rep.word)
            if r:
                v, s = r
                cfg.left = cfg.left[:-1]
                cfg.right = list(head) + [Rep(v, rep.n)] + cfg.right[lu:]
                cfg.steps = cfg.steps + s * rep.n
                return Cross("l", tuple(head), rep.word, v, s, rep.n)
    return None


# ---------------------------------------------------------------- canonical form
def canon(seq):
    """A normal form for comparing token lists: constant repeats expanded, literals pushed to the right of symbolic
    repeats of the same word, adjacent repeats of one word merged."""
    out = []
    for t in seq:
        if isinstance(t, Rep):
            const, var = t.n.k, Lin(0, t.n.c)
            if var.is_zero():
                out.extend(list(t.word) * const)
                continue
            if const < 0:
                raise ValueError("negative constant in a count")
            out.append(Rep(t.word, var))
            out.extend(list(t.word) * const)
        else:
            out.append(t)
    changed = True
    while changed:
        changed = False
        for i in range(len(out)):
            t = out[i]
            if not isinstance(t, Rep):
                continue
            L = len(t.word)
            pre = out[max(0, i - L):i]
            if len(pre) == L and all(isinstance(x, int) for x in pre) and tuple(pre) == t.word:
                out[i - L:i + 1] = [t] + list(t.word)       # w (w)^n = (w)^n w
                changed = True
                break
            if L > 1 and i >= 1 and isinstance(out[i - 1], int) and out[i - 1] == t.word[-1]:
                x = out[i - 1]
                out[i - 1:i + 1] = [Rep((x,) + t.word[:-1], t.n), x]   # x (y x)^n = (x y)^n x
                changed = True
                break
            if i >= 1 and isinstance(out[i - 1], Rep) and out[i - 1].word == t.word:
                out[i - 1:i + 1] = [Rep(t.word, out[i - 1].n + t.n)]
                changed = True
                break
    while len(out) >= 2 and out[-1] == Blank() and out[-2] == 0:
        out.pop(-2)
    while len(out) >= 2 and out[0] == Blank() and out[1] == 0:
        out.pop(1)
    return out


def same_config(c1, c2):
    head = lambda c: Ctx("HEAD:" + STATES[c.state])
    return canon(c1.left + [head(c1)] + c1.right) == canon(c2.left + [head(c2)] + c2.right)


# ---------------------------------------------------------------- runs
def run(m, cfg, stop, max_moves=100000, cross=True, trace=None):
    """Advance until stop(cfg). Shift rules first, then single steps.  With `trace` a list, appends
    ('step', before, after) or ('cross', before, after, Cross) for each move."""
    for _ in range(max_moves):
        if stop(cfg):
            return cfg
        before = cfg.copy() if trace is not None else None
        x = try_cross(m, cfg) if cross else None
        if x is None:
            step(m, cfg)
            if trace is not None:
                trace.append(("step", before, cfg.copy()))
        elif trace is not None:
            trace.append(("cross", before, cfg.copy(), x))
    raise RuntimeError(f"no stop after {max_moves} moves: {cfg}")


# ---------------------------------------------------------------- Lean
B = {0: "false", 1: "true"}


def _word(w):
    return "[" + ", ".join(B[x] for x in w) + "]"


def right_term(tks):
    acc = None
    for t in reversed(tks):
        if isinstance(t, Ctx):
            assert acc is None, "context inside the right tokens"
            acc = t.name
        elif isinstance(t, Blank):
            assert acc is None, "blank inside the right tokens"
            acc = "blank"
        elif isinstance(t, int):
            acc = f"cons {B[t]} ({acc})"
        elif isinstance(t, Rep):
            if t.n.is_zero():
                continue
            acc = f"rep ({t.n.lean()}) {_word(t.word)} ({acc})"
    if acc is None:
        raise ValueError("right tokens must end with a context or blank tape")
    return acc


def left_term(tks):
    acc = None
    for t in tks:
        if isinstance(t, Ctx):
            assert acc is None, "context inside the left tokens"
            acc = t.name
        elif isinstance(t, Blank):
            assert acc is None, "blank inside the left tokens"
            acc = "blank"
        elif isinstance(t, int):
            acc = f"cons {B[t]} ({acc})"
        elif isinstance(t, Rep):
            if t.n.is_zero():
                continue
            acc = f"rep ({t.n.lean()}) {_word(tuple(reversed(t.word)))} ({acc})"
    if acc is None:
        raise ValueError("left tokens must start with a context or blank tape")
    return acc


def cfg_term(c):
    return f"⟨{left_term(c.left)}, {right_term(c.right)}, .{STATES[c.state]}⟩"


def _segments(trace):
    """Group consecutive single steps: [('steps', before, after, n) | ('cross', before, after, Cross)]."""
    segs = []
    for ev in trace:
        if ev[0] == "step":
            if segs and segs[-1][0] == "steps":
                segs[-1] = ("steps", segs[-1][1], ev[2], segs[-1][3] + 1)
            else:
                segs.append(("steps", ev[1], ev[2], 1))
        else:
            segs.append(ev)
    return segs


class ProofError(Exception):
    pass


def prove(m, name, start, end, nsteps=None, doc=None, max_moves=100000, cross=True):
    """Lean theorem `name`: from `start` the machine reaches `end` in `nsteps` steps (default: the run's count).
    `start`, `end`: Config or strings for Config.parse.  Returns (lean_text, final_config)."""
    m = Machine.parse(m) if isinstance(m, str) else m
    start = Config.parse(start) if isinstance(start, str) else start
    end = Config.parse(end) if isinstance(end, str) else end
    trace = []
    try:
        fin = run(m, start.copy(), lambda c: not c.steps.is_zero() and same_config(c, end), max_moves=max_moves, cross=cross, trace=trace)
    except (TouchContext, NeedSplit, Halted, RuntimeError) as e:
        raise ProofError(f"{name}: {type(e).__name__}: {e}")
    if nsteps is not None and lin(nsteps) != fin.steps:
        raise ProofError(f"{name}: the run takes {fin.steps} steps, not {nsteps}")
    vs = sorted(start.vars() | end.vars())
    ctxs = []
    for x in start.contexts() + end.contexts():
        if x not in ctxs:
            ctxs.append(x)
    binders = (f" ({' '.join(vs)} : Nat)" if vs else "") + (f" ({' '.join(ctxs)} : Tape)" if ctxs else "")
    lines = []
    if doc:
        lines.append(f"/-- {doc} -/")
    lines.append(f"theorem {name}{binders} :")
    lines.append(f"    steps ({fin.steps.lean()}) {cfg_term(start)} = some {cfg_term(fin)} := by")
    hs, counts = [], []
    for i, seg in enumerate(_segments(trace)):
        if seg[0] == "steps":
            _, a, b, n = seg
            lines.append(f"  have h{i} : steps {n} {cfg_term(a)} = some {cfg_term(b)} := rfl")
            counts.append(str(n))
        else:
            _, a, b, x = seg
            if x.d == "r":
                u_, w_, v_ = tuple(reversed(x.u)), x.w, tuple(reversed(x.v))
                lines.append(f"  have c{i} : ∀ L R : Tape, steps {x.s} ⟨app {_word(u_)} L, app {_word(w_)} R, "
                             f".{STATES[a.state]}⟩ = some ⟨app {_word(u_)} (app {_word(v_)} L), R, "
                             f".{STATES[a.state]}⟩ := fun _ _ => rfl")
                Lt = left_term(a.left[:len(a.left) - len(x.u)])
                Rt = right_term(a.right[1:])
                lines.append(f"  have h{i} : steps (({x.k.lean()}) * {x.s}) {cfg_term(a)} = some {cfg_term(b)} :=")
                lines.append(f"    cross_r trans c{i} ({x.k.lean()}) ({Lt}) ({Rt})")
            else:
                w_ = tuple(reversed(x.w))
                lines.append(f"  have c{i} : ∀ L R : Tape, steps {x.s} ⟨app {_word(w_)} L, app {_word(x.u)} R, "
                             f".{STATES[a.state]}⟩ = some ⟨L, app {_word(x.u)} (app {_word(x.v)} R), "
                             f".{STATES[a.state]}⟩ := fun _ _ => rfl")
                Lt = left_term(a.left[:-1])
                Rt = right_term(a.right[len(x.u):])
                lines.append(f"  have h{i} : steps (({x.k.lean()}) * {x.s}) {cfg_term(a)} = some {cfg_term(b)} :=")
                lines.append(f"    cross_l trans c{i} ({x.k.lean()}) ({Lt}) ({Rt})")
            counts.append(f"({x.k.lean()}) * {x.s}")
        hs.append(f"h{i}")
    if not hs:
        raise ProofError(f"{name}: the run is empty")
    total = counts[-1]
    for c in reversed(counts[:-1]):
        total = f"{c} + ({total})"
    chain = hs[-1]
    for h in reversed(hs[:-1]):
        chain = f"steps_seq trans {h} ({chain})"
    lines.append(f"  exact steps_congr trans (a := {total}) (by omega) ({chain})")
    return "\n".join(lines) + "\n", fin


def rules_file(machine_module, ns, theorems, doc):
    """A Lean file of rules: `theorems` a list of lean texts from `prove`."""
    head = f"import {machine_module}\n\n/-! {doc} -/\n\nnamespace {ns}\n\nopen TM\n\n"
    return head + "\n".join(theorems) + f"\nend {ns}\n"
