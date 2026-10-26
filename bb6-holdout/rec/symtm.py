"""Symbolic simulation of 1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LD1RE.

A configuration is  left-tokens  STATE>  right-tokens : the head reads the first right token.
Tokens are literal cells 0/1, Rep(word, n) for word repeated n times (n a linear expression in
nonnegative integer variables), or Ctx(name): an unknown stretch of tape the proof may not look at.

Only three facts are used besides single machine steps, the cycle lemmas (proved in prove_cycles):
  PASS   E> (01)^k        ->  (01)^k E>         in 2k steps
  SHIFT  A> (01)^k        ->  (10)^k A>         in 2k steps
  CARRY  (10)^k A> 1 1    ->  A> 1 1 (10)^k     in 4k steps
"""
from dataclasses import dataclass

MACHINE = "1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LD1RE"
TR = {}
for s, g in zip("ABCDEF", MACHINE.split("_")):
    for y in (0, 1):
        x = g[3 * y:3 * y + 3]
        TR[s, y] = None if x == "---" else (int(x[0]), 1 if x[1] == "R" else -1, x[2])


# ---------------------------------------------------------------- linear expressions
class Lin:
    __slots__ = ("c", "k")
    def __init__(self, k=0, c=None):
        if isinstance(k, Lin):
            self.c, self.k = dict(k.c), k.k; return
        if isinstance(k, str):
            self.c, self.k = {k: 1}, 0; return
        self.c = dict(c or {}); self.k = k
        self.c = {v: a for v, a in self.c.items() if a}
    def __add__(self, o):
        o = lin(o); c = dict(self.c)
        for v, a in o.c.items(): c[v] = c.get(v, 0) + a
        return Lin(self.k + o.k, c)
    __radd__ = __add__
    def __sub__(self, o): return self + (-1) * lin(o)
    def __rmul__(self, a): return Lin(a * self.k, {v: a * b for v, b in self.c.items()})
    def __mul__(self, a): return a * self
    def surely_ge(self, n): return all(a >= 0 for a in self.c.values()) and self.k >= n
    def is_zero(self): return not self.c and self.k == 0
    def is_const(self): return not self.c
    def subs(self, env):
        return self.k + sum(a * env[v] for v, a in self.c.items())
    def __eq__(self, o): o = lin(o); return self.k == o.k and self.c == o.c
    def __hash__(self): return hash((self.k, tuple(sorted(self.c.items()))))
    def __repr__(self):
        parts = [(f"{a}*{v}" if a != 1 else v) for v, a in sorted(self.c.items())]
        if self.k or not parts: parts.append(str(self.k))
        return "+".join(parts).replace("+-", "-")

def lin(x): return x if isinstance(x, Lin) else Lin(x)


@dataclass(frozen=True)
class Rep:
    word: tuple
    n: Lin
    def __repr__(self): return f"({''.join(map(str, self.word))})^{self.n}"

@dataclass(frozen=True)
class Ctx:
    name: str
    def __repr__(self): return self.name

@dataclass(frozen=True)
class Blank:
    """The blank tape: infinitely many 0s."""
    def __repr__(self): return "0^inf"

class TouchContext(Exception): pass
class NeedSplit(Exception): pass
class Halted(Exception): pass


def tokens(s, **reps):
    """Parse a tape string like 'L 1 0 0 (10)^m 1 1 R': names in reps give exponents, capital names are contexts."""
    out = []
    for part in s.split():
        if part.startswith("("):
            w, e = part[1:].split(")^")
            n = reps[e] if e in reps else (Lin(int(e)) if e.lstrip("-").isdigit() else parse_lin(e))
            out.append(Rep(tuple(int(ch) for ch in w), lin(n)))
        elif part.isdigit():
            out.extend(int(ch) for ch in part)
        else:
            out.append(Ctx(part))
    return out

def parse_lin(e):
    total = Lin(0); sign = 1; cur = ""
    for ch in e + "+":
        if ch in "+-":
            if cur:
                total = total + sign * (Lin(int(cur)) if cur.isdigit() else Lin(cur))
            sign = 1 if ch == "+" else -1; cur = ""
        else:
            cur += ch
    return total


# ---------------------------------------------------------------- configurations
class Config:
    def __init__(self, left, state, right, steps=0):
        self.left, self.state, self.right = list(left), state, list(right)
        self.steps = lin(steps); self.hist = []; self.lemmas = []
    def copy(self):
        c = Config(self.left, self.state, self.right, self.steps); c.hist = list(self.hist); c.lemmas = list(self.lemmas); return c
    def __repr__(self):
        return " ".join(map(str, self.left)) + f" {self.state}> " + " ".join(map(str, self.right))


def _unroll_front(seq):
    """Make seq[0] a literal (expanding a repeat), raising if impossible."""
    while seq and isinstance(seq[0], Rep):
        r = seq[0]
        if r.n.is_zero(): seq.pop(0); continue
        if not r.n.surely_ge(1): raise NeedSplit(r)
        rest = [Rep(r.word, r.n - 1)] if not (r.n - 1).is_zero() else []
        seq[0:1] = list(r.word) + rest
    if not seq: raise TouchContext("end of tape")
    if isinstance(seq[0], Blank): seq.insert(0, 0)
    if isinstance(seq[0], Ctx): raise TouchContext(seq[0])
    return seq[0]

def _unroll_back(seq):
    while seq and isinstance(seq[-1], Rep):
        r = seq[-1]
        if r.n.is_zero(): seq.pop(); continue
        if not r.n.surely_ge(1): raise NeedSplit(r)
        rest = [Rep(r.word, r.n - 1)] if not (r.n - 1).is_zero() else []
        seq[-1:] = rest + list(r.word)
    if not seq: raise TouchContext("end of tape")
    if isinstance(seq[-1], Blank): seq.append(0)
    return seq[-1]


def count_pairs(seq, pair, from_back=False):
    """Count complete copies of the 2-cell word `pair` at the near end of seq (front, or back read backwards).
    Returns (count, rest) where rest is seq with those copies removed."""
    s = list(reversed(seq)) if from_back else list(seq)
    rv = (lambda w: tuple(reversed(w))) if from_back else (lambda w: w)
    count = Lin(0); pos = 0; pending = None; i = 0
    while i < len(s):
        t = s[i]
        if isinstance(t, int):
            if t == pair[pos]:
                if pos == 0: pending = t; pos = 1
                else: count = count + 1; pos = 0; pending = None
                i += 1; continue
            break
        if isinstance(t, Rep) and len(t.word) == 2:
            w = rv(t.word)
            if pos == 0 and w == pair: count = count + t.n; i += 1; continue
            if pos == 1 and w == (pair[1], pair[0]): count = count + t.n; i += 1; continue
        break
    rest = ([pending] if pos == 1 else []) + s[i:]
    if from_back: rest = list(reversed(rest))
    return count, rest


def step(cfg):
    """One machine step (expanding repeats as needed)."""
    sym = _unroll_front(cfg.right)
    tr = TR[cfg.state, sym]
    key = f"{cfg.state}{sym}"
    if tr is None: raise Halted(key)
    w, d, n = tr
    cfg.right[0] = w
    if d == 1:
        cfg.left.append(cfg.right.pop(0))
    else:
        if not cfg.left: raise TouchContext("end of tape")
        if isinstance(cfg.left[-1], (Rep, Blank)): _unroll_back(cfg.left)
        cfg.right.insert(0, cfg.left.pop())
    cfg.state = n; cfg.steps = cfg.steps + 1; cfg.hist.append(key)


def try_lemma(cfg, use=("PASS", "SHIFT", "CARRY")):
    if cfg.state == "E" and "PASS" in use:
        k, rest = count_pairs(cfg.right, (0, 1))
        if not k.is_zero():
            cfg.left.append(Rep((0, 1), k)); cfg.right = rest; cfg.steps = cfg.steps + 2 * k
            cfg.lemmas.append(("PASS", k)); cfg.hist.append(f"[E0 F1]x{k}"); return True
    if cfg.state == "A" and "SHIFT" in use:
        k, rest = count_pairs(cfg.right, (0, 1))
        if not k.is_zero():
            cfg.left.append(Rep((1, 0), k)); cfg.right = rest; cfg.steps = cfg.steps + 2 * k
            cfg.lemmas.append(("SHIFT", k)); cfg.hist.append(f"[A0 B1]x{k}"); return True
    if cfg.state == "A" and "CARRY" in use:
        r = list(cfg.right)
        try:
            a = _unroll_front(r); b = None
            if a == 1:
                tail = r[1:]; b = _unroll_front(tail); r = [1] + tail
        except (TouchContext, NeedSplit):
            return False
        if a == 1 and b == 1:
            k, rest = count_pairs(cfg.left, (0, 1), from_back=True)
            if not k.is_zero():
                cfg.left = rest; cfg.right = [1, 1, Rep((1, 0), k)] + r[2:]
                cfg.steps = cfg.steps + 4 * k; cfg.lemmas.append(("CARRY", k)); cfg.hist.append(f"[A1 E1 B0 C0]x{k}")
                return True
    return False


def run(cfg, stop, max_iter=100000, use=("PASS", "SHIFT", "CARRY")):
    """Advance until stop(cfg) is true. Lemmas first, then single steps."""
    for _ in range(max_iter):
        if stop(cfg): return cfg
        if not try_lemma(cfg, use): step(cfg)
    raise RuntimeError("no stop")


# ---------------------------------------------------------------- canonical form (for comparing tapes)
def canon(seq):
    out = []
    for t in seq:
        if isinstance(t, Rep):
            const = t.n.k; var = Lin(0, t.n.c)
            if var.is_zero():
                out.extend(list(t.word) * const); continue
            if const < 0: raise ValueError("negative constant in exponent")
            out.append(Rep(t.word, var)); out.extend(list(t.word) * const)
        else:
            out.append(t)
    changed = True
    while changed:                       # push literals rightward through symbolic repeats: x(yx)^v -> (xy)^v x
        changed = False
        for i in range(1, len(out)):
            t = out[i]
            if isinstance(t, Rep) and isinstance(out[i - 1], int) and out[i - 1] == t.word[-1]:
                x = out[i - 1]; nw = (t.word[-1],) + t.word[:-1]
                out[i - 1:i + 1] = [Rep(nw, t.n), x]; changed = True; break
            if isinstance(t, Rep) and isinstance(out[i - 1], Rep) and out[i - 1].word == t.word:
                out[i - 1:i + 1] = [Rep(t.word, out[i - 1].n + t.n)]; changed = True; break
    while len(out) >= 2 and out[-1] == Blank() and out[-2] == 0: out.pop(-2)   # 0 next to blank tape is blank tape
    while len(out) >= 2 and out[0] == Blank() and out[1] == 0: out.pop(1)
    return out

def same_config(c1, c2):
    a = canon(c1.left + [Ctx("HEAD:" + c1.state)] + c1.right)
    b = canon(c2.left + [Ctx("HEAD:" + c2.state)] + c2.right)
    return a == b


# ---------------------------------------------------------------- the cycle lemmas, proved
def prove_cycles():
    """Each lemma: one cycle maps the word to its image with the head crossing it, never touching the
    surrounding tape (contexts L, R). Induction on k then gives the lemma for every k >= 0."""
    results = []
    for name, start, end, nsteps in [
        ("PASS", Config(tokens("L"), "E", tokens("0 1 R")), Config(tokens("L 0 1"), "E", tokens("R")), 2),
        ("SHIFT", Config(tokens("L"), "A", tokens("0 1 R")), Config(tokens("L 1 0"), "A", tokens("R")), 2),
        ("CARRY", Config(tokens("L 1 0"), "A", tokens("1 1 R")), Config(tokens("L"), "A", tokens("1 1 1 0 R")), 4),
    ]:
        c = start.copy()
        for _ in range(nsteps): step(c)          # raises TouchContext if the cycle looked outside the word
        ok = same_config(c, end) and c.steps == nsteps
        results.append((name, ok, " ".join(c.hist)))
    return results

if __name__ == "__main__":
    for r in prove_cycles(): print(r)
