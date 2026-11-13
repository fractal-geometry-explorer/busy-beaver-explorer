"""Chaining symbolic rules into Lean proofs of whole macro steps (shared by the G01 second-pass machines).

Built on `symtm2.py` (a copy of `tools/py/bbtools/symtm.py` that also crosses repeats with literal cells between
the head and the repeat).  Three things:

* `tape_eq(c1, c2)`: a Lean proof that two symbolic configurations that are equal as tapes (same canonical form)
  are equal as Lean terms.  Both sides are rewritten to a normal form (constant repeats written out, literal copies
  folded into the neighbouring repeat, literals rotated to the far side of a repeat, trailing 0s before blank tape
  dropped), each rewrite a closed equation proved by a lemma of `Chain.lean`.
* `Loop`: a round rule `P(x+1, i) -> P(x, i+1)` proved by `symtm2.prove`, and its iteration for any number of
  rounds (`TM.iter`), with the step count in closed form (`TM.iterT_lin`).
* `Case`: a run from a start configuration through segments (proved by `symtm2.prove`) and loops to an end
  configuration, written as one Lean theorem with an explicit step count.

Configurations are strings as for `symtm.Config.parse`, e.g. '0^inf (10)^3*i+3 E> (10)^2*x+4 1 0^inf'.
Lean is the judge: every generated statement is checked there.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import symtm2 as S  # noqa: E402
from symtm2 import Lin, Rep, Ctx, Blank, Config  # noqa: E402

B = {0: "false", 1: "true"}


def W(w):
    return "[" + ", ".join(B[x] for x in w) + "]"


# ------------------------------------------------------------------ linear substitution
def lsub(L, env):
    r = Lin(L.k)
    for v, a in L.c.items():
        r = r + a * (S.lin(env[v]) if v in env else Lin(v))
    return r


def parse_env(env):
    return {k: (S.parse_lin(v) if isinstance(v, str) else S.lin(v)) for k, v in env.items()}


def csub(cfg, env):
    """the configuration with variables substituted (env: name -> Lin | int | str) and contexts replaced
    (env: context name -> token string, e.g. L='0^inf (10)^m 0')"""
    ctx = {k: v for k, v in env.items() if isinstance(v, str) and not _is_lin(v)}
    env = parse_env({k: v for k, v in env.items() if k not in ctx})
    def f(ts):
        out = []
        for t in ts:
            if isinstance(t, Rep):
                out.append(Rep(t.word, lsub(t.n, env)))
            elif isinstance(t, Ctx) and t.name in ctx:
                out.extend(f(S.tokens(ctx[t.name])))
            else:
                out.append(t)
        return out
    return Config(f(cfg.left), cfg.state, f(cfg.right), cfg.steps)


def _is_lin(v):
    try:
        S.parse_lin(v)
        return all(ch in "0123456789+-* abcdefghijklmnopqrstuvwxyz_" for ch in v) and "^" not in v and \
            not any(tok in v for tok in ("inf",))
    except Exception:
        return False


def ctx_term(tokens, side):
    """the Lean term of a context's tokens: side 'l' (tokens far to near) or 'r'"""
    ts = S.tokens(tokens)
    if side == "l":
        ts = [Rep(tuple(reversed(t.word)), t.n) if isinstance(t, Rep) else t for t in reversed(ts)]
    return sterm(ts)


def P(s, **env):
    c = Config.parse(s)
    return csub(c, env) if env else c


# ------------------------------------------------------------------ streams and their Lean terms
def streams(c):
    """(left stream, right stream), nearest cell first, words in stream order"""
    left = [Rep(tuple(reversed(t.word)), t.n) if isinstance(t, Rep) else t for t in reversed(c.left)]
    return left, list(c.right)


def sterm(st):
    acc = None
    for t in reversed(st):
        if isinstance(t, Ctx):
            acc = t.name
        elif isinstance(t, Blank):
            acc = "blank"
        elif isinstance(t, int):
            acc = f"cons {B[t]} ({acc})"
        else:
            acc = f"rep ({t.n.lean()}) {W(t.word)} ({acc})"
    return acc


def cterm(left, right, q):
    return f"(⟨{sterm(left)}, {sterm(right)}, .{S.STATES[q]}⟩ : Config)"


def is_zero_word(w):
    return all(x == 0 for x in w)


def root(w):
    """the primitive root of a word"""
    for p in range(1, len(w) + 1):
        if len(w) % p == 0 and w == w[:p] * (len(w) // p):
            return w[:p]


def hole_term(toks):
    return sterm(list(toks) + [Ctx("X")])


def norm_stream(st):
    """normal form of a stream and the list of Lean equations rewriting it there, in order (each `∀ X, ...` with X
    the untouched rest of the stream, or closed when the rest is blank tape)"""
    st = list(st)
    eqs = []
    while True:
        done = True
        for p in range(len(st)):
            t = st[p]
            rule = None        # (number of tokens replaced, replacement, proof with X)
            if isinstance(t, Rep) and t.n.is_zero():                        # rep 0 w X = X
                rule = (1, [], "rfl")
            elif isinstance(t, Rep) and root(t.word) != t.word:              # rep n (u^k) X = rep (k n) u X
                u = root(t.word)
                k = len(t.word) // len(u)
                rule = (1, [Rep(u, k * t.n)], f"rep_pw ({t.n.lean()}) {k} ({(k * t.n).lean()}) {W(u)} X (by omega)")
            elif isinstance(t, Rep) and t.n.is_const():                     # rep c w X = w...w X
                rule = (1, list(t.word) * t.n.k, "rfl")
            elif isinstance(t, Rep) and p + 1 < len(st) and isinstance(st[p + 1], Rep) and st[p + 1].word == t.word:
                u = st[p + 1]                                                 # rep a w (rep b w X) = rep (a+b) w X
                rule = (2, [Rep(t.word, t.n + u.n)],
                        f"rep_merge ({t.n.lean()}) ({u.n.lean()}) ({(t.n + u.n).lean()}) {W(t.word)} X (by omega)")
            elif (isinstance(t, Rep) and tuple(st[p + 1:p + 1 + len(t.word)]) == t.word
                  and all(isinstance(y, int) for y in st[p + 1:p + 1 + len(t.word)])):
                rule = (1 + len(t.word), [Rep(t.word, t.n + 1)], f"rep_app_comm ({t.n.lean()}) {W(t.word)} X")
            elif isinstance(t, int):
                q = p
                while q < len(st) and isinstance(st[q], int):
                    q += 1
                if q < len(st) and isinstance(st[q], Rep):
                    r = st[q]
                    lits = st[p:q]
                    if tuple(lits) == r.word:                                 # w (rep n w X) = rep (n+1) w X
                        rule = (q - p + 1, [Rep(r.word, r.n + 1)], "rfl")
                    elif len(lits) == 1 and r.word[-1] == t:                  # a (rep n (w' a) X) = rep n (a w') (a X)
                        w2 = (t,) + r.word[:-1]
                        rule = (2, [Rep(w2, r.n), t], f"rep_rotate ({r.n.lean()}) [{B[t]}] {W(r.word)} {W(w2)} rfl X")
            if rule is None and isinstance(st[-1], Blank) and p < len(st) - 1 and all(
                    (isinstance(y, int) and y == 0) or (isinstance(y, Rep) and is_zero_word(y.word)) for y in st[p:-1]):
                old, new = sterm(st[p:]), "blank"
                eqs.append(f"show {old} = blank from {zeros_proof(st[p:])}")
                st = st[:p] + [Blank()]
                done = False
                break
            if rule is None:
                continue
            k, rep_, pr = rule
            old, new = hole_term(st[p:p + k]), hole_term(rep_)
            if old != new:
                eqs.append(f"show ∀ X : Tape, {old} = {new} from fun X => {pr}")
            st = st[:p] + rep_ + st[p + k:]
            done = False
            break
        if done:
            return st, eqs


def zeros_proof(st):
    """proof that a stream of 0s and repeats of 0-words ending in blank tape is blank"""
    # rewrite from the far end: each cons false blank / rep n [0..] blank is blank
    return "by simp only [cons_false_blank, app_cons, app_nil, rep_zeros_blank]"


def tape_eq(c1, c2):
    """Lean proof (a tactic block) that cfg_term(c1) = cfg_term(c2), or raise if their normal forms differ"""
    l1, r1 = streams(c1)
    l2, r2 = streams(c2)
    if c1.state != c2.state:
        raise ValueError(f"states differ: {c1} / {c2}")
    nl1, e1 = norm_stream(l1)
    nr1, e2 = norm_stream(r1)
    nl2, e3 = norm_stream(l2)
    nr2, e4 = norm_stream(r2)
    if sterm(nl1) != sterm(nl2) or sterm(nr1) != sterm(nr2):
        raise ValueError(f"normal forms differ:\n  {c1}\n  {c2}\n  L {nl1} | {nl2}\n  R {nr1} | {nr2}")
    if lean_cfg(c1) == lean_cfg(c2):
        return "rfl"
    N = cterm(nl1, nr1, c1.state)
    def side(c, eqs):
        if not eqs:
            return "rfl"
        return f"(show {lean_cfg(c)} = {N} by rw [" + ", ".join(f"({e})" for e in eqs) + "])"
    a, b = side(c1, e1 + e2), side(c2, e3 + e4)
    if b == "rfl":
        return a
    if a == "rfl":
        return f"{b}.symm"
    return f"({a}).trans ({b}).symm"


def norm_same(c1, c2):
    """equal as tapes by the normal form of `norm_stream` (or by symtm's canonical form)"""
    if c1.state != c2.state:
        return False
    if S.same_config(c1, c2):
        return True
    l1, r1 = streams(c1)
    l2, r2 = streams(c2)
    return (sterm(norm_stream(l1)[0]) == sterm(norm_stream(l2)[0])
            and sterm(norm_stream(r1)[0]) == sterm(norm_stream(r2)[0]))


def lean_cfg(c):
    l, r = streams(c)
    return cterm(l, r, c.state)


# ------------------------------------------------------------------ rules, loops, cases
class Lib:
    """A collection of generated theorems for one machine."""

    def __init__(self, machine, ns, max_seg=40):
        self.M = machine
        self.ns = ns
        self.thms = []
        self.max_seg = max_seg
        self.names = set()

    def add(self, text):
        self.thms.append(text)

    def prove(self, name, start, end, doc=None):
        start = P(start) if isinstance(start, str) else start
        end = P(end) if isinstance(end, str) else end
        text, fin = S.prove(self.M, name, start, end, doc=doc, rotate=True, count_first=True, max_seg=self.max_seg,
                            same=norm_same)
        assert name not in self.names, name
        self.names.add(name)
        self.add(text)
        vs = sorted(start.vars() | end.vars())
        ctxs = []
        for x in start.contexts() + end.contexts():
            if x not in ctxs:
                ctxs.append(x)
        return fin, vs, ctxs


class Loop:
    """`P(x+1, i) -> P(x, i+1)` for a template P in the variables x, i and parameters; `name` (the iteration):
    ∀ params ctxs k x i, steps (k*A + B*(k*x + T) + C*(k*i + T)) P(x+k, i) = some P(x, i+k), T = k(k-1)/2."""

    def __init__(self, lib, name, template, doc=None):
        self.lib, self.name = lib, name
        self.P = Config.parse(template)
        start = csub(self.P, {"x": "x+1"})
        end = csub(self.P, {"i": "i+1"})
        fin, vs, ctxs = lib.prove(name + "_round", start, end, doc=f"One round of `{name}`.")
        cost = fin.steps
        self.B = cost.c.get("x", 0)
        self.C = cost.c.get("i", 0)
        self.A = Lin(cost.k, {v: a for v, a in cost.c.items() if v not in ("x", "i")})
        self.params = sorted((self.P.vars()) - {"x", "i"})
        self.ctxs = [x for x in self.P.contexts()]
        self.ctx_side = {t.name: "l" for t in self.P.left if isinstance(t, Ctx)}
        self.ctx_side.update({t.name: "r" for t in self.P.right if isinstance(t, Ctx)})
        Pl = lambda x, i: lean_cfg(csub(self.P, {"x": x, "i": i}))
        pb = (f" ({' '.join(self.params)} : Nat)" if self.params else "") + \
             (f" ({' '.join(self.ctxs)} : Tape)" if self.ctxs else "")
        F = f"(fun x i => {self.A.lean()} + {self.B} * x + {self.C} * i)"
        args = " ".join(f"({v} := {v})" for v in vs) + " " + " ".join(f"({c} := {c})" for c in ctxs)
        fx = lean_cfg(fin)
        eq = tape_eq(fin, end)
        lam = "fun x i => " + lean_cfg(self.P)
        txt = f"""/-- {doc or 'Iterating `' + name + '_round`.'} -/
theorem {name}{pb} : ∀ kk x i : Nat,
    steps (kk * ({self.A.lean()}) + {self.B} * (kk * x + kk * (kk - 1) / 2) + {self.C} * (kk * i + kk * (kk - 1) / 2))
      {lean_cfg(csub(self.P, {"x": "x+kk"}))} = some {lean_cfg(csub(self.P, {"i": "i+kk"}))} := by
  have hr : ∀ x i, steps ({F} x i) (({lam}) (x + 1) i) = some (({lam}) x (i + 1)) := by
    intro x i
    have h := {name}_round {args}
    have e : {fx} = {lean_cfg(end)} := {eq}
    rw [e] at h
    simp +arith only [] at h ⊢
    exact h
  intro kk x i
  have h := iter trans (P := {lam}) (f := {F}) hr kk x i
  rw [iterT_lin] at h
  simp +arith only [] at h ⊢
  exact h
"""
        lib.add(txt)

    def count(self, k, x, i, env):
        """the Lean step count string of k rounds from P(x+k, i), with parameters env"""
        A = lsub(self.A, parse_env(env)).lean()
        K, X, I = (S.lin(S.parse_lin(v) if isinstance(v, str) else v).lean() for v in (k, x, i))
        return (f"({K}) * ({A}) + {self.B} * (({K}) * ({X}) + ({K}) * (({K}) - 1) / 2) + "
                f"{self.C} * (({K}) * ({I}) + ({K}) * (({K}) - 1) / 2)")


class Case:
    """A run from `start` through segments and loops, as one theorem `name`."""

    def __init__(self, lib, name, start, doc=None):
        self.lib, self.name, self.doc = lib, name, doc
        self.start = P(start) if isinstance(start, str) else start
        self.cur = self.start
        self.pieces = []      # (lean have-expression, count string, start cfg, end cfg)
        self.nseg = 0

    def to(self, target):
        target = P(target) if isinstance(target, str) else target
        if lean_cfg(self.cur) == lean_cfg(target) or norm_same(self.cur, target):
            self.cur = target
            return self
        nm = f"{self.name}_s{self.nseg}"
        self.nseg += 1
        fin, vs, ctxs = self.lib.prove(nm, self.cur, target)
        args = " ".join(f"({v} := {v})" for v in vs) + " " + " ".join(f"({c} := {c})" for c in ctxs)
        self.pieces.append((f"{nm} {args}", fin.steps.lean(), self.cur, fin))
        self.cur = fin.copy()
        self.cur.steps = Lin(0)       # the next piece counts its own steps
        return self

    def regroup(self, target):
        """continue from `target`, the same tape written with other repeats (bridged by `tape_eq`)"""
        target = P(target) if isinstance(target, str) else target
        assert norm_same(self.cur, target), (self.cur, target)
        self.cur = target
        return self

    def loop(self, lp, k, x="0", i="0", **env):
        k_, x_, i_ = (S.parse_lin(str(v)) for v in (k, x, i))
        ctx = {c: env.pop(c) for c in lp.ctxs}
        env = parse_env(env)
        st = csub(lp.P, dict(env, x=x_ + k_, i=i_, **ctx))
        self.to(st)
        en = csub(lp.P, dict(env, x=x_, i=i_ + k_, **ctx))
        args = " ".join(f"({v} := {env[v].lean()})" for v in lp.params)
        args += " " + " ".join(f"({c} := ({ctx_term(ctx[c], lp.ctx_side[c])}))" for c in lp.ctxs)
        cnt = lp.count(k_, x_, i_, env)
        h = (f"by\n    have h := {lp.name} {args} ({k_.lean()}) ({x_.lean()}) ({i_.lean()})\n"
             f"    simp +arith only [] at h ⊢\n    exact h")
        h = (f"steps ({cnt}) {lean_cfg(st)} = some {lean_cfg(en)}", h)
        self.pieces.append((h, cnt, st, en))
        self.cur = en
        return self

    def emit(self, end, binders):
        """the theorem; `binders` e.g. '(m k : Nat)'"""
        end = P(end) if isinstance(end, str) else end
        self.to(end)
        lines = []
        total = None
        for _, c, _, _ in reversed(self.pieces):
            total = f"({c})" if total is None else f"({c}) + ({total})"
        self.total = total
        lines.append(f"/-- {self.doc or self.name} -/")
        lines.append(f"theorem {self.name} {binders} :")
        lines.append(f"    steps ({total}) {lean_cfg(self.start)} = some {lean_cfg(end)} := by")
        for j, (h, _, _, _) in enumerate(self.pieces):
            if isinstance(h, tuple):
                lines.append(f"  have h{j} : {h[0]} := {h[1]}")
            else:
                lines.append(f"  have h{j} := {h}")
        # chain from the back
        n = len(self.pieces)
        expr = None
        for j in reversed(range(n)):
            if expr is None:
                last_end = self.pieces[j][3]
                eq = tape_eq(last_end, end)
                expr = f"bridge_lr trans rfl h{j} ({eq})"
            else:
                eq = tape_eq(self.pieces[j][3], self.pieces[j + 1][2])
                expr = f"bridge trans h{j} ({eq}) ({expr})"
        eq0 = tape_eq(self.start, self.pieces[0][2])
        lines.append(f"  exact bridge_lr trans ({eq0}) ({expr}) rfl")
        self.lib.add("\n".join(lines) + "\n")
        return total


def lean_file(lib, imports, doc):
    head = "".join(f"import {m}\n" for m in imports)
    return head + f"\nset_option linter.unusedSimpArgs false\n\n/-! {doc} -/\n\nnamespace {lib.ns}\n\nopen TM\n\n" + "\n".join(lib.thms) + f"\nend {lib.ns}\n"


def tok_str(ts):
    """tokens back to a parse string"""
    out = []
    for t in ts:
        if isinstance(t, Rep):
            out.append(f"({''.join(map(str, t.word))})^{t.n}")
        elif isinstance(t, Blank):
            out.append("0^inf")
        elif isinstance(t, Ctx):
            out.append(t.name)
        else:
            out.append(str(t))
    return " ".join(out)


def run_until(machine, cfg, pred, max_moves=100000):
    """the first configuration of the symbolic run from cfg (after at least one step) with pred(c), or None"""
    m = S.Machine.parse(machine)
    c = cfg.copy()
    try:
        S.run(m, c, lambda c: not c.steps.is_zero() and pred(c), max_moves=max_moves, rotate=True)
        return c
    except (S.TouchContext, S.NeedSplit, S.Halted, RuntimeError):
        return None
