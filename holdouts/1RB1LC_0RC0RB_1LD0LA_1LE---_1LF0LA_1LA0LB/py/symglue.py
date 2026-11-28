"""Local passes stated in the counters' own block structure, with the re-bracketing proved.

`bbtools.symtm.prove` proves a run between two configurations and states the end the way the run writes it.  The
step lemmas of the walk need each pass stated with the blocks of the counter encoding (`(00001)^(2t+3)` for 2t + 3
digits 1 of U, `(01)^(5t+7)` for digits of V), while the run crosses the tape in larger blocks (`(0000100001)^(t+1)`)
and ends rotated.  `prove_enc` regroups the start for the run, runs symtm, and proves in Lean that the stated start
and end equal the run's (both sides brought to the normal form of `symtm.canon`, every rewrite a `TM.rep_rotate`,
`TM.rep_add` or `rep_mul_word` instance).  The theorem it returns is stated exactly as given.
"""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "py"))
from bbtools import symtm as S
from bbtools.symtm import Rep, Ctx, Lin, lin, Config, left_term, right_term, _word, B

STATES = S.STATES


def term(side, T):
    return left_term(T) if side == "l" else right_term(T)


class Eqs:
    """A chain of local rewrites of one side's token list, each with its Lean equation."""

    def __init__(self, side, T):
        self.side, self.T, self.eqs = side, list(T), []

    def replace(self, a, b, new, proof):
        """tokens T[a:b] (reading order) become `new`; proof: Lean term or tactic block for the local equation."""
        T = self.T
        if self.side == "l":
            lhs, rhs = left_term(T[:b]), left_term(T[:a] + list(new))
        else:
            lhs, rhs = right_term(T[a:]), right_term(list(new) + T[b:])
        self.eqs.append(f"show {lhs} = {rhs} from {proof}")
        self.T = T[:a] + list(new) + T[b:]

    def rest(self, a, b):
        return left_term(self.T[:a]) if self.side == "l" else right_term(self.T[b:])


def rw_word(side, w):
    """the Lean list of a word as the term builder writes it on this side"""
    return _word(tuple(reversed(w)) if side == "l" else tuple(w))


def expand(E, i):
    """Rep(w, v + c) at i (c >= 0 constant) -> Rep(w, v) w^c (w^c only when v = 0)."""
    T, side = E.T, E.side
    r = T[i]
    c, v = r.n.k, Lin(0, r.n.c)
    W = rw_word(side, r.word)
    if v.is_zero():
        E.replace(i, i + 1, list(r.word) * c, "rfl")
        return
    new = [Rep(r.word, v)] + list(r.word) * c
    if side == "r":
        E.replace(i, i + 1, new, f"(by rw [rep_add]; rfl)")
    else:
        E.replace(i, i + 1, new, f"(by rw [show {r.n.lean()} = {c} + ({v.lean()}) from by omega, rep_add]; rfl)")


def canon_eqs(side, T):
    """symtm.canon with every rewrite recorded (no blank tape handling: contexts at the ends)."""
    E = Eqs(side, T)
    i = 0
    while i < len(E.T):
        t = E.T[i]
        if isinstance(t, Rep):
            if t.n.k < 0:
                raise ValueError("negative constant in a count")
            if t.n.k > 0 or Lin(0, t.n.c).is_zero():
                expand(E, i)
                continue
        i += 1
    changed = True
    while changed:
        changed = False
        out = E.T
        for i in range(len(out)):
            t = out[i]
            if not isinstance(t, Rep):
                continue
            L = len(t.word)
            pre = out[max(0, i - L):i]
            n = t.n.lean()
            if len(pre) == L and all(isinstance(x, int) for x in pre) and tuple(pre) == t.word:
                W = rw_word(side, t.word)
                rest = E.rest(i - L, i + 1)
                if side == "r":
                    pf = f"rep_rotate ({n}) {W} {W} {W} rfl ({rest})"
                else:
                    pf = f"(rep_rotate ({n}) {W} {W} {W} rfl ({rest})).symm"
                E.replace(i - L, i + 1, [t] + list(t.word), pf)
                changed = True
                break
            if L > 1 and i >= 1 and isinstance(out[i - 1], int) and out[i - 1] == t.word[-1]:
                x = out[i - 1]
                w2 = (x,) + t.word[:-1]
                rest = E.rest(i - 1, i + 1)
                if side == "r":
                    pf = f"rep_rotate ({n}) [{B[x]}] {_word(t.word)} {_word(w2)} rfl ({rest})"
                else:
                    # reading x (y x)^n: left term rep n (x :: rev y) (cons x R) = cons x (rep n (rev y ++ [x]) R)
                    pf = (f"(rep_rotate ({n}) [{B[x]}] {_word(tuple(reversed(w2)))} {_word(tuple(reversed(t.word)))} rfl "
                          f"({rest})).symm")
                E.replace(i - 1, i + 1, [Rep(w2, t.n), x], pf)
                changed = True
                break
            if i >= 1 and isinstance(out[i - 1], Rep) and out[i - 1].word == t.word:
                a, b = out[i - 1].n, t.n
                c = (a + b).lean()
                if side == "r":
                    pf = f"(by rw [← rep_add, show {a.lean()} + ({b.lean()}) = {c} from by omega])"
                else:
                    pf = f"(by rw [← rep_add, show {b.lean()} + ({a.lean()}) = {c} from by omega])"
                E.replace(i - 1, i + 1, [Rep(t.word, a + b)], pf)
                changed = True
                break
    return E


def regroup_eqs(side, T, k=None):
    """Every repeat Rep(w, a v + b) with a > 1 (one variable) becomes Rep(w^a, v + b // a) w^(b % a) (k: the
    multiplicity, default a), so that symtm can cross it in larger blocks."""
    E = Eqs(side, T)
    i = 0
    while i < len(E.T):
        t = E.T[i]
        if isinstance(t, Rep) and len(t.n.c) == 1:
            (v, a), = t.n.c.items()
            kk = k or a
            if kk > 1 and a % kk == 0:
                b = t.n.k
                q, d = b // kk, b % kk
                inner = Lin(0, {v: a // kk}) + q
                W2 = t.word * kk
                new = [Rep(W2, inner)] + list(t.word) * d
                il = inner.lean()
                if side == "r":
                    pf = f"(by rw [show {t.n.lean()} = {kk} * ({il}) + {d} from by omega, rep_add, rep_mul_word]; rfl)"
                else:
                    pf = f"(by rw [show {t.n.lean()} = {d} + {kk} * ({il}) from by omega, rep_add, rep_mul_word]; rfl)"
                E.replace(i, i + 1, new, pf)
        i += 1
    return E


def conv(eqs):
    if not eqs:
        return "rfl"
    return "by\n    conv =>\n      lhs\n      rw [" + ",\n        ".join(eqs) + "]"


def cfg_of(left, state, right):
    return f"⟨{left_term(left)}, {right_term(right)}, .{STATES[state]}⟩"


def prove_enc(m, name, start, end, doc=None, k=None, **kw):
    """Theorem `name`: from `start` the machine reaches `end` (strings or Configs, in the encoding's blocks), proved
    by symtm on regrouped blocks and re-bracketing.  Returns (lean text of the raw lemma and the theorem, steps)."""
    st = Config.parse(start) if isinstance(start, str) else start
    en = Config.parse(end) if isinstance(end, str) else end
    gl, gr = regroup_eqs("l", st.left, k), regroup_eqs("r", st.right, k)
    el, er = regroup_eqs("l", en.left, k), regroup_eqs("r", en.right, k)
    s2 = Config(gl.T, st.state, gr.T)
    e2 = Config(el.T, en.state, er.T)
    raw, fin = S.prove(m, name + "_raw", s2, e2, rotate=True, **kw)
    # end: E -> regrouped -> canon, and fin -> canon
    cl1, cr1 = canon_eqs("l", el.T), canon_eqs("r", er.T)
    cl2, cr2 = canon_eqs("l", fin.left), canon_eqs("r", fin.right)
    assert cl1.T == cl2.T and cr1.T == cr2.T, (cl1.T, cl2.T, cr1.T, cr2.T)
    vs = sorted(st.vars() | en.vars())
    ctxs = []
    for x in st.contexts() + en.contexts():
        if x not in ctxs:
            ctxs.append(x)
    binders = (f" ({' '.join(vs)} : Nat)" if vs else "") + (f" ({' '.join(ctxs)} : Tape)" if ctxs else "")
    args = " ".join(vs + ctxs)
    N = fin.steps.lean()
    L = []
    if doc:
        L.append(f"/-- {doc} -/")
    L.append(f"theorem {name}{binders} :")
    L.append(f"    steps ({N}) {cfg_of(st.left, st.state, st.right)} = some {cfg_of(en.left, en.state, en.right)} := by")
    L.append(f"  have h := {name}_raw {args}")
    L.append(f"  have a1 : {left_term(st.left)} = {left_term(s2.left)} := {conv(gl.eqs)}")
    L.append(f"  have a2 : {right_term(st.right)} = {right_term(s2.right)} := {conv(gr.eqs)}")
    L.append(f"  have b1 : {left_term(en.left)} = {left_term(cl1.T)} := {conv(el.eqs + cl1.eqs)}")
    L.append(f"  have b2 : {right_term(en.right)} = {right_term(cr1.T)} := {conv(er.eqs + cr1.eqs)}")
    L.append(f"  have c1 : {left_term(fin.left)} = {left_term(cl2.T)} := {conv(cl2.eqs)}")
    L.append(f"  have c2 : {right_term(fin.right)} = {right_term(cr2.T)} := {conv(cr2.eqs)}")
    L.append(f"  rw [a1, a2, b1, b2]")
    L.append(f"  rw [c1, c2] at h")
    L.append(f"  exact h")
    return raw + "\n" + "\n".join(L) + "\n", fin.steps
