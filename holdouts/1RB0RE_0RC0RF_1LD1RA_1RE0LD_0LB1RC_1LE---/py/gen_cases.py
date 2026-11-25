"""Lean proofs of the frontier cases of py/sym_law.py, from the steps of the symbolic engine.

For each shape t and group value v it writes one theorem: from the frontier of shape t fed v (every value of the
family's parameters, every history with enough digits, every counter above the group) the machine reaches a
frontier of the next shape (or the moment where the transient ends).  The proof is the engine's case tree: each step
of the engine becomes one lemma of lean/FrontLib.lean, each case split of the engine a case split in Lean.

usage: python3 py/gen_cases.py [SHAPE-INDEX GROUP] > lean/Cases.lean
"""
import os, sys, copy
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sym_trace  # noqa: F401  (records the engine's steps)
import sym_engine as E
from sym_lin import Lin
from sym_law import FAM, frontier, name, explore, shape, infam


class Unsupported(Exception):
    pass


# ---- splits are recorded in the trace
_subst = E.St.subst


def subst(s, v, e):
    _subst(s, v, e)
    s.trace = s.trace + [("split", v, e)]


E.St.subst = subst


# ---- comparisons of two parameters: split by substitutions (each case a parameter in terms of the other) rather
# than by linear constraints, so that every entry stays a sum of parameters with nonnegative coefficients
import sym_lin
from math import gcd
_ge = sym_lin.ge


def ge2(e, c=0):
    try:
        return _ge(e, c)
    except sym_lin.Need as N_:
        if not (N_.cases and N_.cases[0][0] == "C"): raise
        e = sym_lin.L(e) - c
        pos = [v for v, x in e.c.items() if x > 0]; neg = [v for v, x in e.c.items() if x < 0]
        if not pos or not neg:   # all of one sign: split a parameter at 0
            v = sorted(e.c)[0]
            raise sym_lin.Need([(v, Lin(0)), (v, Lin.var(v) + 1)])
        if len(pos) != 1 or len(neg) != 1 or len(e.c) != 2: raise
        m, n = pos[0], neg[0]; a, b = e.c[m], -e.c[n]; L_ = a * b // gcd(a, b); k = e.k
        if a != L_: raise sym_lin.Need([(m, Lin.var(m) * (L_ // a) + r) for r in range(L_ // a)])
        if b != L_: raise sym_lin.Need([(n, Lin.var(n) * (L_ // b) + r) for r in range(L_ // b)])
        K = -(k // L_)   # e >= 0 iff m - n >= K
        M, Nn = Lin.var(m), Lin.var(n)
        if K >= 0: cs = [(m, Nn + K + M), (n, M + Nn)] + [(m, Nn + j) for j in range(1, K)]
        else: cs = [(m, Nn + M)] + [(n, M + j) for j in range(1, -K + 1)] + [(n, M + (1 - K) + Nn)]
        raise sym_lin.Need(cs)


sym_lin.ge = ge2; E.ge = ge2


# ---- loops: the same as sym_engine.try_loop, keeping the general turn for the proof
def try_loop(s, maxsteps=80):
    import sym_lin as lin_
    base, shape_ = E.lins(s)
    runs = [p for p, v in base if len(p) == 3 and p[2] == 2 and not v.isconst()]
    for tgt in runs:
        r = E.fresh("r"); R_ = Lin.var(r)
        t = s.copy(); E.setlin(t, tgt, 1 + R_); tb, _ = E.lins(t)
        lin_.CTX[:] = s.cons
        found = None
        for k in range(maxsteps):
            try: t.step()
            except (E.Need, E.Stop, E.Halt): break
            cur, sh = E.lins(t)
            if sh != shape_: continue
            d = {}; ok = True
            for (p, v0), (p2, v1) in zip(tb, cur):
                dd = v1 - v0
                if p == tgt:
                    if dd != Lin(-1): ok = False; break
                    continue
                if not dd.isconst(): ok = False; break
                if dd.k: d[p] = dd.k
            if ok: found = (k, d); break
        if not found: continue
        k, d = found
        j = E.fresh("j"); J_ = Lin.var(j)
        g = s.copy()
        for p, v0 in base:
            if p == tgt: E.setlin(g, p, 1 + R_)
            elif p in d: E.setlin(g, p, v0 + d[p] * J_)
        want, _ = E.lins(g)
        g2 = g.copy(); lin_.CTX[:] = s.cons
        try:
            for k2 in range(k + 1): g2.step()
        except (E.Need, E.Stop, E.Halt): continue
        got, sh2 = E.lins(g2)
        if sh2 != shape_: continue
        good = True
        for (p, v0), (p2, v1) in zip(want, got):
            exp = (R_ if p == tgt else (v0.subst(j, J_ + 1) if p in d else v0))
            if v1 != exp: good = False; break
        if not good: continue
        c = dict(base)[tgt]
        out = s.copy()
        for p, v0 in base:
            if p == tgt: E.setlin(out, p, Lin(0))
            elif p in d: E.setlin(out, p, v0 + d[p] * c)
        # the general state S(R, J): the run of R, the moving entries at v0 + d J
        S = g.copy(); E.setlin(S, tgt, R_)
        turn = g2.trace[len(g.trace):]
        out.trace = s.trace + [("loop", tgt, c, d, k + 1,
                                dict(R=r, J=j, S=S, pre=s.copy(), out=out.copy(), turn=turn))]
        return out
    return None


E.try_loop = try_loop


# ---- Lean terms
def lin(x):
    x = x if isinstance(x, Lin) else Lin(x)
    if any(c < 0 for c in x.c.values()) or (x.k < 0):
        raise Unsupported(f"negative coefficient {x}")
    parts = [(f"{c} * {v}" if c != 1 else v) for v, c in sorted(x.c.items()) if c]
    if x.k or not parts: parts.append(str(x.k))
    t = " + ".join(parts)
    return f"({t})" if (len(parts) > 1 or " " in t) else t


class Ctx:
    def __init__(s):
        s.H = {0: dict(q="q", digits=[], tail="D")}
        s.lines = []
        s.ind = 1
        s.cnt = 0
        s.defic = {"D": Lin(0)}   # tail -> d: its length is at least len(D) - d
        s.req = []           # lower bounds on len(D) that the proof uses
        s.auxs = []          # lemmas for the arithmetic, proved in a context of their own
        s.prefix = "aux"

    def aux_lemma(s, goal, proof, facts):
        import re
        txt = goal + " " + " ".join(f for _, f in facts)
        names = []
        for w in re.findall(r"[A-Za-z_][A-Za-z0-9_'.]*", txt):
            if "." in w or w in ("T", "sig") or w in names: continue
            names.append(w)
        binders = " ".join(f"({w} : {'List Nat' if (w.startswith('D') or w == 'gs') else 'Nat'})" for w in names)
        hyps = " ".join(f"({h} : {f})" for h, f in facts)
        nm = f"{s.prefix}_{len(s.auxs) + 1}"
        s.auxs.append(f"theorem {nm} {binders} {hyps} :\n    {goal} := by\n  {proof}\n")
        return f"{nm} {' '.join(names)} {' '.join(h for h, _ in facts)}"

    def fresh(s, p):
        s.cnt += 1; return f"{p}_{s.cnt}"

    def emit(s, t):
        s.lines.append("  " * s.ind + t)

    def copy(s):
        c = copy.copy(s); c.H = {k: dict(v, digits=list(v["digits"])) for k, v in s.H.items()}
        c.lines = s.lines; c.defic = dict(s.defic)
        return c


def dlist(digits, tail):
    return " :: ".join([lin(d) for d in digits] + [tail]) if digits else tail


def hist(ctx, i):
    h = ctx.H[i]
    return f"hist {h['q']} ({dlist(h['digits'], h['tail'])})"


def items(ctx, lst, open_last=False):
    """a list of engine items as a Lean list"""
    out = []
    for j, it in enumerate(lst):
        last = j == len(lst) - 1
        if it[0] == 'b':
            if open_last and last: out.append(("cons", f"(g + {lin(it[1])})")); out.append(("end", "gs"))
            else: out.append(("cons", lin(it[1])))
        elif it[0] == 'r':
            if open_last and last: raise Unsupported("run at the open end")
            out.append(("app", f"List.replicate {lin(it[2])} {lin(it[1])}"))
        elif it[0] == 'H':
            assert last; out.append(("end", f"({hist(ctx, it[1])})"))
        else: raise Unsupported(it)
    if not out or out[-1][0] != "end": out.append(("end", "[]"))
    t = out[-1][1]
    for kind, x in reversed(out[:-1]):
        t = f"{x} :: {t}" if kind == "cons" else (f"{x} ++ ({t})" if "++" in t else f"{x} ++ {t}")
    return t


PH = {"A": ".A", "C": ".C", "E": ".E"}


def ps_term(ctx, st):
    return f"⟨{items(ctx, st['lb'])}, {PH[st['ph']]}, {lin(st['k'])}, {items(ctx, st['us'], True)}⟩"


def mom_bs(ctx, st):
    return items(ctx, st['F'])


# ---- the history
def take_digit(ctx, i, name=None):
    """make sure H i has a known first digit (from its tail)"""
    h = ctx.H[i]
    if h["digits"]: return
    tail = h["tail"]
    nm = name or ctx.fresh("d")
    nt = ctx.fresh("D")
    ctx.emit(f"rcases {tail} with _ | ⟨{nm}, {nt}⟩")
    ctx.emit("· simp only [List.length_nil, List.length_cons] at *; omega")
    ctx.emit("try simp only [List.length_cons] at *")
    d = ctx.defic[tail]
    ctx.req.append(d + 1); ctx.defic[nt] = d + 1
    for k, v in ctx.H.items():
        if v["tail"] == tail:
            v["digits"] = v["digits"] + [Lin.var(nm)]; v["tail"] = nt


def apply_ops(ctx, ops, arith=False):
    for o in ops:
        op, src, dst = o[0], o[1], o[2]
        if op == "pull":
            x = o[3]
            take_digit(ctx, src, name=None)
            h = ctx.H[src]
            d = h["digits"][0]
            xv = lin(x)
            if x.isconst() or len(x.c) != 1 or list(x.c.values())[0] != 1 or x.k != 0:
                raise Unsupported(f"pull of {x}")
            if d != x:
                ctx.emit(f"generalize h_{xv} : {lin(d)} = {xv}")
                for hh in ctx.H.values():
                    hh["digits"] = [x if y == d else y for y in hh["digits"]]
            ctx.H[dst] = dict(q=h["q"], digits=h["digits"][1:], tail=h["tail"])
        elif op == "dbl":
            if arith: raise Unsupported("dbl in arith")
            z = o[3]
            take_digit(ctx, src)
            h = ctx.H[src]
            ctx.H[dst] = dict(q=h["q"], digits=[h['digits'][0] + z] + h["digits"][1:], tail=h["tail"])
        elif op == "push":
            raise Unsupported("push in a step")
        else:
            raise Unsupported(f"op {op}")


def digterm(lst, end="[]"):
    """front items (blocks 3d + 2 and runs of 2) as a Lean list of digits"""
    out = []
    for it in lst:
        if it[0] == 'b':
            dd, r = E.divmod_(it[1] - 2, 3)
            if r: raise Unsupported("not a digit")
            out.append(("cons", lin(dd)))
        elif it[0] == 'r':
            if it[1] != Lin(2): raise Unsupported("run not of digits")
            out.append(("app", f"List.replicate {lin(it[2])} 0"))
        else: raise Unsupported(it)
    t = end
    for kind, x in reversed(out):
        t = f"{x} :: {t}" if kind == "cons" else (f"{x} ++ ({t})" if "++" in t else f"{x} ++ {t}")
    return t


def reps(lst):
    return [lin(it[2]) for it in lst if it[0] == 'r']


TEQ = ("try simp only [T_append, T_cons, T_nil, sig_append, sig_cons, sig_nil, sig_rep0, List.cons_append, "
       "List.nil_append, List.replicate_zero, List.append_nil] at *")


def emit_arith(ctx, ev):
    _, kind, before, after, ops, ch = ev
    F, F2 = before['F'], after['F']
    if not F or F[-1][0] != 'H' or not F2 or F2[-1][0] != 'H': raise Unsupported("arith without history")
    src, dst = F[-1][1], F2[-1][1]
    l, us, l2, us2 = before['l'], before['us'], after['l'], after['us']
    # the history after
    adds = [o for o in ops if o[0] == "add"]
    dbls = [o for o in ops if o[0] == "dbl"]
    borrow = None
    if not ops:
        mode = "same"
    elif len(ops) == 1 and dbls:
        mode = "dbl"; z = dbls[0][3]
        take_digit(ctx, src)
    elif len(adds) + len(dbls) == len(ops) and len(adds) in (1, 2) and len(dbls) <= 1 and ops[-1][0] == (
            "dbl" if dbls else "add"):
        if len(adds) == 1:
            a, e = adds[0][3], adds[0][4]
            if a != -1: raise Unsupported("carry into history")
            borrow = (Lin(0), e)
        else:
            (a1, e1), (a2, e2) = (adds[0][3], adds[0][4]), (adds[1][3], adds[1][4])
            if (a1, a2) != (1, -1): raise Unsupported("adds")
            borrow = None if e1 == e2 else (e1, e2)
        mode = "same" if borrow is None else "borrow"
        if borrow is None and dbls:
            mode = "dbl"; z = dbls[0][3]
            take_digit(ctx, src)
    else:
        raise Unsupported(f"arith ops {[o[0] for o in ops]}")
    hs = ctx.H[src]
    Dsrc = dlist(hs["digits"], hs["tail"])
    qn = ctx.fresh("q")
    bs1 = items(ctx, F); usT = items(ctx, us, True); us1T = items(ctx, us[1:], True)
    if mode == "same":
        ctx.H[dst] = dict(q=qn, digits=list(hs["digits"]), tail=hs["tail"]); D2 = Dsrc
    elif mode == "dbl":
        ctx.H[dst] = dict(q=qn, digits=[hs['digits'][0] + z] + hs["digits"][1:], tail=hs["tail"])
        D2 = dlist(ctx.H[dst]["digits"], hs["tail"])
    else:
        e1, e = borrow
        if e1 == Lin(0) and borrow[0] is not None and len(adds) == 2:
            c, hc = "1", "Nat.one_le_two_pow"
        elif len(adds) == 1:
            c, hc = "0", "Nat.zero_le _"
        else:
            c, hc = f"(2 ^ {lin(e1)})", f"Nat.pow_le_pow_right (by omega) (show {lin(e1)} ≤ {lin(e)} by omega)"
        nD = ctx.fresh("D"); nT = ctx.fresh("hT"); nl = ctx.fresh("hl")
        dg = hs["digits"]
        if dg:
            rest = dlist(dg[1:], hs["tail"])
            ctx.emit(f"obtain ⟨{nD}, {nT}, {nl}⟩ := borrowD {lin(dg[0])} ({rest}) {c} {lin(e)} ({hc}) "
                     f"(by (try simp only [List.length_cons] at *); omega)")
            dr = ctx.defic[hs["tail"]] - (len(dg) - 1)          # len(rest) >= L - dr
            gap = e - dg[0]
            gap_pos = Lin(max(gap.k, 0), {w: x for w, x in gap.c.items() if x > 0})
            ctx.req.append(dr + gap_pos)
            ctx.defic[nD] = dr - 1 + gap_pos + 2
        else:
            ctx.emit(f"obtain ⟨{nD}, {nT}, {nl}⟩ := borrow ({Dsrc}) {c} {lin(e)} ({hc}) "
                     f"(by (try simp only [List.length_cons] at *); omega)")
            d = ctx.defic[hs["tail"]]
            ctx.req.append(d + e + 1); ctx.defic[nD] = d + e + 2
        ctx.emit(f"try simp only [List.length_cons] at {nl}")
        ctx.H[dst] = dict(q=qn, digits=[], tail=nD); D2 = nD
        fact = (nT, nD)
        if dbls:
            z = dbls[0][3]
            take_digit(ctx, dst)
            h2 = ctx.H[dst]
            fact = (nT, dlist(h2["digits"], h2["tail"]))
            h2["digits"] = [h2['digits'][0] + z] + h2["digits"][1:]
            D2 = dlist(h2["digits"], h2["tail"])
    # the kind of step
    Fd, Fd2 = digterm(F[:-1]), digterm(F2[:-1])
    A = f"T ({Fd2}) + 2 ^ sig ({Fd2}) * T ({D2})"
    B = f"T ({Fd}) + 2 ^ sig ({Fd}) * T ({Dsrc})"
    us2T = items(ctx, us2, True)
    teq = [TEQ] + [f"have := T_rep0 {c}" for c in reps(F[:-1]) + reps(F2[:-1])]
    q4, r4 = E.divmod_(l - 1, 4)
    if ch is None:
        if us[0][0] != 'b': raise Unsupported("chunks of a run")
        j, rr = E.divmod_(us[0][1], 4)
        N = f"(2 ^ ({lin(q4)} + {lin(j)}) - 2 ^ {lin(q4)})"
        goal = f"{A} + 2 ^ ({lin(q4)} + {lin(j)}) = {B} + 2 ^ {lin(q4)}"
        fin = f"have := Nat.pow_le_pow_right (show 0 < 2 by omega) (Nat.le_add_right {lin(q4)} {lin(j)}); omega"
        if len(us) == 1:   # the open gap: take its known chunks, the rest stays open
            u0, r0, us1T = f"(g + {lin(us[0][1])})", f"(g + {rr})", "gs"
        else:
            u0, r0 = lin(us[0][1]), str(rr)
        hy = (f"giter_j {lin(j)} {lin(q4)} {r0} {lin(l)} {lin(l2)} {u0} ({us1T}) "
              f"({us2T}) (by omega) (by omega) (by omega) rfl")
    elif ch[2] is None and r4 >= 1:
        N = "1"; goal = f"{A} + 1 = {B}"; fin = None; hy = "rfl"
    elif ch[2] is None:
        N = f"(2 ^ {lin(q4)})"; goal = f"{A} + 2 ^ {lin(q4)} = {B}"; fin = None
        y1 = l2 - 4 * q4
        hy = f"giter_pow {lin(q4)} {lin(l)} {lin(l2)} {lin(y1)} ({usT}) ({us2T}) rfl (by omega) (by omega)"
    else:
        N = f"(2 ^ {lin(q4)} - 1)"; goal = f"{A} + 2 ^ {lin(q4)} = {B} + 1"
        fin = f"have := @Nat.one_le_two_pow {lin(q4)}; omega"
        hy = f"giter_pm1 {lin(q4)} {lin(l)} ({usT}) ({us2T}) (by omega) rfl"
    proof = "; ".join(teq) + ("; (try simp only [Nat.pow_add, Nat.pow_zero, Nat.mul_one, Nat.one_mul] at *); "
                              "first | grind | (simp only [Nat.pow_mul'] at *; grind)")
    facts = []
    if mode == "borrow":
        facts.append((fact[0], f"T ({fact[1]}) + 2 ^ {lin(e)} = T ({Dsrc}) + {c}"))
    aux = ctx.aux_lemma(goal, proof, facts)
    hT = f"({aux})" if fin is None else f"(by have hs : {goal} := {aux}; {fin})"
    nr = ctx.fresh("hrc")
    bs2 = items(ctx, F2)
    ctx.emit(f"refine Lands.castl (a' := gcfg ({bs1}) {lin(l)} ({usT})) (by cfgeq) ?_")
    ctx.emit(f"obtain ⟨{qn}, {nr}⟩ := RC.arithG {N} {hs['q']} ({Fd}) ({Fd2}) ({Dsrc}) ({D2}) (bs := {bs1}) "
             f"(l := {lin(l)}) (us := {usT}) (l' := {lin(l2)}) (us' := {us2T}) (by bseq)")
    ctx.emit(f"  {hT}")
    ctx.emit(f"  ({hy})")
    ctx.emit(f"refine Lands.trans (RC.castbs (bs' := {bs2}) {nr} (by bseq)) ?_")
    ctx.emit(f"clear {nr}" + (f" {fact[0]}" if mode == "borrow" else ""))


def emit_step(ctx, ev):
    _, kind, before, after, ops, ch = ev
    if kind == "arith":
        return emit_arith(ctx, ev)
    apply_ops(ctx, ops)
    if kind == "ps":
        ctx.emit(f"refine Lands.trans (RC.pnext (s' := {ps_term(ctx, after)}) rfl) ?_")
    elif kind == "arun":
        q, r = E.divmod_(before['k'], 3)
        lb = items(ctx, before['lb']); us = items(ctx, before['us'], True)
        ctx.emit(f"refine Lands.trans (RC.arun ({lb}) ({us}) {lin(before['k'])} {lin(q)} {r} (by omega) (by omega) (by omega)) ?_")
    elif kind == "pdone":
        ctx.emit(f"refine Lands.trans (RC.pdone (bs := {mom_bs(ctx, after)}) (l := {lin(after['l'])}) "
                 f"(us := {items(ctx, after['us'], True)}) rfl) ?_")
    elif kind == "start":
        ctx.emit(f"refine Lands.trans (RC.start (s := {ps_term(ctx, after)}) rfl) ?_")
    else:
        raise Unsupported(kind)


# ---- the case tree
def tree(leaves, i=0):
    """leaves: list of (why, state); events at index i"""
    done = [l for l in leaves if len(l[1].trace) == i]
    if done:
        assert len(leaves) == 1, "a leaf is a prefix of another"
        return ("leaf",) + done[0]
    evs = [l[1].trace[i] for l in leaves]
    if all(e[0] == "step" for e in evs):
        return ("step", evs[0], tree(leaves, i + 1))
    if all(e[0] == "split" for e in evs):
        groups = []
        for l, e in zip(leaves, evs):
            key = (e[1], repr(e[2]))
            for g in groups:
                if g[0] == key: g[2].append(l); break
            else: groups.append((key, e, [l]))
        return ("split", [(e[1], e[2], tree(ls, i + 1)) for key, e, ls in groups])
    if all(e[0] == "loop" for e in evs):
        return ("loop", evs[0], tree(leaves, i + 1))
    raise Unsupported(f"mixed events {[e[0] for e in evs]}")


def snap_cfg(ctx, sn):
    if sn["mode"] == "ps":
        return f"PS.cfg {ps_term(ctx, sn)}"
    return f"gcfg ({items(ctx, sn['F'])}) {lin(sn['l'])} ({items(ctx, sn['us'], True)})"


def cast_to(ctx, node):
    """after a substitution: bring the goal to the engine's form of the next state"""
    if node[0] == "step": t = snap_cfg(ctx, node[1][2])
    elif node[0] == "loop": t = st_cfg(ctx, node[1][5]["pre"])
    else: return
    ctx.emit(f"refine Lands.castl (a' := {t}) (by cfgeq) ?_")


def emit_split(ctx, alts, emit_node):
    v = alts[0][0]
    if v == "C":
        e = alts[0][1]
        pos = Lin(e.k if e.k > 0 else 0, {x: c for x, c in e.c.items() if c > 0})
        neg = Lin(-e.k if e.k < 0 else 0, {x: -c for x, c in e.c.items() if c < 0})
        hn = ctx.fresh("hc")
        ctx.emit(f"by_cases {hn} : {lin(neg)} ≤ {lin(pos)}")
        for j, (vv, ee, node) in enumerate(alts):
            ctx.emit("·"); c2 = ctx.copy(); c2.ind += 1
            emit_node(c2, node)
        raise Unsupported("constraint split")
    exs = [e for _, e, _ in alts]
    same = all(a[0] == v for a in alts)
    if same and len(exs) == 2 and set(map(repr, exs)) == {repr(Lin(0)), repr(Lin.var(v) + 1)}:
        ctx.emit(f"rcases {v} with _ | {v}")
        for (vv, ee, node) in sorted(alts, key=lambda a: a[1] != Lin(0)):
            ctx.emit("·"); c2 = ctx.copy(); c2.ind += 1
            cast_to(c2, node)
            c2.defic = {k: x.subst(v, ee) for k, x in c2.defic.items()}
            emit_node(c2, node)
        return
    q = len(exs)
    alts = sorted(alts, key=lambda a: a[1].k)
    exs = [e for _, e, _ in alts]
    if same and all(e == Lin.var(v) * q + r for r, e in enumerate(exs)):
        hn = ctx.fresh("hr")
        ors = " ∨ ".join(f"{v} % {q} = {r}" for r in range(q))
        pat = " | ".join([hn] * q)
        ctx.emit(f"rcases (by omega : {ors}) with {pat}")
        for r, (vv, ee, node) in enumerate(alts):
            ctx.emit("·"); c2 = ctx.copy(); c2.ind += 1
            c2.emit(f"have hx : ∃ {v}', {v} = {q} * {v}' + {r} := ⟨{v} / {q}, by omega⟩")
            c2.emit(f"obtain ⟨{v}, rfl⟩ := hx")
            cast_to(c2, node)
            c2.defic = {k: x.subst(v, ee) for k, x in c2.defic.items()}
            emit_node(c2, node)
        return
    # a general cover by substitutions v := c v' + R (R free of v) or v := R
    conds, codes = [], []
    for (v, ee, node) in alts:
        c = ee.c.get(v, 0); R = Lin(ee.k, {w: x for w, x in ee.c.items() if w != v})
        if any(x < 0 for x in R.c.values()) or R.k < 0 or c < 0: raise Unsupported(f"split {v} {exs}")
        if c == 0:
            conds.append(f"{v} = {lin(R)}"); codes.append(f"obtain rfl : {v} = {lin(R)} := by omega")
        else:
            cond = f"{lin(R)} ≤ {v}" + (f" ∧ ({v} - {lin(R)}) % {c} = 0" if c > 1 else "")
            conds.append(f"({cond})")
            codes.append(f"have hx : ∃ {v}', {v} = {lin(Lin(R.k, dict(R.c, **{v + chr(39): c})))} := "
                         f"⟨({v} - {lin(R)}) / {c}, by omega⟩; obtain ⟨{v}, rfl⟩ := hx")
    hn = ctx.fresh("hs")
    ctx.emit(f"rcases (by omega : {' ∨ '.join(conds)}) with {' | '.join([hn] * len(alts))}")
    for (vv, ee, node), code in zip(alts, codes):
        ctx.emit("·"); c2 = ctx.copy(); c2.ind += 1
        for cl in code.split("; obtain"): c2.emit(cl if cl.startswith(("have", "obtain")) else "obtain" + cl)
        cast_to(c2, node)
        c2.defic = {k: x.subst(vv, ee) for k, x in c2.defic.items()}
        emit_node(c2, node)


def leaf_target(t, why, s):
    """the Lean property of the leaf's final state, and the witnesses"""
    if why == "block":
        t2, a2, b2 = shape(s)
        if t2 not in FAM or not infam(t2, a2, b2): raise Unsupported("out of family")
        return t2, a2, b2
    raise Unsupported(f"leaf {why}")


def fam_args(t2, a2, b2):
    a0, b0 = FAM[t2]
    args = []
    for x, x0 in ((a2, a0), (b2, b0)):
        if x0 is None or x0.isconst(): continue
        d = x - x0.k
        args.append(lin(Lin(d.k // 12, {v: c // 12 for v, c in d.c.items()})))
    return args


def emit_end(ctx, s):
    """the transient ends at a moment of the counter form"""
    F = s.F
    if not F or F[-1][0] != 'H': raise Unsupported("end without history")
    h = ctx.H[F[-1][1]]
    Dfull = digterm(F[:-1], end=f"({dlist(h['digits'], h['tail'])})")
    lq, lr = E.divmod_(s.l - 1, 4); assert lr == 0
    xs = []
    for it in s.us:
        if it[0] != 'b': raise Unsupported("run at the end")
        x, r = E.divmod_(it[1] - 3, 4); assert r == 0; xs.append(lin(x))
    u = xs.pop()
    ctx.emit(f"exact EndM.of {h['q']} ({Dfull}) {lin(lq)} [{', '.join(xs)}] {u} (by bseq) (by omega)")
    ctx.emit("  (by rw [hz]; simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, "
             "List.cons.injEq, and_true, true_and] <;> omega)")


def emit_leaf(ctx, node, t2info):
    _, why, s = node
    if len(ctx.targets) == 2:
        ctx.emit("refine Lands.or_l ?_" if (why != "end") == (ctx.targets[0] != "end") else "refine Lands.or_r ?_")
    if why == "end":
        t2info.add("end"); return emit_end(ctx, s)
    t2, a2, b2 = leaf_target(None, why, s)
    t2info.add(t2 if t2 != ("C", 0, 4, 3) else ("C", 0, 4, 3))
    # the push at canon
    pushes = [o for o in s.ops if o[0] == "push"]
    last = s.lb[-1]; assert last[0] == 'H'
    hid = last[1]
    if hid not in ctx.H:
        p = [o for o in s.ops if o[0] == "push" and o[2] == hid]
        if not p: raise Unsupported("unknown final history")
        o = p[0]; src = o[1]; F = o[3]
        h = ctx.H[src]
        dig = []
        for it in F:
            if it[0] == 'b':
                dd, r = E.divmod_(it[1] - 2, 3); assert r == 0; dig.append(("d", lin(dd)))
            else:
                assert it[1] == 2; dig.append(("r", lin(it[2])))
        t = dlist(h["digits"], h["tail"])
        for kind, x in reversed(dig):
            t = f"{x} :: {t}" if kind == "d" else (f"List.replicate {x} 0 ++ ({t})" if "++" in t else f"List.replicate {x} 0 ++ {t}")
        qF, DF = h["q"], t
    else:
        qF, DF = ctx.H[hid]["q"], dlist(ctx.H[hid]["digits"], ctx.H[hid]["tail"])
    args = fam_args(t2, a2, b2)
    wit = ", ".join(args + [qF, f"({DF})"])
    a0, b0 = FAM[t2]
    front = [lin(a2)] + ([lin(b2)] if b2 is not None else [])
    # the front as the family writes it
    def famform(x, x0, nm_arg):
        return lin(x0) if x0.isconst() else f"(12 * {nm_arg} + {x0.k})"
    fr = []
    ai = 0
    for x, x0 in ((a2, a0), (b2, b0)):
        if x0 is None: continue
        if x0.isconst(): fr.append(lin(x0))
        else: fr.append(f"(12 * {args[ai]} + {x0.k})"); ai += 1
    tgt = f"⟨{' :: '.join(fr)} :: hist {qF} ({DF}), {PH[t2[0]]}, 0, (g + {t2[1]}) :: gs⟩"
    ctx.emit(f"refine Lands.fin {tgt} ?_ ⟨{wit}, by simp only [Fam_{fid(t2)}, hz]⟩")
    ctx.emit("lsteq")


def st_cfg(ctx, st):
    if st.mode == "ps":
        return f"PS.cfg {ps_term(ctx, dict(lb=st.lb, ph=st.ph, k=st.k, us=st.us))}"
    return f"gcfg ({items(ctx, st.F)}) {lin(st.l)} ({items(ctx, st.us, True)})"


def emit_loop(ctx, ev):
    _, tgt, c, d, nsteps, info = ev
    R, J, S = info["R"], info["J"], info["S"]
    S0 = S.copy(); _subst(S0, J, Lin.var(J) + Lin.var(R)); E.setlin(S0, tgt, Lin(0))
    if any(e[0] != "step" or e[4] for e in info["turn"]): raise Unsupported("loop turn with history moves")
    L_ = ctx.fresh("L")
    ctx.emit(f"have {L_} : ∀ ({R} {J} : Nat), RC ({st_cfg(ctx, S)})")
    ctx.emit(f"    ({st_cfg(ctx, S0)}) := by")
    c1 = ctx.copy(); c1.ind += 1
    c1.emit(f"intro {R}")
    c1.emit(f"induction {R} with")
    c1.emit(f"| zero => intro {J}; exact RC.castl (by cfgeq) (RC.refl _)")
    c1.emit(f"| succ {R} ih =>")
    c2 = c1.copy(); c2.ind += 1
    c2.emit(f"intro {J}")
    c2.emit(f"refine RC.trans ?_ (RC.castr (ih ({J} + 1)) (by cfgeq))")
    c2.emit("apply RC.of_lands")
    nd = ("leaf",)
    for e in reversed(info["turn"]): nd = ("step", e, nd)
    while nd[0] == "step":
        nx = emit_run(c2, nd)
        if nx is None: emit_step(c2, nd[1]); nx = nd[2]
        nd = nx
    c2.emit("exact Lands.here (by cfgeq)")
    ctx.emit(f"refine Lands.trans (b := {st_cfg(ctx, info['out'])})")
    ctx.emit(f"  (RC.castl (by cfgeq) (RC.castr ({L_} {lin(c)} 0) (by cfgeq))) ?_")
    ctx.emit(f"clear {L_}")


def fid(t):
    return "".join(str(x) for x in t)


def emit_run(ctx, node):
    """a run of moves of the pass machine without history moves after the first: one lemma (RC.prn / RC.prd);
    returns the node after the run, or None when the node is not such a run"""
    ev = node[1]
    if ev[1] != "ps": return None
    k = 0; last = ev; nxt = node[2]
    while nxt[0] == "step" and nxt[1][1] in ("ps", "pdone") and not nxt[1][4]:
        k += 1; last = nxt[1]; nxt = nxt[2]
        if last[1] == "pdone": break
    if k == 0: return None
    apply_ops(ctx, ev[4])
    after = last[3]
    if last[1] == "ps":
        ctx.emit(f"refine Lands.trans (RC.prn {k} (s' := {ps_term(ctx, after)}) rfl) ?_")
    else:
        ctx.emit(f"refine Lands.trans (RC.prd {k} (bs := {mom_bs(ctx, after)}) (l := {lin(after['l'])}) "
                 f"(us := {items(ctx, after['us'], True)}) rfl) ?_")
    return nxt


def emit_node(ctx, node, t2info):
    if node[0] == "step":
        nxt = emit_run(ctx, node)
        if nxt is not None: return emit_node(ctx, nxt, t2info)
        emit_step(ctx, node[1]); emit_node(ctx, node[2], t2info)
    elif node[0] == "loop":
        emit_loop(ctx, node[1]); emit_node(ctx, node[2], t2info)
    elif node[0] == "split":
        emit_split(ctx, node[1], lambda c, n: emit_node(c, n, t2info))
    else:
        emit_leaf(ctx, node, t2info)


def fam_def(t):
    a0, b0 = FAM[t]
    ps = []
    for x, nm in ((a0, "n"), (b0, "m")):
        if x is not None and not x.isconst(): ps.append(nm)
    def fm(x, nm):
        return lin(Lin(x.k, {nm: 12}) if not x.isconst() else x)
    front = [fm(a0, "n")] + ([fm(b0, "m")] if b0 is not None else [])
    binders = " ".join(f"({p} : Nat)" for p in ps)
    return ps, (f"def Fam_{fid(t)} {binders} (q : Nat) (D : List Nat) (bs : List Bool) : Config :=\n"
                f"  PS.cfg ⟨{' :: '.join(front)} :: hist q D, {PH[t[0]]}, 0, openZ {t[1]} bs⟩\n")


def theorem(t, v):
    out = explore(frontier(t, v))
    tr = tree([(why, s) for why, s, path in out])
    ctx = Ctx(); t2info = set(); ctx.prefix = f"aux_{fid(t)}_{v}"
    tg = set()
    for why, s, path in out:
        tg.add("end" if why == "end" else (shape(s)[0] if why == "block" else why))
    ctx.targets = sorted(tg, key=lambda x: x == "end")
    if len(tg) > 2: raise Unsupported(f"targets {tg}")
    emit_node(ctx, tr, t2info)
    def prop(t2):
        if t2 == "end": return "EndM bs c"
        ps2, _ = fam_def(t2)
        ex = " ".join(f"{p}'" for p in ps2)
        return f"∃ {ex} q' D', c = Fam_{fid(t2)} {' '.join(p + chr(39) for p in ps2)} q' D' bs"
    ps, _ = fam_def(t)
    bits = " :: ".join("true" if (v >> i) & 1 else "false" for i in range(3))
    binders = " ".join(f"({p} : Nat)" for p in ps)
    nd = {}; k0 = 0
    for r in ctx.req:
        if any(w not in ps for w in r.c) or any(c < 0 for c in r.c.values()): raise Unsupported(f"length bound {r}")
        k0 = max(k0, r.k)
        for w, c in r.c.items(): nd[w] = max(nd.get(w, 0), c)
    need = lin(Lin(k0, nd))
    head = (f"theorem case_{fid(t)}_{v} {binders} (q : Nat) (D : List Nat) (bs : List Bool) (hD : {need} ≤ D.length) :\n"
            f"    Lands (Fam_{fid(t)} {' '.join(ps)} q D ({bits} :: bs))\n"
            + f"      (fun c => {' ∨ '.join('(' + prop(x) + ')' for x in ctx.targets)}) := by\n"
            + f"  obtain ⟨g, gs, hz⟩ := openZ_eq bs\n"
            f"  simp only [Fam_{fid(t)}, openZ_false, openZ_true, hz]")
    return "\n".join(ctx.auxs) + "\n" + head + "\n" + "\n".join(ctx.lines) + "\n"


HEAD = ("namespace H4320\n\nopen TM\n\nset_option linter.unusedSimpArgs false\n"
        "set_option linter.unusedVariables false\nset_option maxHeartbeats 0\n")
# groups whose proofs are in lean/FrontCases.lean
DONE = {(("C", 0, 5, 'D'), v) for v in range(8)} | {
    (("A", 2, 6, 'D'), 0), (("C", 0, 0, 7), 0), (("C", 0, 1, 6), 0), (("C", 0, 4, 3), 0), (("C", 0, 8, 'D'), 0)}


def main():
    """gen_cases.py OUTDIR: lean/Cases/Defs.lean, one file per group, lean/Cases.lean;
    gen_cases.py - I V: the group (I-th shape, V) on stdout"""
    if sys.argv[1] == "-":
        sel = (list(FAM)[int(sys.argv[2])], int(sys.argv[3]))
        print("import Cases.Defs\n\n" + HEAD); print(theorem(*sel)); print("end H4320"); return
    out = sys.argv[1]
    os.makedirs(os.path.join(out, "Cases"), exist_ok=True)
    with open(os.path.join(out, "Cases", "Defs.lean"), "w") as f:
        f.write("import FrontLib\n\n/-! The families of the front's case tree (generated by py/gen_cases.py). -/\n\n"
                + HEAD + "\n" + "\n".join(fam_def(t)[1] for t in FAM) + "\nend H4320\n")
    mods = []; ok = bad = 0
    for t in FAM:
        for v in range(8):
            if (t, v) in DONE: continue
            try:
                th = theorem(t, v)
            except Unsupported as e:
                bad += 1; print(f"{t} {v}: not yet ({e})", file=sys.stderr); continue
            ok += 1; m = f"C{fid(t)}_{v}"; mods.append(m)
            with open(os.path.join(out, "Cases", m + ".lean"), "w") as f:
                f.write("import Cases.Defs\n\n/-! Generated by py/gen_cases.py. -/\n\n" + HEAD + "\n" + th
                        + "\nend H4320\n")
    with open(os.path.join(out, "Cases.lean"), "w") as f:
        f.write("".join(f"import Cases.{m}\n" for m in mods)
                + "\n/-! All generated groups of the front's case tree (py/gen_cases.py). -/\n")
    with open(os.path.join(out, "Cases", "list.txt"), "w") as f:
        f.write("".join(f"Cases/{m}.lean\n" for m in mods))
    print(f"generated {ok}, skipped {bad}", file=sys.stderr)


if __name__ == "__main__":
    main()
