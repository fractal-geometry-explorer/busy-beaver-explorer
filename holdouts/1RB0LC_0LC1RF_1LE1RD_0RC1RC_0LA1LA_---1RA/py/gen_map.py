"""Writes lean/Cases.lean, lean/Map.lean and lean/cases.json for 1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_---1RA: every
case of the A-event map with an even first number a, as a Lean theorem for all values of its variables, and the map
`next` built from them with its soundness theorem `next_sound`.

Events: U(a, b) = A> 011011 1^a 0 1^b, V(a, b) = A> 1110 1^a 0 1^b (blank elsewhere).  Every event of the run from
blank tape has a even, and the map sends even a to even a, so the cases with a even are all the run needs.

A case is a family of events (a, b linear in variables x, y).  Its run is: regroup the a block into the repeats the
loop needs, a prefix (symtm2.prove), one loop (`la`, `lb`: a round of the b-odd phase; `e1`, `e2`: a round of the
Euclid phase) iterated by induction, and the rest of the way to the next event (symtm2.prove).  The loop instance
is found by unifying the loop template with the configurations of a symbolic run.  The expected next event is read
off `emap.step` at sample points and fitted linearly; Lean then checks everything.

Uses the chaining framework of ../../1RB---_1LC0LD_0RF0LD_0LE0RA_0LC1RA_1RC1RD/py/chain.py.

usage: python3 gen_map.py      (a few minutes)
"""
import itertools
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..", "..", "1RB---_1LC0LD_0RF0LD_0LE0RA_0LC1RA_1RC1RD", "py"))
import chain as C  # noqa: E402
import importlib.util  # noqa: E402

_spec = importlib.util.spec_from_file_location("emap13743", os.path.join(HERE, "emap.py"))
emap = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(emap)

S = C.S
Lin, Rep, Blank = C.Lin, C.Rep, C.Blank
M = emap.M
NS = "H13743"
PRE = {"U": "0 1 1 0 1 1", "V": "1 1 1 0"}


def ev(F, a, b):
    return f"0^inf A> {PRE[F]} (1)^{a} 0 (1)^{b} 0^inf"


def evg(F, ga, gb):
    """an event with the blocks given as token strings"""
    return f"0^inf A> {PRE[F]} {ga} 0 {gb} 0^inf"


lib = C.Lib(M, NS)
LOOPS = [
    C.Loop(lib, "la", "L (111111)^i 1 1 1 1 1 1 0 C> 1 1 1 (1111)^x+1 1 1 0 (11)^y 1 0^inf",
           doc="A round of the b-odd phase with a = 2 mod 4: four 1s of the a block become six on the left."),
    C.Loop(lib, "lb", "L (111111)^i 1 1 1 1 1 1 D> 0 (1111)^x+1 1 1 1 0 (11)^y 1 0^inf",
           doc="A round of the b-odd phase with a = 0 mod 4."),
    C.Loop(lib, "e1", "L (111111)^i 1 1 1 1 1 1 0 C> (11)^x+1 1 0 (11)^x+y 1 1 0^inf",
           doc="A round of the Euclid phase (a block the shorter): both blocks lose 11, the left gains six 1s."),
    C.Loop(lib, "e2", "L (111111)^i 1 1 1 1 1 1 0 C> (11)^x+y 1 0 (11)^x+1 1 1 0^inf",
           doc="A round of the Euclid phase (b block the shorter)."),
]
LCTX = ["0^inf", "0^inf 1"]
TV = {"x": "_x", "i": "_i", "y": "_y"}


def ren(cfg):
    return C.csub(cfg, {k: Lin(v) for k, v in TV.items()})


def flat(st):
    """normal-form stream with constant repeats as literals"""
    return C.norm_stream(st)[0]


def unify(c, tmpl):
    """env {x, i, y: Lin} with tmpl[env] the same tape as c, or None"""
    if c.state != tmpl.state:
        return None
    eqs = []
    for s1, s2 in zip(C.streams(c), C.streams(tmpl)):
        a, b = flat(s1), flat(s2)
        p = q = 0
        while q < len(b):
            t = b[q]
            if isinstance(t, Rep):
                if p < len(a) and isinstance(a[p], Rep) and a[p].word == t.word:
                    eqs.append((a[p].n, t.n))
                    p += 1
                else:
                    m = 0
                    w = list(t.word)
                    while a[p:p + len(w)] == w and all(isinstance(z, int) for z in a[p:p + len(w)]):
                        p += len(w)
                        m += 1
                    eqs.append((Lin(m), t.n))
                q += 1
            else:
                if p >= len(a) or type(a[p]) is not type(t) or (isinstance(t, int) and a[p] != t):
                    return None
                p += 1
                q += 1
        if p != len(a):
            return None
    env = {}
    for _ in range(4):
        for lc, lt in eqs:
            un = [v for v in lt.c if v not in env]
            if len(un) == 1:
                v = un[0]
                rest = Lin(lt.k, {u: a for u, a in lt.c.items() if u != v})
                rest = C.lsub(rest, env)
                d = lc - rest
                a = lt.c[v]
                if d.k % a or any(z % a for z in d.c.values()):
                    return None
                env[v] = Lin(d.k // a, {u: z // a for u, z in d.c.items()})
    for lc, lt in eqs:
        if any(v not in env for v in lt.c) or C.lsub(lt, env) != lc:
            return None
    if any(z.k < 0 or any(a < 0 for a in z.c.values()) for z in env.values()):
        return None
    return {k: env[v] for k, v in TV.items() if v in env}


def find_loop(cur):
    """the first configuration of the symbolic run from cur that is an instance of a loop with a non-constant
    number of rounds: (loop, env), or None"""
    m = S.Machine.parse(M)
    c = cur.copy()
    tr = []
    try:
        S.run(m, c, lambda c: False, max_moves=3000, trace=tr, rotate=True)
    except Exception:
        pass
    for e in tr:
        for cf in (e[1], e[2]):
            for lp in LOOPS:
                for L in LCTX:
                    env = unify(cf, ren(C.csub(lp.P, {"L": L})))
                    if env and not env["x"].is_const():
                        env["L"] = L
                        return lp, env
    return None


def fit(fn, vs):
    """fn(env) -> (F', a', b'); a linear fit in vs checked on a grid, or None"""
    base = {v: 4 for v in vs}
    pts = [dict(zip(vs, p)) for p in itertools.product(*[(4, 5, 7)] * len(vs))] or [{}]
    outs = [fn(p) for p in pts]
    if any(o is None or o == "HALT" for o in outs) or len({o[0] for o in outs}) != 1:
        return None
    o0 = fn(base)
    res = [o0[0]]
    for j in (1, 2):
        coef = {}
        for v in vs:
            e = dict(base)
            e[v] += 1
            coef[v] = fn(e)[j] - o0[j]
        c = o0[j] - sum(coef[v] * base[v] for v in vs)
        for p, o in zip(pts, outs):
            if o[j] != c + sum(coef[v] * p[v] for v in vs):
                return None
        if c < 0 or any(a < 0 for a in coef.values()):
            return None
        res.append(Lin(c, coef))
    return res


CASES = []


def rot_side(toks, near_first):
    """toks: one side of the tape (Config order); the side with the repeat next to the head re-bracketed so that a
    literal copy of its word comes first, or None"""
    st = list(toks) if near_first else list(reversed(toks))
    if not st or not isinstance(st[0], Rep):
        return None
    r = st[0]
    w = list(r.word) if near_first else list(reversed(r.word))
    if st[1:1 + len(w)] != w or not all(isinstance(z, int) for z in st[1:1 + len(w)]):
        return None
    st = w + [r] + st[1 + len(w):]
    return st if near_first else list(reversed(st))


def unstick(c, end):
    """run c towards end; if the symbolic run needs to split a repeat next to the head that is followed by a copy
    of its word, prove the way there and re-bracket it (`(w)^n w = w (w)^n`).  True when the end is reached."""
    m = S.Machine.parse(M)
    cc = c.cur.copy()
    try:
        S.run(m, cc, lambda q: not q.steps.is_zero() and C.norm_same(q, end), max_moves=20000, rotate=True)
        return True
    except S.NeedSplit:
        pass
    for side in ("r", "l"):
        new = rot_side(cc.right if side == "r" else cc.left, side == "r")
        if new is not None:
            if cc.steps.is_zero():
                c.regroup(C.Config(cc.left if side == "r" else new, cc.state, new if side == "r" else cc.right))
            else:
                cc.steps = Lin(0)
                c.to(cc)
                c.regroup(C.Config(c.cur.left if side == "r" else new, c.cur.state,
                                   new if side == "r" else c.cur.right))
            return False
    raise S.ProofError(f"stuck at {cc}")


def attempt(name, F, a, b, ga, gb, vs):
    """the case F(a, b) (Lin strings), regrouped as blocks ga, gb (token strings); metadata or None"""
    la, lb = S.parse_lin(a), S.parse_lin(b)
    e = fit(lambda env: emap.step(F, la.subs(env), lb.subs(env)), vs)
    if e is None:
        return None
    F2, a2, b2 = e
    mark, names = len(lib.thms), set(lib.names)
    c = C.Case(lib, name, ev(F, a, b))
    try:
        c.regroup(evg(F, ga, gb))
        fl = find_loop(c.cur) if vs else None
        if fl:
            lp, env = fl
            c.loop(lp, env["x"].__repr__(), "0", env["i"].__repr__(), L=env["L"],
                   **({"y": env["y"].__repr__()} if "y" in env else {}))
        binders = f"({' '.join(vs)} : Nat)" if vs else ""
        end = C.P(ev(F2, a2.__repr__(), b2.__repr__()))
        for _ in range(12):
            if unstick(c, end):
                break
        total = c.emit(end, binders)
    except (S.ProofError, ValueError, AssertionError, RuntimeError) as ex:
        print("  fail", name, str(ex)[:200], file=sys.stderr, flush=True)
        del lib.thms[mark:]
        lib.names = names
        return None
    md = dict(name=name, F=F, a=a, b=b, vars=vs, F2=F2, a2=repr(a2), b2=repr(b2), total=total)
    CASES.append(md)
    print("OK", name, F, a, b, "->", F2, a2, b2, flush=True)
    return md


def ones(n):
    """a block 1^n as tokens, grouped (n a Lin string)"""
    return f"(1)^{n}"


def generic(prefix, F, mk, Kmax=6):
    """mk(K) -> (a, b, ga, gb, vs) for the generic family with offset K; then the concrete small values mk
    leaves out are added by the caller.  Returns the K that worked."""
    for K in range(Kmax):
        a, b, ga, gb, vs = mk(K)
        if attempt(f"{prefix}_g{K}", F, a, b, ga, gb, vs):
            return K
    raise SystemExit(f"no generic case for {prefix}")


def must(*args):
    r = attempt(*args)
    assert r, args[0]


if __name__ == "__main__":
    for F in "UV":
        # a = 2 mod 4, b odd
        K = generic(f"A{F}", F, lambda K: (f"4*x+{4 * K + 2}", "2*y+1", f"(1111)^x+{K} 1 1", "(11)^y 1", ["x", "y"]))
        for a in range(2, 4 * K + 2, 4):
            must(f"A{F}_a{a}", F, str(a), "2*y+1", ones(a), "(11)^y 1", ["y"])
        # a = 0 mod 4, b odd >= 7, b = 3, b = 5
        for bb, gb, vb in (("2*y+7", "(11)^y+3 1", ["y"]), ("3", "1 1 1", []), ("5", "1 1 1 1 1", [])):
            tag = f"B{F}" + ("" if vb else bb)
            K = generic(tag, F, lambda K: (f"4*x+{4 * K + 4}", bb, f"(1111)^x+{K + 1}", gb, ["x"] + vb))
            for a in range(4, 4 * K + 4, 4):
                must(f"{tag}_a{a}", F, str(a), bb, ones(a), gb, vb)
        # a, b even, b >= a + 4
        K = generic(f"C{F}", F, lambda K: (f"2*x+{2 * K + 2}", f"2*x+2*y+{2 * K + 6}", f"(11)^x+{K + 1}",
                                           f"(11)^x+y+{K + 3}", ["x", "y"]))
        for a in range(2, 2 * K + 2, 2):
            must(f"C{F}_a{a}", F, str(a), f"2*y+{a + 4}", ones(a), f"(11)^y+{a // 2 + 2}", ["y"])
        # a, b even, b <= a - 2 (b >= 2)
        K = generic(f"D{F}", F, lambda K: (f"2*x+2*y+{2 * K + 4}", f"2*y+{2 * K + 2}", f"(11)^x+y+{K + 2}",
                                           f"(11)^y+{K + 1}", ["x", "y"]))
        for b in range(2, 2 * K + 2, 2):
            must(f"D{F}_b{b}", F, f"2*x+{b + 2}", str(b), f"(11)^x+{b // 2 + 1}", ones(b), ["x"])
        # b = a, b = a + 2 (a even >= 2)
        for d in (0, 2):
            K = generic(f"E{F}{d}", F, lambda K: (f"2*x+{2 * K + 2}", f"2*x+{2 * K + 2 + d}", f"(11)^x+{K + 1}",
                                                  f"(11)^x+{K + 1 + d // 2}", ["x"]))
            for a in range(2, 2 * K + 2, 2):
                must(f"E{F}{d}_a{a}", F, str(a), str(a + d), ones(a), ones(a + d), [])
    out = C.lean_file(lib, ["Machine", "Chain"],
                      "The cases of the A-event map (a even), generated by `py/gen_map.py` with "
                      "`../1RB---_1LC0LD_0RF0LD_0LE0RA_0LC1RA_1RC1RD/py/chain.py`; do not edit by hand.")
    open(os.path.join(HERE, "..", "lean", "Cases.lean"), "w").write(out)
    json.dump(CASES, open(os.path.join(HERE, "..", "lean", "cases.json"), "w"), indent=1)
    print(len(CASES), "cases")
