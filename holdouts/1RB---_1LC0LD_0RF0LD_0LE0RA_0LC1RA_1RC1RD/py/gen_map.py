"""Writes lean/Cases.lean: every case of the E-event map of 1RB---_1LC0LD_0RF0LD_0LE0RA_0LC1RA_1RC1RD as a Lean
theorem (for all values of its variables), and lean/cases.json, the list of cases the map file is built from.

A case is a family of E-events E(n, T) (`ev`), n and the tail index written with variables m, t, j, and the theorem
says the machine goes to the next E-event the map (`emap.step`) predicts, in the stated number of steps.  The run is
proved by `chain.py`: segments by `symtm2.prove`, loops (`srX`, `srY`, `srY0`: three rounds of the 9/8 phase;
`one_even`, `one_odd`: a round of the 3/2 phase, also used on the tail) by induction.  The expected next event is
read off `emap.step` at sample points and fitted linearly; Lean then checks it.

usage: python3 gen_map.py            (writes ../lean/Cases.lean and ../lean/cases.json; a few minutes)
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import chain as C  # noqa: E402
import emap  # noqa: E402

M = emap.M
NS = "H70770"


def tl(F, t):
    return {"1": "1", "X": f"0 0 0 (10)^{t} 1", "Y": f"1 1 (01)^{t}", "Z": f"0 0 0 (10)^{t} 0 0 0 1"}[F]


def ev(n, F, t):
    return f"0^inf E> 0 0 0 0 0 0 (10)^{n} {tl(F, t)} 0^inf"


def ev_lean(n, F, t):
    T = {"1": ".one", "X": f".X ({t})", "Y": f".Y ({t})", "Z": f".Z ({t})"}[F]
    return f"Ev ({n}) ({T})"


def evalin(expr, env):
    return eval(expr.replace("^", "**"), {}, dict(env))


def fit(fn, vs):
    """fn(env) -> (F', t', n'); a linear fit of t', n' in the variables vs, checked on a grid; or None"""
    import itertools
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
        res.append(lin_str(coef, c))
    return res


def lin_str(coef, c):
    parts = [(f"{a}*{v}" if a != 1 else v) for v, a in sorted(coef.items()) if a]
    if c or not parts:
        parts.append(str(c))
    return "+".join(parts)


lib = C.Lib(M, NS)
LOOPS = {
    "X": C.Loop(lib, "srX", "0^inf (10)^9*i+3 E> (10)^8*x+8+r 0 0 0 (10)^t 1 0^inf",
                doc="Three rounds of the 9/8 phase with tail X_t: `(10)^(9i+3) E> (10)^(8x+8+r) 000 (10)^t 1`."),
    "Y": C.Loop(lib, "srY", "0^inf (10)^9*i+3 E> (10)^8*x+8+r 1 1 (01)^t+1 0^inf",
                doc="Three rounds of the 9/8 phase with tail Y_(t+1)."),
    "Y0": C.Loop(lib, "srY0", "0^inf (10)^9*i+3 E> (10)^8*x+8+r 1 1 0^inf",
                 doc="Three rounds of the 9/8 phase with tail Y_0."),
    "e": C.Loop(lib, "one_even", "L (10)^3*i+3 E> (10)^2*x+2 1 0^inf",
                doc="A round of the 3/2 phase (on the main block with tail `1`, or on a tail): `L (10)^(3i+3) E> (10)^(2x+2) 1`."),
    "o": C.Loop(lib, "one_odd", "L (10)^3*i+3 E> (10)^2*x+3 1 0^inf",
                doc="A round of the 3/2 phase with an odd block."),
}

CASES = []


def tail_point(c, var="j"):
    """the 3/2 phase on a tail: state E, right = (10)^(2j+c) 1 blank, left ending in (10)^3"""
    if C.S.STATES[c.state] != "E":
        return False
    r = C.norm_stream(C.streams(c)[1])[0]
    if not (len(r) == 3 and isinstance(r[0], C.Rep) and r[0].word == (1, 0) and var in r[0].n.c and r[1] == 1
            and isinstance(r[2], C.Blank)):
        return False
    lf = C.S.canon(c.left)
    return len(lf) >= 7 and lf[-6:] == [1, 0, 1, 0, 1, 0]


def attempt(name, F, n, t, vs, kind, zloop=None):
    """kind: 'big' (n = 8m+8+r, super-round loop first) or 'small' or 'one'; returns metadata or None"""
    def fn(env):
        return emap.step(F, evalin(t, env), evalin(n, env))
    e = fit(fn, vs)
    if e is None:
        return None
    F2, t2, n2 = e
    start = ev(n, F, t)
    end = ev(n2, F2, t2 if F2 != "1" else "0")
    c = C.Case(lib, name, start)
    try:
        if kind == "big":
            r = int(n.split("+")[-1])
            if F == "X":
                c.loop(LOOPS["X"], "m", "0", "0", r=r, t=t)
            elif t == "0":
                c.loop(LOOPS["Y0"], "m", "0", "0", r=r)
            else:
                tm = C.S.parse_lin(t) - 1
                if tm.k < 0:
                    raise C.S.ProofError("Y needs t >= 1 here")
                c.loop(LOOPS["Y"], "m", "0", "0", r=r, t=tm.lean().replace(" ", ""))
        elif kind == "Z":
            sz, cz = zloop
            c.loop(LOOPS["Z", sz], "j", "0", "0", y=f"2*z+{cz - 24}")
        elif kind == "one":
            if n.startswith("2*m"):
                c.loop(LOOPS["e" if int(n.split("+")[-1]) % 2 == 0 else "o"], "m", "0", "0", L="0^inf")
        if "j" in vs or kind == "Z":
            var = "z" if kind == "Z" else "j"
            pt = C.run_until(M, c.cur, lambda c: tail_point(c, var))
            if pt is None:
                raise C.S.ProofError("no tail phase found")
            r = C.norm_stream(C.streams(pt)[1])[0][0].n
            cc = r.k
            lf = C.S.canon(pt.left)[:-6]
            Lstr = C.tok_str(lf)
            assert r.c == {var: 2}, r
            if cc % 2 == 0:
                c.loop(LOOPS["e"], var, str((cc - 2) // 2), "0", L=Lstr)
            else:
                c.loop(LOOPS["o"], var, str((cc - 3) // 2), "0", L=Lstr)
        binders = f"({' '.join(vs)} : Nat)" if vs else ""
        total = c.emit(end, binders)
    except (C.S.ProofError, ValueError, AssertionError) as ex:
        print("  fail", name, str(ex)[:160], file=sys.stderr, flush=True)
        # forget the theorems this attempt added
        return "fail"
    md = dict(name=name, F=F, n=n, t=t, vars=vs, F2=F2, n2=n2, t2=t2 if F2 != "1" else "0", total=total)
    CASES.append(md)
    print("OK", name, F, n, t, "->", F2, n2, t2, flush=True)
    return md


def run_family(prefix, F, n, kind, nvars, Kmax=4, parity=False):
    """generic t >= K (smallest K that works) plus the concrete t < K"""
    if parity:
        for p in (0, 1):
            for K in range(0, Kmax):
                mark = len(lib.thms)
                names = set(lib.names)
                tt = f"2*j+{p + 2 * K}"
                res = attempt(f"{prefix}_{'e' if p == 0 else 'o'}{K}", F, n, tt, nvars + ["j"], kind)
                if isinstance(res, dict):
                    break
                del lib.thms[mark:]
                lib.names = names
            for t0 in range(p, p + 2 * K, 2):
                res = attempt(f"{prefix}_t{t0}", F, n, str(t0), nvars, kind)
                assert isinstance(res, dict), (prefix, t0)
        return
    for K in range(0, Kmax):
        mark = len(lib.thms)
        names = set(lib.names)
        res = attempt(f"{prefix}_g{K}", F, n, f"t+{K}", nvars + ["t"], kind)
        if isinstance(res, dict):
            break
        del lib.thms[mark:]
        lib.names = names
    else:
        raise SystemExit(f"no generic case for {prefix}")
    for t0 in range(K):
        mark = len(lib.thms)
        res = attempt(f"{prefix}_t{t0}", F, n, str(t0), nvars, kind)
        assert isinstance(res, dict), (prefix, t0)


if __name__ == "__main__":
    # tail 1
    attempt("one_e", "1", "2*m+2", "0", ["m"], "one")
    attempt("one_o", "1", "2*m+3", "0", ["m"], "one")
    attempt("one_0", "1", "0", "0", [], "small")
    attempt("one_1", "1", "1", "0", [], "small")
    for F in "XY":
        for r in range(8):
            par = (F == "X" and r == 7) or (F == "Y" and r == 2)
            run_family(f"c{F}{r}", F, f"8*m+8+{r}", "big", ["m"], parity=par)
            run_family(f"s{F}{r}", F, f"{r}", "small", [], parity=par)
    for sz in (1, 2):
        LOOPS["Z", sz] = C.Loop(lib, f"srZ{sz}", f"0^inf (10)^27*i+3 E> (10)^24*x+y+24 0 0 0 (10)^2*x+{sz} 0 0 0 1 0^inf",
                                doc=f"Nine rounds of the phase with tail Z: two of the tail's `10` are used up.")
        for p in (0, 1):
            for cz in range(12 * sz + 12 + p, 70, 2):
                mark, names = len(lib.thms), set(lib.names)
                res = attempt(f"cZ{sz}{p}_{cz}", "Z", f"24*j+2*z+{cz}", f"2*j+{sz}", ["j", "z"], "Z", (sz, cz))
                if isinstance(res, dict):
                    break
                del lib.thms[mark:]
                lib.names = names
    out = C.lean_file(lib, ["Machine", "Chain"],
                      "The cases of the E-event map, generated by `py/gen_map.py` with `py/chain.py`; do not edit by hand.")
    open(os.path.join(HERE, "..", "lean", "Cases.lean"), "w").write(out)
    json.dump(CASES, open(os.path.join(HERE, "..", "lean", "cases.json"), "w"), indent=1)
    print(len(CASES), "cases")
