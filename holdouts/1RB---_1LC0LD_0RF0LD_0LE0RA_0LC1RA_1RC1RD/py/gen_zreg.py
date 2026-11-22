"""Writes lean/ZRegion.lean: the E-event after Z_k for n < 12k + 12 (the region the map of Map.lean leaves open).

Inside the region the n-block runs out before the tail's (10)^k block does, so the whole pass is the 9/8 phase of a
Z tail (`srZw`: nine rounds use 24 of n and 2 of k) and ends with the rest of the block still on the tape, followed
by a new end word.  Families: n = 24j + 24 + r (r < 24), k = 2j + q e + C (e >= 0 generic; q = 1, or q = 8 for
r = 7 mod 8, where the rest of the block is itself multiplied by 9/8).  The end configuration is read off direct
simulation at sample points and fitted linearly; Lean checks it.

usage: python3 gen_zreg.py [r ...]      (writes ../lean/ZRegion.lean and ../lean/zreg.json)
"""
import itertools
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import chain as C  # noqa: E402
import emap  # noqa: E402
sys.path.insert(0, os.path.join(HERE, "..", "..", "1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LC---", "py"))
import g01tools as g  # noqa: E402

M = emap.M
NS = "H70770"
lib = C.Lib(M, NS)


def zword(k):
    return "000" + "10" * k + "0001"


def shape(tail):
    """tail string -> (template: literal words and repeated words, [repeat counts])"""
    tmpl, nums = [], []
    for t in g.compress(tail).split():
        m = re.fullmatch(r"\(([01]+)\)\^(\d+)", t)
        if m:
            tmpl.append(("R", m.group(1)))
            nums.append(int(m.group(2)))
            continue
        m = re.fullmatch(r"([01])\^(\d+)", t)
        tmpl.append(("L", m.group(1) * int(m.group(2)) if m else t))
    out = []
    for t in tmpl:
        if out and t[0] == "L" and out[-1][0] == "L":
            out[-1] = ("L", out[-1][1] + t[1])
        else:
            out.append(t)
    return tuple(out), nums


def sim(n, k, tail=None):
    d = emap.nxt(tail if tail is not None else zword(k), n, 10**11)
    if d is None:
        return None
    if d[0] == "HALT":
        return "HALT"
    return d[0], d[1]


def linfit(pts, vals, vs):
    """exact integer linear fit vals = c + sum a_v v over the sample points; or None"""
    base = pts[0]
    coef = {}
    for v in vs:
        q = [i for i, p in enumerate(pts) if all(p[u] == base[u] + (1 if u == v else 0) for u in vs)]
        if not q:
            return None
        coef[v] = vals[q[0]] - vals[0]
    c = vals[0] - sum(coef[v] * base[v] for v in vs)
    for p, y in zip(pts, vals):
        if y != c + sum(coef[v] * p[v] for v in vs):
            return None
    return c, coef


def lin_str(c, coef):
    parts = [(f"{a}*{v}" if a != 1 else v) for v, a in sorted(coef.items()) if a]
    if c or not parts:
        parts.append(str(c))
    return "+".join(parts)


def fit_end(fn, vs):
    """fn(env) -> (tail, n') by simulation; the end as (n' expression, tail token string), or None"""
    grid = [(3, 4, 6)] * len(vs)
    pts = [dict(zip(vs, p)) for p in itertools.product(*grid)]
    # put the base point first and make sure the unit steps from it are present
    outs = []
    for p in pts:
        o = fn(p)
        if o is None or o == "HALT":
            return None
        outs.append(o)
    shs = [shape(t) for t, _ in outs]
    if len({s for s, _ in shs}) != 1:
        return None
    tmpl = shs[0][0]
    nf = linfit(pts, [n for _, n in outs], vs)
    if nf is None or nf[0] < 0 or any(a < 0 for a in nf[1].values()):
        return None
    cnts = []
    for i in range(len(shs[0][1])):
        f = linfit(pts, [s[1][i] for s in shs], vs)
        if f is None or f[0] < 0 or any(a < 0 for a in f[1].values()):
            return None
        cnts.append(lin_str(*f))
    parts, ci = [], 0
    for kind, w in tmpl:
        if kind == "L":
            parts.append(" ".join(w))
        else:
            parts.append(f"({w})^{cnts[ci]}")
            ci += 1
    return lin_str(*nf), " ".join(parts)


LOOPZ = C.Loop(lib, "srZw", "0^inf (10)^27*i+3 E> (10)^24*x+y+2 0 0 0 (10)^2*x+w 0 0 0 1 0^inf",
               doc="Nine rounds of the 9/8 phase with tail Z and any rest `w` of its block: 24 of n and two of its "
                   "`10` are used up.")
LOOPT = C.Loop(lib, "srT", "L (01)^9*i+c 0 0 0 (10)^8*x+y 0 0 0 1 B> 0^inf",
               doc="A round of the 9/8 phase on the rest of the tail block, after the main block has run out: "
                   "`L (01)^(9i+c) 000 (10)^(8x+y) 0001 B>` (8 of the block become 9 `01`).")
CASES = []
SUBRE = re.compile(r"((?:10)*)((?:01)*)000((?:10)*)0001B0")


def sub_point(n, k):
    """the first right end of the run from E(n, Z_k) of the shape (10)^A (01)^c 000 (10)^b 0001 B>"""
    for _, t in g.events(M, "E> 0^6 (10)^%d %s" % (n, " ".join(zword(k))), 10**9, "B", "R"):
        if isinstance(t, int):
            return None
        m = SUBRE.fullmatch(t)
        if m and m.group(1):
            return tuple(len(m.group(i)) // 2 for i in (1, 2, 3))
    return None


def sub_params(r, Cc, q, generic_j=True):
    """(A0, c, y): the sub-pass starts at (10)^(27j + A0) (01)^c 000 (10)^(8e + y) 0001 B> (no 27j if not
    generic_j), or None"""
    pts = {}
    for J, E in ((3, 3), (4, 3), (3, 4)):
        p = sub_point(24 * J + 24 + r if generic_j else r, (2 * J if generic_j else 0) + q * E + Cc)
        if p is None:
            return None
        pts[J, E] = p
    (a, c, b), (a2, c2, b2), (a3, c3, b3) = pts[3, 3], pts[4, 3], pts[3, 4]
    if a2 - a != (27 if generic_j else 0) or a3 != a or c2 != c or c3 != c or b2 != b or b3 - b != 8:
        return None
    return a - (81 if generic_j else 0), c, b - 24


def zloop(c, r, kexpr):
    """the main loop of nine rounds, j + 1 times (j times for r < 2), from n = 24j + 24 + r, k = kexpr"""
    rest = C.S.parse_lin(kexpr) - C.S.parse_lin("2*j")
    if r >= 2:
        c.loop(LOOPZ, "j+1", "0", "0", y=str(r - 2), w=(rest - 2).lean().replace(" ", ""))
    else:
        c.loop(LOOPZ, "j", "0", "0", y=str(r + 22), w=rest.lean().replace(" ", ""))


def nk(r, Cc, q, generic_j):
    """the Lean-side expressions of n and k, and the variables"""
    qe = "" if q == 0 else ("e+" if q == 1 else f"{q}*e+")
    if generic_j:
        return f"24*j+{24 + r}", f"2*j+{qe}{Cc}", ["j"] + (["e"] if q else [])
    return str(r), f"{qe}{Cc}", (["e"] if q else [])


def attempt(name, r, Cc, q=1, generic_j=True):
    """n = 24j + 24 + r, k = 2j + q e + Cc (q = 0: no e; generic_j False: no j, n = r, k = q e + Cc)"""
    n, k, vs = nk(r, Cc, q, generic_j)

    def fn(env):
        J, E = env.get("j", 0), env.get("e", 0)
        if not generic_j:
            return sim(r, q * E + Cc)
        return sim(24 * J + 24 + r, 2 * J + q * E + Cc)
    p = fit_end(fn, vs)
    if p is None:
        return None
    n2, tail2 = p
    start = f"0^inf E> 0 0 0 0 0 0 (10)^{n} 0 0 0 (10)^{k} 0 0 0 1 0^inf"
    end = f"0^inf E> 0 0 0 0 0 0 (10)^{n2} {tail2} 0^inf"
    c = C.Case(lib, name, start)
    try:
        if generic_j:
            zloop(c, r, k)
        if q == 8:
            sp = sub_params(r, Cc, q, generic_j)
            if sp is None:
                raise ValueError("no sub-pass found")
            L = f"0^inf (10)^27*j+{sp[0]}" if generic_j else f"0^inf (10)^{sp[0]}"
            c.loop(LOOPT, "e", "0", "0", c=str(sp[1]), y=str(sp[2]), L=L)
        total = c.emit(end, f"({' '.join(vs)} : Nat)" if vs else "")
    except (C.S.ProofError, ValueError, AssertionError) as ex:
        print("  fail", name, str(ex)[:200], file=sys.stderr, flush=True)
        return "fail"
    md = dict(name=name, kind="ev", r=r, C=Cc, q=q, generic_j=generic_j, vars=vs, n=n, k=k, n2=n2, tail2=tail2,
              total=total, thm_hi=len(lib.thms))
    CASES.append(md)
    print("OK", name, "n =", n, " k =", k, " ->  n' =", n2, " tail", tail2, flush=True)
    return md


def attempt_halt(name, n, k, vs, end, loop=None):
    """a family that halts in its pass: the run reaches `end`, a configuration with no transition"""
    start = f"0^inf E> 0 0 0 0 0 0 (10)^{n} 0 0 0 (10)^{k} 0 0 0 1 0^inf"
    c = C.Case(lib, name, start)
    if loop:
        zloop(c, int(loop), k)
    total = c.emit(end, f"({' '.join(vs)} : Nat)" if vs else "")
    md = dict(name=name, kind="halt", vars=vs, n=n, k=k, end=end, total=total, thm_hi=len(lib.thms))
    CASES.append(md)
    print("OK halt", name, "n =", n, " k =", k, " ->", end, flush=True)
    return md


def first(name, r, cands, q, generic_j):
    """the first Cc of cands with a proved family, or None"""
    for Cc in cands:
        mark, names = len(lib.thms), set(lib.names)
        res = attempt(name, r, Cc, q, generic_j)
        if isinstance(res, dict):
            return Cc
        del lib.thms[mark:]
        lib.names = names
    return None


def in_region(n, k):
    return n < 12 * k + 12


if __name__ == "__main__":
    only = set(sys.argv[1:])
    # 1. n = 24j + 24 + r, k = 2j + s: generic families in the rest e of the tail block, then the s below them
    for r in range(24):
        if only and str(r) not in only:
            continue
        q = 8 if r % 8 == 7 else 1
        slo = (r + 12) // 12 + 1          # smallest s with n < 12k + 12
        for p in range(q):
            Cc = first(f"zr{r}_{p}" if q > 1 else f"zr{r}", r, range(p, 48, q), q, True)
            assert Cc is not None, (r, p)
            for sb in range(p, Cc, q):
                if sb < slo:
                    continue
                if r == 21 and sb == 3:   # k odd, n = 12k + 9: the halting family
                    attempt_halt("zh", "24*j+45", "2*j+3", ["j"], "0^inf (10)^27*j+55 A> 1 0^inf", "21")
                    continue
                assert first(f"zb{r}_{sb}", r, [sb], 0, True) is not None, (r, sb)
    # 2. n = r < 24 (no full round of nine): generic in k, then the small k one by one
    for r in range(24):
        if only and str(r) not in only:
            continue
        q = 8 if r % 8 == 7 else 1
        for p in range(q):
            Cc = first(f"zs{r}_{p}" if q > 1 else f"zs{r}", r, range(p, 48, q), q, False)
            assert Cc is not None, (r, p)
            for kk in range(p, Cc, q):
                if not in_region(r, kk) and kk > 0:
                    continue
                if r == 21 and kk == 1:
                    attempt_halt("zh0", "21", "1", [], "0^inf (10)^28 A> 1 0^inf")
                    continue
                assert first(f"zt{r}_{kk}", r, [kk], 0, False) is not None, (r, kk)
    # 3. Z_0 for n >= 24 (outside the region, but not in the map of Map.lean): after a few rounds that use up
    #    the six 0s, the 3/2 phase of tail 1
    if not only or "z0" in only:
        for p in (0, 1):
            lp = C.Loop(lib, f"srZ0{p}", f"L (10)^3*i+3 E> (10)^2*x+{2 + p} 1 0^inf",
                        doc=f"A round of the 3/2 phase with tail `1` and {'an even' if p == 0 else 'an odd'} block.")
            nn = f"2*m+{24 + p}"
            o1, o2 = sim(24 + p, 0), sim(26 + p, 0)
            assert o1[0] == o2[0] and o2[1] - o1[1] == 3, (o1, o2)
            tail2 = " ".join(o1[0])
            end = f"0^inf E> 0 0 0 0 0 0 (10)^3*m+{o1[1]} {tail2} 0^inf"
            done = False
            for c0 in range(12):
                for i0 in range(12):
                    mark, names = len(lib.thms), set(lib.names)
                    c = C.Case(lib, f"zz{p}", f"0^inf E> 0 0 0 0 0 0 (10)^{nn} 0 0 0 0 0 0 1 0^inf")
                    try:
                        c.loop(lp, "m", str(c0), str(i0), L="0^inf")
                        total = c.emit(end, "(m : Nat)")
                        done = True
                        break
                    except (C.S.ProofError, ValueError, AssertionError):
                        del lib.thms[mark:]
                        lib.names = names
                if done:
                    break
            assert done, p
            CASES.append(dict(name=f"zz{p}", kind="ev", vars=["m"], n=nn, k="0", n2=f"3*m+{o1[1]}", tail2=tail2,
                              total=total, thm_hi=len(lib.thms)))
            print("OK", f"zz{p}", nn, "->", f"3*m+{o1[1]}", tail2, flush=True)
    # the theorems in files of about 1.5 MB each (one file is too much for Lean's memory), each importing the last
    cuts, size, lo = [], 0, 0
    for c in CASES:
        size += sum(len(t) for t in lib.thms[lo:c["thm_hi"]])
        lo = c["thm_hi"]
        if size > 1_500_000:
            cuts.append(lo)
            size = 0
    if not cuts or cuts[-1] != len(lib.thms):
        cuts.append(len(lib.thms))
    names, lo = [], 0
    ldir = os.path.join(HERE, "..", "lean")
    for f in os.listdir(ldir):
        if re.fullmatch(r"ZRegion\d*\.lean", f):
            os.remove(os.path.join(ldir, f))
    for i, hi in enumerate(cuts):
        nm = f"ZRegion{i}"
        imports = ["Machine", "Chain"] if i == 0 else [names[-1]]
        txt = "".join(f"import {m}\n" for m in imports)
        txt += (f"\nset_option linter.unusedSimpArgs false\n\n/-! The E-events after Z_k inside the region n < 12k + 12,"
                f" part {i + 1} of {len(cuts)}; generated by `py/gen_zreg.py`, do not edit by hand. -/\n\n"
                f"namespace {NS}\n\nopen TM\n\n" + "\n".join(lib.thms[lo:hi]) + f"\nend {NS}\n")
        open(os.path.join(ldir, nm + ".lean"), "w").write(txt)
        names.append(nm)
        lo = hi
    json.dump(dict(files=names, cases=CASES), open(os.path.join(ldir, "zreg.json"), "w"), indent=1)
    print("files:", names)
