"""The counting rules at depth 1, 2 and 3 of 1RB0LE_1RC0LB_1RD0RC_1LA1RC_---1LF_1LB1LD as Lean theorems (lean/Deep/*.lean, one file per rule).

Depth k: k blocks lie between the counter c and the block holding the marker `0 0`.  From one rest-like moment
(head at the left end in state B reading 1) to the next, the boundaries between the k blocks work as a binary
counter: the head runs 2^k times between the marker and the boundaries, moving copies of 1101 across the marker
each time, and the counter c gains one when the binary counter overflows.  So one unit of c costs 4·2^k + 2·2^k =
6·2^k copies (`uk_one` moves 4·2^k, `uk_two` moves 2·2^k and increments c).  Depth 0 is `u0_one`, `u0_two` in
Rules.lean.

The proofs are `symtm2.prove` runs (split into segments of at most 40 single steps) through the chaining framework
of ../../1RB---_1LC0LD_0RF0LD_0LE0RA_0LC1RA_1RC1RD/py/chain.py; each segment theorem leaves the
tape it does not touch as contexts and is stated with small constant offsets in its repeat counts (the kernel's
check of a step through `rep (z + k)` grows exponentially with k), then instantiated.

usage: python3 gen_deep.py       (writes ../lean/Deep/*.lean; about a minute)
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "1RB---_1LC0LD_0RF0LD_0LE0RA_0LC1RA_1RC1RD", "py"))
import chain as C  # noqa: E402

M = "1RB0LE_1RC0LB_1RD0RC_1LA1RC_---1LF_1LB1LD"
W = "(1101)"
CUT = 12


def shifts(*cfgs):
    """{v: m}: every repeat count containing v is v + k with k >= m (m > 0); the segment is then stated with v - m in
    place of v, so that its repeats have small constant offsets (the kernel's check is exponential in them)"""
    occ = {}
    bad = set()
    for cf in cfgs:
        for t in list(cf.left) + list(cf.right):
            if isinstance(t, C.Rep):
                n = t.n
                if len(n.c) == 1 and list(n.c.values()) == [1]:
                    v = next(iter(n.c))
                    occ[v] = min(occ.get(v, n.k), n.k)
                else:
                    bad |= set(n.c)
    return {v: m for v, m in occ.items() if v not in bad and m > 0}


def lean_of(lin, env):
    """a Lin as a Lean term with its variables replaced by Lean terms"""
    parts = [(f"({env[v]})" if a == 1 else f"{a} * ({env[v]})") for v, a in sorted(lin.c.items())]
    if lin.k or not parts:
        parts.append(str(lin.k))
    return " + ".join(parts)


def to_abs(c, target):
    """like Case.to, but the segment theorem has the parts of the tape it does not touch as contexts L2, R2
    (instantiated when the theorem is used): the far blocks then never enter the kernel's computation"""
    cur = c.cur
    S = C.S
    sl = C.streams(cur)[0]          # left, nearest first
    tl = C.streams(target)[0]

    def attempt(kl, kr):
        L, R = [], []
        nl, nr = cur.left, cur.right
        if kr is not None:
            suf = cur.right[kr:]
            if target.right[len(target.right) - len(suf):] != suf:
                return None
            R = suf
            nr = cur.right[:kr] + [C.Ctx("R2")]
            tr_ = target.right[:len(target.right) - len(suf)] + [C.Ctx("R2")]
        else:
            tr_ = target.right
        if kl is not None:
            far = sl[kl:]
            if tl[len(tl) - len(far):] != far:
                return None
            L = far
            nl = [C.Ctx("L2")] + cur.left[len(cur.left) - kl:]
            tl_ = [C.Ctx("L2")] + target.left[len(target.left) - (len(tl) - len(far)):]
        else:
            tl_ = target.left
        st = C.Config(nl, cur.state, nr)
        en = C.Config(tl_, target.state, tr_)
        sh = shifts(st, en)
        st = C.csub(st, {v: C.Lin(v) + (-m) for v, m in sh.items()})
        en = C.csub(en, {v: C.Lin(v) + (-m) for v, m in sh.items()})
        nm = f"{c.name}_s{c.nseg}"
        try:
            fin, vs, ctxs = c.lib.prove(nm, st, en)
        except (S.ProofError, ValueError, AssertionError):
            c.lib.names.discard(nm)
            return None
        return fin, vs, ctxs, L, R, sh

    def ok(r):
        return r is not None

    best = None
    for kr in list(range(1, len(cur.right))) + [None]:
        if kr is not None and all(isinstance(t, S.Blank) for t in cur.right[kr:]):
            continue
        mark = len(c.lib.thms)
        r = attempt(None, kr)
        if ok(r):
            del c.lib.thms[mark:]
            c.lib.names.discard(f"{c.name}_s{c.nseg}")
            best_kr = kr
            break
    for kl in list(range(1, len(sl))) + [None]:
        if kl is not None and all(isinstance(t, S.Blank) for t in sl[kl:]):
            continue
        r = attempt(kl, best_kr)
        if ok(r):
            best = r
            break
    fin, vs, ctxs, Lf, Rf, sh = best
    nm = f"{c.name}_s{c.nseg}"
    c.nseg += 1
    env = {v: (f"{v} + {sh[v]}" if sh.get(v) else v) for v in vs}
    args = " ".join(f"({v} := {env[v]})" for v in vs)
    count = lean_of(fin.steps, env)
    fin = C.csub(fin, {v: C.Lin(v) + m for v, m in sh.items()})
    if Rf:
        args += f" (R2 := {C.sterm(Rf)})"
    if Lf:
        args += f" (L2 := {C.sterm(Lf)})"
    full = C.Config([t for t in fin.left if not (isinstance(t, C.Ctx) and t.name == "L2")],
                    fin.state, [t for t in fin.right if not (isinstance(t, C.Ctx) and t.name == "R2")])
    # put the contexts' tokens back
    fl = fin.left
    if Lf:
        assert isinstance(fl[0], C.Ctx) and fl[0].name == "L2", fl
        far_cfg = [C.Rep(tuple(reversed(t.word)), t.n) if isinstance(t, C.Rep) else t for t in reversed(Lf)]
        full.left = far_cfg + fl[1:]
    if Rf:
        assert isinstance(fin.right[-1], C.Ctx) and fin.right[-1].name == "R2", fin.right
        full.right = fin.right[:-1] + Rf
    full.steps = fin.steps
    c.pieces.append((f"{nm} {args}", count, cur, full))
    c.cur = full.copy()
    c.cur.steps = C.Lin(0)

RULES = [
    ("u1_one", f"0^inf B> 1 {W}^c+1 0 {W}^p+1 0 {W}^z+9 0 0 {W}^y+1 0 R",
     f"0^inf B> 1 0 {W}^c+1 0 {W}^p+1 0 {W}^z+1 0 0 {W}^y+9 0 R",
     "Depth 1, first half: eight copies cross the marker (two runs of the binary counter of one boundary)."),
    ("u1_two", f"0^inf B> 1 0 {W}^c+1 0 {W}^p+1 0 {W}^z+5 0 0 {W}^y+1 0 R",
     f"0^inf B> 1 {W}^c+2 0 {W}^p+1 0 {W}^z+1 0 0 {W}^y+5 0 R",
     "Depth 1, second half: four more copies cross and the counter gains one (twelve per unit)."),
    ("u2_one", f"0^inf B> 1 {W}^c+1 0 {W}^p+1 0 {W}^q+1 0 {W}^z+17 0 0 {W}^y+1 0 R",
     f"0^inf B> 1 0 {W}^c+1 0 {W}^p+1 0 {W}^q+1 0 {W}^z+1 0 0 {W}^y+17 0 R",
     "Depth 2, first half: sixteen copies cross the marker (four runs of the two-boundary binary counter)."),
    ("u2_two", f"0^inf B> 1 0 {W}^c+1 0 {W}^p+1 0 {W}^q+1 0 {W}^z+9 0 0 {W}^y+1 0 R",
     f"0^inf B> 1 {W}^c+2 0 {W}^p+1 0 {W}^q+1 0 {W}^z+1 0 0 {W}^y+9 0 R",
     "Depth 2, second half: eight more copies cross and the counter gains one (24 per unit)."),
    ("u3_one", f"0^inf B> 1 {W}^c+1 0 {W}^p+1 0 {W}^q+1 0 {W}^r+1 0 {W}^z+33 0 0 {W}^y+1 0 R",
     f"0^inf B> 1 0 {W}^c+1 0 {W}^p+1 0 {W}^q+1 0 {W}^r+1 0 {W}^z+1 0 0 {W}^y+33 0 R",
     "Depth 3, first half: 32 copies cross the marker (eight runs of the three-boundary binary counter)."),
    ("u3_two", f"0^inf B> 1 0 {W}^c+1 0 {W}^p+1 0 {W}^q+1 0 {W}^r+1 0 {W}^z+17 0 0 {W}^y+1 0 R",
     f"0^inf B> 1 {W}^c+2 0 {W}^p+1 0 {W}^q+1 0 {W}^r+1 0 {W}^z+1 0 0 {W}^y+17 0 R",
     "Depth 3, second half: 16 more copies cross and the counter gains one (48 per unit)."),
]

if __name__ == "__main__":
    for name, start, end, doc in RULES:
        lib = C.Lib(M, "H173433")
        c = C.Case(lib, name, start, doc=doc)
        vs = sorted(C.P(start).vars())
        # cut the run into pieces of about CUT moves, each its own theorem (keeps the kernel's memory small)
        m = C.S.Machine.parse(M)
        cc, tr = C.P(start), []
        C.S.run(m, cc, lambda q: not q.steps.is_zero() and C.norm_same(q, C.P(end)), max_moves=20000, trace=tr,
                rotate=True)
        for e in tr[CUT::CUT][:-1]:
            t = e[2].copy()
            t.steps = C.S.Lin(0)
            to_abs(c, t)
        to_abs(c, C.P(end))
        total = c.emit(end, f"({' '.join(vs)} : Nat) (R : Tape)")
        print(name, ":", start, "->", end, "in", total, "steps", flush=True)
        out = C.lean_file(lib, ["Machine", "Chain"],
                          f"Counting rule `{name}`, generated by `py/gen_deep.py`; do not edit by hand.")
        out = out.replace("set_option linter.unusedSimpArgs false\n",
                          "set_option linter.unusedSimpArgs false\nset_option maxRecDepth 8000\n")
        open(os.path.join(HERE, "..", "lean", "Deep", f"{name}.lean"), "w").write(out)
