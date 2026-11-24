"""Write the Lean theorem of one step family of the walk.

A family: a reading state (suffix, header) and a digit pattern read from the counter, top to bottom, with run lengths
affine in r (r >= 0).  The step is run concretely (famdata.py) for r = 0..3 and several down-counters; its boundaries
(pass ends, phase ends) are fitted over r: at a phase the tape is a tick configuration `tcfg H u v L R` with the
up-counter u of a width affine in r, the cells above it constant, and the down-counter v = (low bits) ++ (rest).
Each pass is proved by symtm on the encoding's blocks (symglue.prove_enc); each phase fills u and is
`StepKit.phase_split`; the theorem collects them:

  theorem NAME (r) (X) (Ltop) (v0) (R0) (hv : 2 ^ (a r + b) <= val v0) :
    ∃ z, z.length + c1 = v0.length + c2 ∧ val z + A1 * 2 ^ (a r) = A * val v0 + A0 ∧
      Reach (clean start) (clean end with V = (low bits) ++ z)
"""
import os, sys, random
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import famdata as FD
import symglue as G
from bbtools.symtm import Rep, Ctx, Lin, Config, STATES

M = FD.M
RS = range(4)
B = {False: "false", True: "true", 0: "false", 1: "true"}


class Unsupported(Exception):
    pass


class NeedV(Unsupported):
    """the step depends on low bits of the down-counter: split the family on them"""


def lw(bits):
    return "[" + ", ".join(B[b] for b in bits) + "]"


def fit_lin(vals):
    a = vals[1] - vals[0]
    if any(vals[i + 1] - vals[i] != a for i in range(len(vals) - 1)):
        return None
    return Lin(0, {"r": a} if a else {}) + vals[0]


def rle(bits):
    out = []
    for b in bits:
        if out and out[-1][0] == b:
            out[-1][1] += 1
        else:
            out.append([b, 1])
    return out


def fit_runs(lists):
    """bit lists for r = 0..3 -> [(bit, Lin)] (one structure) or None"""
    rs = [rle(x) for x in lists]
    if len({len(x) for x in rs}) != 1 or any([b for b, _ in x] != [b for b, _ in rs[0]] for x in rs):
        return None
    out = []
    for i in range(len(rs[0])):
        n = fit_lin([x[i][1] for x in rs])
        if n is None:
            return None
        out.append((rs[0][i][0], n))
    return out


def runs_eval(runs, r):
    out = []
    for b, n in runs:
        out += [b] * n.subs({"r": r})
    return out


def runs_lean(runs):
    """runs in list order -> Lean list expression"""
    parts, lit = [], []
    for b, n in runs:
        if n.is_const():
            lit += [b] * n.k
        else:
            if lit:
                parts.append(lw(lit)); lit = []
            parts.append(f"rf ({n.lean()}) {B[b]}")
    if lit:
        parts.append(lw(lit))
    return " ++ ".join(parts) if parts else "[]"


def runs_tokens(runs, word):
    """runs in reading order -> tokens; word(bit) the cells of one digit in reading order"""
    out = []
    for b, n in runs:
        w = tuple(int(ch) for ch in word(b))
        if n.is_const():
            out += list(w) * n.k
        else:
            out.append(Rep(w, n))
    return out


UW = lambda b: "00001" if b else "00000"
VW = lambda b: "01" if b else "11"


def cells_tokens(s):
    return [int(ch) for ch in s]


def collect(suf, H, digruns, vpre=(), seeds=3, nv=None):
    data = {}
    for r in RS:
        digs = "".join(("1" if b else "0") * n.subs({"r": r}) for b, n in digruns)
        rows = []
        for sd in range(seeds):
            random.seed(1000 * r + sd)
            n = nv or (8 * len(digs) + 40)
            V = ((random.getrandbits(n - 4) | (1 << (n - 4)) | (1 << (n - 5))) << len(vpre)) | vval(vpre)
            n += len(vpre)
            res = FD.run(digs, suf, H, V, n)
            if isinstance(res, str):
                raise Unsupported(f"r={r}: {res}")
            res['V0'], res['nv'] = V >> len(vpre), n - len(vpre)
            rows.append(res)
        data[r] = rows
    ev0 = [e[0] if e[0] != 'phase' else (e[0], e[2]) for e in data[0][0]['events']]
    for r in RS:
        for row in data[r]:
            if [e[0] if e[0] != 'phase' else (e[0], e[2]) for e in row['events']] != ev0:
                raise NeedV("event structure differs")
    return data


def vval(bits):
    return sum(1 << i for i, b in enumerate(bits) if b)


def generate(name, suf, Hi, digruns, doc="", vpre=()):
    H = FD.HD[Hi]
    data = collect(suf, H, digruns, vpre)
    rows = [(r, row) for r in RS for row in data[r]]
    ev = data[0][0]['events']
    nb = len(data[0][0]['bounds'])
    has_r = any(not n.is_const() for _, n in digruns)
    # widths of the phases and carries, per r
    W = {}
    for i, e in enumerate(ev):
        if e[0] in ('phase', 'carry'):
            W[i] = fit_lin([data[r][0]['events'][i][1] for r in RS])
            if W[i] is None:
                raise Unsupported("width not affine")
    def tick_at(j):
        """the phase or carry next to boundary j"""
        if j < len(ev) and ev[j][0] != 'pass':
            return j
        if j >= 1 and ev[j - 1][0] != 'pass':
            return j - 1
        return None

    def bound_left(j, tc=False):
        """(Lx cells, U runs MSB first, tail cells, kind)"""
        if j == 0 and not tc:
            return ("", [(b, n) for b, n in digruns], suf + "00", "start")
        if j == nb - 1 and not tc:
            ss = {row['bounds'][j]['lit'] for r, row in rows}
            if len(ss) != 1:
                raise Unsupported("end suffix varies")
            return ("", [], ss.pop(), "end")
        i = tick_at(j)
        lxs, us = [], []
        for r in RS:
            w = W[i].subs({"r": r})
            for row in data[r]:
                lit = row['bounds'][j]['lit']
                if lit[-2:] != "00":
                    raise Unsupported("no gap")
                U = lit[len(lit) - 2 - 5 * w:len(lit) - 2]
                ws = [U[k:k + 5] for k in range(0, len(U), 5)]
                if any(x not in ("00000", "00001") for x in ws):
                    raise Unsupported(f"U words {ws}")
                lxs.append(lit[:len(lit) - 2 - 5 * w])
                if row is data[r][0]:
                    us.append([x == "00001" for x in ws])
        if len(set(lxs)) != 1:
            raise Unsupported(f"cells above U vary: {set(lxs)}")
        runs = fit_runs(us)
        if runs is None:
            raise Unsupported("U not fitted")
        return (lxs[0], runs, "00", "tcfg")

    lefts = [bound_left(j) for j in range(nb)]
    tl0 = bound_left(0, tc=True) if ev[0][0] != 'pass' else None
    heads = []
    for j in range(nb):
        hs = {row['bounds'][j]['H'] for r, row in rows}
        if len(hs) != 1:
            raise Unsupported("header varies")
        heads.append(hs.pop())

    def L_of(j):
        return tl0 if (j == 0 and tl0) else lefts[j]

    def lx_cells(j):
        return [c == '1' for c in reversed(L_of(j)[0])]

    def lx_lean(j, drop=0):
        acc = "(encU X Ltop)"
        for c in reversed(lx_cells(j)[drop:]):
            acc = f"(cons {B[c]} {acc})"
        return acc

    def u_lean(j):
        runs = list(reversed(L_of(j)[1]))
        if len(runs) == 1:
            return f"rf ({runs[0][1].lean()}) {B[runs[0][0]]}"
        return runs_lean(runs)

    def u_tokens(j):
        runs = L_of(j)[1]
        if len(runs) == 1 and lefts[j][3] == "tcfg":
            b, n = runs[0]
            return [Rep(tuple(int(ch) for ch in UW(b)), n)]
        return runs_tokens(runs, UW)

    def hname(h):
        return "hdr0" if h == FD.HD[0] else "hdr1"

    def cfg_lean(j, v):
        lx, runs, tail, kind = lefts[j]
        if kind == "start":
            S = lw([c == '1' for c in reversed(suf)])
            return f"⟨cons false (cons false (app {S} (encU ({runs_lean(list(reversed(digruns)))} ++ X) Ltop))), app {hname(heads[j])} (encV ({v}) R0), .D⟩"
        if kind == "end":
            S = lw([c == '1' for c in reversed(tail[:-2])])
            return f"⟨cons false (cons false (app {S} (encU X Ltop))), app {hname(heads[j])} (encV ({v}) R0), .D⟩"
        return f"(tcfg {hname(heads[j])} ({u_lean(j)}) ({v}) {lx_lean(j)} R0)"

    def tcfg_lean(j, v):
        return f"(tcfg {hname(heads[j])} ({u_lean(j)}) ({v}) {lx_lean(j)} R0)"

    def left_tokens(j):
        lx, runs, tail, kind = lefts[j]
        return [Ctx("L")] + cells_tokens(lx) + u_tokens(j) + cells_tokens(tail)

    def right_tokens(j, vbits_runs):
        return cells_tokens(heads[j]) + runs_tokens(vbits_runs, VW) + [Ctx("R")]

    def need(i):
        """pairs of V the pass i reads (from its start boundary)"""
        m = 0
        for r, row in rows:
            bs = row['bounds'][i]
            hi = row['events'][i][3]
            m = max(m, -(-(hi - (bs['pos'] + 7) + 1) // 2))
        return m

    SIMP = ("tcfg, encU, encV, encU_append, encV_append, encU_replicate, encV_replicate, dU, dV, hdr0, hdr1, app, "
            "List.cons_append, List.nil_append, List.append_assoc, List.append_nil, rep_zero_cons, rep_succ, rep_zero")
    slopes = {W[i].c.get("r", 0) for i in W}
    slopes.discard(0)
    if len(slopes) > 1:
        raise Unsupported(f"widths with slopes {slopes}")
    a = slopes.pop() if slopes else 0
    if any(W[i].c.get("r", 0) == 0 and a for i in W if ev[i][0] == 'phase'):
        raise Unsupported("constant-width phase in a family")
    Qe = f"2 ^ ({a} * r)" if a else "1"
    Qof = lambda r: 1 << (a * r)
    ticks = [i for i in W]

    body, passtext, steps_terms, needs = [], [], [], []
    VL = list(vpre)          # the known low bits of V (constant), then the rest zcur
    VLsym = None             # runs of the low bits when they have symbolic lengths (only at the end)
    zcur = "v0"
    k = 0

    def vcur_lean():
        if VLsym is not None:
            return f"{runs_lean(VLsym)} ++ {zcur}"
        return f"{lw(VL)} ++ {zcur}" if VL else zcur

    for idx, e in enumerate(ev):
        if e[0] == 'pass':
            if VLsym is not None:
                raise Unsupported("a pass after symbolic low bits of V")
            mv = len(VL)
            if need(idx) > mv:
                raise NeedV(f"pass {k} reads {need(idx)} pairs of V, {mv} known")
            ves = []
            for r in RS:
                mer = set()
                for row in data[r]:
                    bs, be = row['bounds'][idx], row['bounds'][idx + 1]
                    if bs['v'][:mv] != VL:
                        raise Unsupported("known low bits of V disagree with the run")
                    Rb = bs['pos'] + 7 + 2 * mv
                    me2 = Rb - be['pos'] - 7
                    if me2 < 0 or me2 % 2:
                        raise Unsupported("V boundary misaligned")
                    me = me2 // 2
                    if bs['v'][mv:] != be['v'][me:]:
                        raise Unsupported("V rest changed")
                    mer.add(tuple(be['v'][:me]))
                if len(mer) != 1:
                    raise NeedV(f"pass {k} end low bits depend on V: r={r} {mer}")
                ves.append(list(mer.pop()))
            vend = fit_runs(ves)
            if vend is None:
                raise Unsupported("end V bits not fitted")
            st = Config(left_tokens(idx), 3, right_tokens(idx, [(b, Lin(1)) for b in VL]))
            en = Config(left_tokens(idx + 1), 3, right_tokens(idx + 1, vend))
            txt, n = G.prove_enc(M, f"{name}_p{k}", st, en, doc=f"{name}, pass {k}.", max_seg=30)
            passtext.append(txt)
            vars_ = sorted(st.vars() | en.vars())
            vin = vcur_lean()
            if all(nn.is_const() for _, nn in vend):
                VL, VLsym = runs_eval(vend, 0), None
            else:
                VLsym = vend
            vout = vcur_lean()
            st_l, en_l = cfg_lean(idx, vin), cfg_lean(idx + 1, vout)
            args = " ".join((["r"] if "r" in vars_ else []) + ["(encU X Ltop)", f"(encV {zcur} R0)"])
            body.append(f"  have e{k} : Reach {st_l} {en_l} :=")
            body.append(f"    reach_congr ({name}_p{k} {args}) (by simp only [{SIMP}]) (by simp only [{SIMP}])")
            steps_terms.append(f"e{k}")
            k += 1
            continue
        # a phase or a carry
        if VLsym is not None:
            raise Unsupported("a phase on symbolic low bits of V")
        j = idx
        m = need(idx + 1) if (idx + 1 < len(ev) and ev[idx + 1][0] == 'pass') else 0
        cs = {tuple(row['bounds'][idx + 1]['v'][:m]) for r, row in rows}
        if len(cs) != 1:
            raise NeedV(f"low bits after event {idx} depend on V")
        newVL = list(cs.pop())
        c = vval(newVL)
        vfull = vcur_lean()
        cvl, pw = vval(VL), 1 << len(VL)
        Wi = W[idx]
        hH = "Or.inl rfl" if heads[idx] == FD.HD[0] else "Or.inr rfl"
        body.append(f"  have hval{j} : val ({vfull}) = {cvl} + {pw} * val {zcur} := by simp [val_append, val] <;> omega")
        if idx == 0:
            body.append(f"  have eS : {cfg_lean(0, vfull)} = {tcfg_lean(0, vfull)} := by")
            body.append(f"    simp only [{SIMP}]")
            steps_terms.append("(Reach.of_eq eS)")
        # val v at this event, for the bound on v0
        pts = [(r, row['V0'], vval(row['bounds'][idx]['v'])) for r, row in rows]
        Ai = (pts[1][2] - pts[0][2]) // (pts[1][1] - pts[0][1])
        Bi = {}
        for (r_, V0_, vv) in pts:
            Bi.setdefault(r_, set()).add(vv - Ai * V0_)
        if any(len(x) != 1 for x in Bi.values()):
            raise Unsupported("V at an event not affine in v0")
        Bi = [Bi[r_].pop() for r_ in RS]
        if a:
            bb1 = (Bi[1] - Bi[0]) // (Qof(1) - Qof(0)); bb0 = Bi[0] - bb1
        else:
            bb1, bb0 = 0, Bi[0]
        if e[0] == 'phase':
            u = e[2]
            b_i = Wi.k
            cK = 1 << b_i
            Kexpr = f"{cK} * Q - {u + 1}" if (a and not Wi.is_const()) else f"{cK - u - 1}"
            needs.append((Ai, bb1, bb0, cK if (a and not Wi.is_const()) else 0, (0 if (a and not Wi.is_const()) else cK) - u - 1))
            if a and not Wi.is_const():
                body.append(f"  have P{j} : 2 ^ ({Wi.lean()}) = {cK} * Q := by")
                body.append(f"    rw [show {Wi.lean()} = {a} * r + {b_i} from by omega, Nat.pow_add, hQ, show 2 ^ {b_i} = {cK} from rfl, Nat.mul_comm]")
            else:
                body.append(f"  have P{j} : 2 ^ ({Wi.lean()}) = {cK} := rfl")
            body.append(f"  have hu{j} : val ({u_lean(idx)}) = {u} := by simp [val, val_append, val_replicate_false]")
            body.append(f"  obtain ⟨z{j}, st{j}, lz{j}, vz{j}⟩ := phase_split {hname(heads[idx])} ({hH}) ({u_lean(idx)}) "
                        f"({vfull}) {lx_lean(idx)} R0 ({Wi.lean()}) (by simp) ({Kexpr}) (by omega) "
                        f"(by rw [hu{j}, P{j}] <;> omega) {m} {c} (by simp) (by rw [hval{j}, show 2 ^ {m} = {1 << m} from rfl] <;> omega)")
        else:
            needs.append((Ai, bb1, bb0, 0, 1))
            cells = lx_cells(idx)
            if not cells or cells[0]:
                raise Unsupported("carry into a cell 1")
            body.append(f"  obtain ⟨z{j}, st{j}, lz{j}, vz{j}⟩ := carry_split {hname(heads[idx])} ({hH}) ({Wi.lean()}) "
                        f"({vfull}) {lx_lean(idx, 1)} R0 (by omega) {m} {c} (by simp) "
                        f"(by rw [hval{j}, show 2 ^ {m} = {1 << m} from rfl] <;> omega)")
        body.append(f"  simp only [show bitsOf {m} {c} = {lw(newVL)} from rfl, List.nil_append] at st{j}")
        body.append(f"  try simp only [List.length_append, List.length_cons, List.length_nil] at lz{j}")
        body.append(f"  rw [hval{j}, show 2 ^ {m} = {1 << m} from rfl] at vz{j}")
        steps_terms.append(f"st{j}")
        zcur = f"z{j}"
        VL = newVL
    # the end: V = (low bits) ++ z, z fitted
    endv = []
    for r, row in rows:
        vb = row['bounds'][-1]['v']
        ne = len(runs_eval(VLsym, r)) if VLsym is not None else len(VL)
        z = vb[ne:]
        endv.append((r, row['V0'], row['nv'], vval(z), len(z)))
    dl = {x[4] - x[2] for x in endv}
    if len(dl) != 1:
        raise Unsupported(f"rest length varies {dl}")
    dl = dl.pop()
    r0 = [x for x in endv if x[0] == 0]
    A = (r0[1][3] - r0[0][3]) // (r0[1][1] - r0[0][1])
    Bs = {}
    for (r, V0, nv, vz, lz) in endv:
        Bs.setdefault(r, set()).add(vz - A * V0)
    if any(len(x) != 1 for x in Bs.values()):
        raise Unsupported("rest value not affine in V0")
    Bv = [Bs[r].pop() for r in RS]
    if a:
        c1 = (Bv[1] - Bv[0]) // (Qof(1) - Qof(0))
        c0 = Bv[0] - c1 * Qof(0)
        if any(Bv[r] != c1 * Qof(r) + c0 for r in RS):
            raise Unsupported(f"rest value constant part not c1 Q + c0: {Bv}")
    else:
        if len(set(Bv)) != 1:
            raise Unsupported("constant part varies")
        c1, c0 = 0, Bv[0]
    A1, A0 = (-c1 if c1 < 0 else 0), (c0 if c0 >= 0 else 0)
    L1, L0 = (c1 if c1 > 0 else 0), (-c0 if c0 < 0 else 0)
    lhs = f"val z + {A1} * {Qe} + {L0}"
    rhs = f"{A} * val v0 + {L1} * {Qe} + {A0}"
    ln = f"z.length = v0.length + {dl}" if dl >= 0 else f"z.length + {-dl} = v0.length"
    b0 = 0
    if ticks:
        def good(b):
            for (Ai, bb1, bb0, cq, cc) in needs:
                # Ai V0 + bb1 Q + bb0 >= cq Q + cc with V0 >= 2^b Q (a > 0) or V0 >= 2^b (a = 0)
                if a:
                    co = Ai * (1 << b) + bb1 - cq
                    if co < 0 or co + bb0 - cc < 0:
                        return False
                else:
                    if Ai * (1 << b) + bb0 - cc < 0:
                        return False
            return True
        while not good(b0):
            b0 += 1
            if b0 > 60:
                raise Unsupported("no bound")
    vout = (f"{runs_lean(VLsym)} ++ z" if VLsym is not None else (f"{lw(VL)} ++ z" if VL else "z"))
    start = cfg_lean(0, (lw(list(vpre)) + " ++ v0") if vpre else "v0")
    endc = cfg_lean(nb - 1, vout)
    hv = (f" (hv : 2 ^ ({a} * r + {b0}) ≤ val v0)" if a else f" (hv : {1 << b0} ≤ val v0)") if ticks else ""
    L = [f"/-- {doc or name} -/"]
    L.append(f"theorem {name}" + (" (r : Nat)" if has_r else "") + f" (X : List Bool) (Ltop : Tape) (v0 : List Bool) (R0 : Tape){hv} :")
    L.append(f"    ∃ z : List Bool, {ln} ∧ {lhs} = {rhs} ∧")
    L.append(f"      Reach {start}")
    L.append(f"        {endc} := by")
    if ticks and a:
        L.append(f"  have hv' : {1 << b0} * {Qe} ≤ val v0 := by")
        L.append(f"    rw [show {1 << b0} = 2 ^ {b0} from rfl, ← Nat.pow_add, Nat.add_comm]; exact hv")
        L.append(f"  have hQ1 : 1 ≤ {Qe} := Nat.one_le_two_pow")
        L.append(f"  generalize hQ : {Qe} = Q at *")
    chain = steps_terms[-1]
    for t in reversed(steps_terms[:-1]):
        chain = f"{t}.trans ({chain})"
    body.append(f"  exact ⟨{zcur}, by omega, by omega, {chain}⟩")
    if not a:
        body = [x.replace("* Q", "* 1") for x in body]
    return passtext, "\n".join(L + body), dict(a=a, A=A, c1=c1, c0=c0, dl=dl, events="".join(x[0][1] for x in ev))


def generate_all(name, suf, Hi, digruns, vpre=(), depth=0, log=None):
    """generate, splitting on low bits of V (NeedV) or shifting r (other failures, the cases below the shift
    become families of their own).  Returns [(name, spec, passtext, theorem, info)]."""
    try:
        pt, thm, info = generate(name, suf, Hi, digruns, doc="", vpre=vpre)
        return [(name, (suf, Hi, digruns, tuple(vpre)), pt, thm, info)]
    except NeedV as e:
        if log: log(f"{name}: {e}; splitting on V bit {len(vpre)}")
        if len(vpre) >= 8:
            raise
        out = []
        for b in (False, True):
            out += generate_all(f"{name}_v{int(b)}", suf, Hi, digruns, tuple(vpre) + (b,), depth, log)
        return out
    except Unsupported as e:
        if depth >= 3 or all(n.is_const() for _, n in digruns):
            raise
        if log: log(f"{name}: {e}; shifting r")
        base = [(b, Lin(n.subs({"r": 0}))) for b, n in digruns]
        shifted = [(b, n + n.c.get("r", 0)) for b, n in digruns]
        bname = name + "_r0"
        return (generate_all(bname, suf, Hi, base, vpre, depth, log) +
                generate_all(name + "_s", suf, Hi, shifted, vpre, depth + 1, log))


HEAD = """import StepKit

/-!
# Steps of the walk, for every family of digits read

Written by `py/gen_all_steps.py` (families in `py/fams.py`, generator `py/gen_fam.py`, see StepKit.lean); do not edit.
Each theorem takes the walk from one clean configuration (state D on a header, `00` on its left, the unread digits
of the up-counter above a suffix, the down-counter on the right) to the next, for every rest X of the up-counter,
every run length r and every down-counter v0 above the stated bound.
-/

set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

namespace H49767
open TM

local notation "rf" => List.replicate
"""

if __name__ == "__main__":
    name = sys.argv[1]
    suf = sys.argv[2]; Hi = int(sys.argv[3])
    # digit runs: e.g. "0:1,0:1,1:2r+5"
    digruns = []
    for part in sys.argv[4].split(","):
        b, n = part.split(":")
        digruns.append((b == "1", G.S.parse_lin(n)))
    B0 = sys.argv[5] if len(sys.argv) > 5 else "0"
    pt, thm, info = generate(name, suf, Hi, digruns, doc=f"{name}")
    print(HEAD)
    for t in pt:
        print(t)
    print(thm.replace("{B0}", B0))
    print("\nend H49767")
    print(info, file=sys.stderr)
