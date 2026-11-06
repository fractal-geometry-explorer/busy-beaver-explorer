"""Generate Rework.lean: the cases of `lean/rework_cases.txt` (`py/rework.py`) as lemmas, the round function as a
`Sys` of `ReworkCore.lean`, and the wall trips of any list of blocks as two theorems, `wall_turn` and `wall_last`.

usage: python3 rework_gen.py       writes Rework.lean (tests/test_machine.py checks that it is current)

Each case is proved twice: `rw_raw_*`, its symbolic run as `symtm.prove` writes it, and `rw_*`, the same run with
the tape left of the head written as blocks (`itp`), the equalities between the two writings closed by `simp` with
the rewriting lemmas of Counter.lean and Wall.lean.  `rw_ok` collects them by cases on the mode, the separator and
the length of the block (`nat_eo`, then the small values apart).
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "py"))
import rework  # noqa: E402
from bbtools.symtm import Ctx, Lin, Rep, left_term, lin, prove, right_term, same_config, cfg_term  # noqa: E402

OUT = os.path.join(HERE, "Rework.lean")
ST = "ABCDEF"
B = {0: "false", 1: "true"}
NFL = ("simp only [itp, rep_add, rq, rep_succ, rep_zero, app_cons, app_nil, pq, rotf, rotT, mv10, rotP, pp, "
       "cons_false_blank, Nat.mul_add, Nat.add_assoc]")
NF = f"first | ({NFL}; done) | ({NFL[:-1]}, rep_swap]; done)"
NFR = ("simp only [rep_add, rpq, rep_succ, rep_zero, app_cons, app_nil, mvQ, mvQ0, mv10, mv01, cons_false_blank, "
       "Nat.mul_add, Nat.add_assoc]")
NF_R = f"first | ({NFR}; done) | ({NFR[:-1]}, rep_swap]; done)"


def _ren(toks):
    return [Ctx({"L": "X", "R": "Y"}[t.name]) if isinstance(t, Ctx) else t for t in toks]


def LT(toks):
    return left_term(_ren(toks))


def RT(toks):
    return right_term(_ren(toks))


def blist(cells):
    return "[" + ", ".join(B[c] for c in cells) + "]"


def count(n):
    """A block length in Lean, the pairs nearest the head first (`rep_add` splits it in that order): the terms in
    t, the constant, then the open block e (which lies farthest).  `4 * t` is written `2 * (2 * t)` for `rq`."""
    parts = []
    for v, a in sorted(n.c.items(), key=lambda x: x[0] == "e"):
        if v == "e":
            continue
        parts.append(v if a == 1 else f"2 * ({a // 2} * {v})" if a > 2 and a % 2 == 0 else f"{a} * {v}")
    if n.k or not parts and "e" not in n.c:
        parts.append(str(n.k))
    if "e" in n.c:
        if n.c["e"] != 1:
            raise ValueError(f"block {n}")
        parts.append("e")
    return " + ".join(parts)


def news_term(news):
    """news (far first) as a Lean list, nearest first."""
    return "[" + ", ".join(f"({B[s]}, {count(n)})" for s, n in reversed(news)) + "]"


def upat(u, var):
    """A pattern / expression for u: `t + u` (var) or the value."""
    if var:
        return "t" if u == 0 else f"t + {u}"
    return str(u)


def epat(J):
    return "e" if J == 0 else f"e + {J}"


def block(par, U):
    return f"2 * ({U})" + (" + 1" if par else "")


class Gen:
    def __init__(self, cs):
        self.cs = cs
        self.lemmas = []
        self.n = 0

    def name(self, kind):
        self.n += 1
        return f"rw_{kind}{self.n}"

    # -- raw runs
    def raw(self, name, start, fin, doc):
        vs = sorted(start.vars() | fin.vars())
        if fin.steps.is_zero():         # the case is where it starts (a turn at once)
            ctx = []
            for x in start.contexts():
                if x not in ctx:
                    ctx.append(x)
            binders = (f" ({' '.join(vs)} : Nat)" if vs else "") + (f" ({' '.join(ctx)} : Tape)" if ctx else "")
            txt = f"theorem {name}{binders} :\n    steps 0 {cfg_term(start)} = some {cfg_term(start)} := rfl\n"
            end = start
        else:
            txt, end = prove(rework.M, name, start, fin, rotate=True, max_seg=200, count_first=True)
            if not same_config(end, fin):
                raise RuntimeError(f"{name}: the run ends elsewhere")
        self.lemmas.append(txt)
        ctxs = []
        for x in start.contexts() + fin.contexts():
            if x not in ctxs:
                ctxs.append(x)
        return vs, ctxs, end

    def wrap(self, name, binders, stmt, rawname, rawargs, eqs):
        """A wrapper lemma: the raw run with the equalities `eqs` (canonical = raw) rewritten in the goal."""
        lines = [f"theorem {name} {binders} :", f"    {stmt} := by",
                 f"  have h := {rawname} {' '.join(rawargs)}"]
        rws = []
        for k, (a, b, tac) in enumerate(eqs):
            if a == b:
                continue
            lines.append(f"  have e{k} : {a} = {b} := by {tac}")
            rws.append(f"e{k}")
        if rws:
            lines.append(f"  rw [{', '.join(rws)}]")
        lines.append("  exact ⟨_, h⟩")
        self.lemmas.append("\n".join(lines) + "\n")

    # -- left cases
    def left_case(self, mi, s, par, last, u, var, out):
        cs = self.cs
        m = cs.lms[mi]
        q, lc, um = m
        start = rework.left_start(m, s, par, u, var, last)
        o, _, fin = rework.left_run(m, s, par, u, var, last)
        raw = self.name("raw_L")
        vs, ctxs, end = self.raw(raw, start, fin, None)
        U = upat(u, var)
        X = "blank" if last else "X"
        lhs = f"app {blist(lc[::-1])} (rep ({block(par, U)}) P ({X if last else f'cons {B[s]} X'}))"
        raw_l = LT(start.left)
        if out[0] == "refl":
            ri, news = out[1], out[2]
            c = cs.rms[ri][1]
            rhs_l = f"app {blist(c[::-1])} (itp {news_term(news)} {X})"
            stmt = (f"∃ k, steps k ⟨{lhs}, cons {B[um[0]]} Y, .{ST[q]}⟩ = some ⟨{rhs_l}, Y, .{ST[cs.rms[ri][0]]}⟩")
        else:
            mi2, gi = out[1], out[2]
            m2 = cs.lms[mi2]
            rhs_l = "X"
            stmt = (f"∃ k, steps k ⟨{lhs}, cons {B[um[0]]} Y, .{ST[q]}⟩ = some ⟨app [] X, "
                    f"cons {B[m2[2][0]]} (GF.T .g{gi} {'t' if var else '0'} Y), .{ST[m2[0]]}⟩")
        raw_r = LT(end.left)
        name = self.name("L")
        _KIND[name] = out[0]
        binders = ("(t : Nat) " if var else "") + ("(Y : Tape)" if last else "(X Y : Tape)")
        args = (["t"] if "t" in vs else []) + [("X" if c == "L" else "Y") for c in ctxs]
        self.wrap(name, binders, stmt, raw, args, [(lhs, raw_l, NF), (rhs_l, raw_r, NF)])
        return name

    # -- right cases
    def rx_case(self, ri, s, gi, T, var, J, out):
        cs = self.cs
        r = cs.rms[ri]
        kind, g = cs.gs[gi]
        gt = rework.subst_t(g, T, var)
        start = rework.rx_start(r, s, J, gt)
        o, _, fin = rework.rx_run(r, s, J, gt, kind)
        raw = self.name("raw_R")
        vs, ctxs, end = self.raw(raw, start, fin, None)
        Tx = upat(T, var)
        lhs = f"app {blist(r[1][::-1])} (rep ({epat(J)}) P (cons {B[s]} X))"
        raw_l = LT(start.left)
        nf0 = NF if J == 0 else f"rw [Nat.add_comm e {J}]; {NF}"
        if out[0] == "pass":
            ri2, news = out[1], out[2]
            r2 = cs.rms[ri2]
            rhs_l = f"app {blist(r2[1][::-1])} (itp {news_term(news)} X)"
            stmt = (f"∃ k, steps k ⟨{lhs}, GF.T .g{gi} ({Tx}) Y, .{ST[r[0]]}⟩ = some ⟨{rhs_l}, GF.F .g{gi} Y, "
                    f".{ST[r2[0]]}⟩")
        else:
            mi, news, gi2 = out[1], out[2], out[3]
            m = cs.lms[mi]
            rhs_l = f"app {blist(m[1][::-1])} (itp {news_term(news)} X)"
            stmt = (f"∃ k, steps k ⟨{lhs}, GF.T .g{gi} ({Tx}) Y, .{ST[r[0]]}⟩ = some ⟨{rhs_l}, "
                    f"cons {B[m[2][0]]} (GF.T .g{gi2} {'t' if var else '0'} Y), .{ST[m[0]]}⟩")
        raw_r = LT(end.left)
        name = self.name("R")
        _KIND[name] = out[0]
        binders = ("(t : Nat) " if var else "") + "(e : Nat) (X Y : Tape)"
        args = [v for v in vs] + [("X" if c == "L" else "Y") for c in ctxs]
        self.wrap(name, binders, stmt, raw, args, [(lhs, raw_l, nf0), (rhs_l, raw_r, NF)])
        return name

    # -- start cases
    def trig_case(self, tail, s, par, last, u, var, news):
        start = rework.trig_start(tail, s, par, u, var, last)
        _, _, fin = rework.trig_run(tail, s, par, u, var, last)
        raw = self.name("raw_T")
        vs, ctxs, end = self.raw(raw, start, fin, None)
        U = upat(u, var)
        Z = "blank" if last else "X"
        item = f"rep ({block(par, U)}) P (cons {B[s]} {Z})"
        lhs = (f"rep (2 * w + 2) P (cons false (rep (2 * x + 2) P (cons false (rep 1 P (cons true ({item}))))))")
        raw_l = LT(start.left)
        rhs_l = f"cons true (itp {news_term(news)} {Z})"
        raw_rl = LT(end.left)
        if tail == "turn":
            rs, tl = "W5 (cons false (cons true Y))", "cons false (cons true (cons false (cons true Y)))"
        else:
            rs, tl = "R0", "cons true (cons false (cons true blank))"
        rhs_r = f"rep (2 * x + 3) P' (cons false (rep (2 * w + 3) P' ({tl})))"
        raw_rr = RT(end.right)
        stmt = f"∃ k, steps k ⟨{lhs}, {rs}, .C⟩ = some ⟨{rhs_l}, {rhs_r}, .B⟩"
        name = self.name("T")
        binders = ("(t : Nat) " if var else "") + "(x w : Nat)" + ("" if last else " (X : Tape)") + \
            (" (Y : Tape)" if tail == "turn" else "")
        args = list(vs) + [("X" if c == "L" else "Y") for c in ctxs]
        eqs = [(lhs, raw_l, NF), (rhs_l, raw_rl, NF), (rhs_r, raw_rr, NF_R)]
        self.wrap(name, binders, stmt, raw, args, eqs)
        return name


# ---------------------------------------------------------------- the file
def lean_lm(cs):
    out = ["inductive LM where", "  " + " ".join(f"| l{i}" for i in range(len(cs.lms))), "  deriving DecidableEq", ""]
    out.append("def LM.q : LM → St")
    out += [f"  | .l{i} => .{ST[q]}" for i, (q, lc, u) in enumerate(cs.lms)]
    out.append("def LM.lc : LM → List Bool")
    out += [f"  | .l{i} => {blist(lc[::-1])}" for i, (q, lc, u) in enumerate(cs.lms)]
    out.append("def LM.u : LM → Bool")
    out += [f"  | .l{i} => {B[u[0]]}" for i, (q, lc, u) in enumerate(cs.lms)]
    out += ["", "inductive RM where", "  " + " ".join(f"| r{i}" for i in range(len(cs.rms))), "  deriving DecidableEq",
            ""]
    out.append("def RM.q : RM → St")
    out += [f"  | .r{i} => .{ST[q]}" for i, (q, c) in enumerate(cs.rms)]
    out.append("def RM.c : RM → List Bool")
    out += [f"  | .r{i} => {blist(c[::-1])}" for i, (q, c) in enumerate(cs.rms)]
    out += ["", "inductive GF where", "  " + " ".join(f"| g{i}" for i in range(len(cs.gs))), ""]
    out.append("/-- The pieces of tape right of the head, with their parameter, in front of `Y`. -/")
    out.append("def GF.T : GF → Nat → Tape → Tape")
    for i, (kind, g) in enumerate(cs.gs):
        out.append(f"  | .g{i}, {'t' if any(isinstance(x, Rep) and 't' in x.n.c for x in g) else '_'}, Y => "
                   f"{right_term(list(g) + [Ctx('Y')])}")
    out.append("/-- The tape right of the head when a crossing of the piece ends. -/")
    out.append("def GF.F : GF → Tape → Tape")
    for i, (kind, g) in enumerate(cs.gs):
        f = {"lv": "cons true (cons false Y)", "g": "Y", "ft": "Y",
             "fl": "cons false (cons true (cons false (cons false (cons false (cons false Y)))))"}[kind]
        out.append(f"  | .g{i}, Y => {f}")
    return out


def text():
    """The content of Rework.lean."""
    cs = rework.Cases.load()
    gen = Gen(cs)
    # left cases: rows of leftP / lastP, and the proof rows
    left_rows, last_rows, rx_rows, trig_rows = [], [], [], {"turn": [], "last": []}
    left_proof, last_proof, rx_proof, trig_proof = {}, {}, {}, {"turn": {}, "last": {}}

    def louts(o, var):
        if o[0] == "refl":
            return f".refl .r{o[1]} {news_term(o[2])}"
        return f".cont .l{o[1]} .g{o[2]} {'t' if var else '0'}"

    for (mi, s, par, last), e in sorted(cs.left.items()):
        rows, proof = [], []
        for u, o in sorted(e["con"].items()):
            if o is None:
                continue
            nm = gen.left_case(mi, s, par, last, u, False, o)
            rows.append((str(u), louts(o, False)))
            proof.append((str(u), nm))
        if e["gen"] is not None:
            nm = gen.left_case(mi, s, par, last, e["off"], True, e["gen"])
            rows.append((upat(e["off"], True), louts(e["gen"], True)))
            proof.append((upat(e["off"], True), nm))
        key = (mi, s, par) if not last else (mi, par)
        (last_rows if last else left_rows).append((key, rows))
        (last_proof if last else left_proof)[key] = (proof, e["off"] if e["gen"] is not None else None)

    def routs(o, var):
        if o[0] == "pass":
            return f".pass .r{o[1]} {news_term(o[2])}"
        return f".bounce .l{o[1]} {news_term(o[2])} .g{o[3]} {'t' if var else '0'}"

    for (ri, s, gi), e in sorted(cs.rx.items()):
        rows, proof = [], []
        for T, (J, o) in sorted(e["con"].items()):
            nm = gen.rx_case(ri, s, gi, T, False, J, o)
            rows.append((str(T), J, routs(o, False)))
            proof.append((str(T), J, nm))
        if e["gen"] is not None:
            J, o = e["gen"]
            nm = gen.rx_case(ri, s, gi, e["t0"], True, J, o)
            rows.append((upat(e["t0"], True), J, routs(o, True)))
            proof.append((upat(e["t0"], True), J, nm))
        rx_rows.append(((ri, s, gi), rows))
        rx_proof[(ri, s, gi)] = (proof, e["t0"] if e["gen"] is not None else None)

    for (tail, s, par, last), e in sorted(cs.trig.items()):
        rows, proof = [], []
        for u, news in sorted(e["con"].items()):
            nm = gen.trig_case(tail, s, par, last, u, False, news)
            rows.append((str(u), news_term(news)))
            proof.append((str(u), nm))
        if e["gen"] is not None:
            nm = gen.trig_case(tail, s, par, last, e["off"], True, e["gen"])
            rows.append((upat(e["off"], True), news_term(e["gen"])))
            proof.append((upat(e["off"], True), nm))
        trig_rows[tail].append(((s, par, last), rows))
        trig_proof[tail][(s, par, last)] = (proof, e["off"] if e["gen"] is not None else None)

    out = [HEADER, "namespace BB6e", "open TM", "", "namespace RW", ""]
    out += lean_lm(cs)
    out.append("")
    # functions
    out.append("/-- A block `(s, 2u + par)` with more blocks to its left, in a left mode. -/")
    out.append("def leftP : LM → Bool → Nat → Nat → LRes LM RM GF")
    for (mi, s, par), rows in left_rows:
        for U, val in rows:
            out.append(f"  | .l{mi}, {B[s]}, {par}, {U} => {val}")
    out += ["  | _, _, _, _ => .stuck", ""]
    out.append("/-- The last block `(false, 2u + par)`, on blank tape. -/")
    out.append("def lastP : LM → Nat → Nat → LRes LM RM GF")
    for (mi, par), rows in last_rows:
        for U, val in rows:
            out.append(f"  | .l{mi}, {par}, {U} => {val}")
    out += ["  | _, _, _ => .stuck", ""]
    out.append("/-- A piece with its parameter, over the nearest block `(s, E)`, from a right mode. -/")
    out.append("def rxC : RM → Bool → GF → Nat → Nat → XRes LM RM GF")
    for (ri, s, gi), rows in rx_rows:
        for T, J, val in rows:
            out.append(f"  | .r{ri}, {B[s]}, .g{gi}, {T}, {epat(J)} => {val}")
    out += ["  | _, _, _, _, _ => .stuck", ""]
    out += [SYS, ""]
    out += gen.lemmas
    out += [ok_proof(cs, left_proof, last_proof, rx_proof)]
    # trig
    for tail in ("turn", "last"):
        out.append(f"/-- The start of a wall trip ({tail}): the blocks replacing the first one, `(s, 2u + par)` (last: the "
                   f"last block). -/")
        out.append(f"def trigP_{tail} : Bool → Bool → Nat → Nat → Option (List Item)")
        for (s, par, last), rows in trig_rows[tail]:
            for U, val in rows:
                out.append(f"  | {B[s]}, {B[last]}, {par}, {U} => some {val}")
        out += ["  | _, _, _, _ => none", ""]
    out.append(TAIL.replace("TRIGPROOF_turn", trig_ok(trig_proof["turn"], "turn"))
               .replace("TRIGPROOF_last", trig_ok(trig_proof["last"], "last")))
    out += ["end RW", "", "end BB6e", ""]
    return "\n".join(out), gen.n


def main():
    src, n = text()
    with open(OUT, "w") as f:
        f.write(src)
    print(f"wrote {OUT}: {n} lemmas")


def u_cases(proof, off, indent, exact):
    """Tactic `match u with` over the rows of one (mode, sep, parity): each row's lemma, `trivial` elsewhere."""
    pats = {p: nm for p, nm in proof}
    lit = sorted(int(p) for p in pats if p.isdigit())
    top = (off if off is not None else (max(lit) + 1 if lit else 0))
    lines = [f"{indent}match u with"]
    for v in range(top):
        lines.append(f"{indent}| {v} => " + (exact(pats[str(v)], False) if str(v) in pats else "exact trivial"))
    if off is not None:
        lines.append(f"{indent}| {upat(off, True)} => " + exact(pats[upat(off, True)], True))
    else:
        lines.append(f"{indent}| {'t' if top == 0 else f't + {top}'} => exact trivial")
    return lines


def ok_proof(cs, left_proof, last_proof, rx_proof):
    L = ["theorem rw_ok : sys.Ok where", "  left := by", "    intro m s b X Y",
         "    obtain ⟨u, rfl | rfl⟩ := nat_eo b"]
    for par in (0, 1):
        bexp = "2 * u" if par == 0 else "2 * u + 1"
        L += [f"    · have hb : sys.leftC m s ({bexp}) = leftP m s {par} u := by",
              f"        show leftP m s (({bexp}) % 2) (({bexp}) / 2) = _",
              f"        rw [show ({bexp}) % 2 = {par} by omega, show ({bexp}) / 2 = u by omega]",
              "      rw [hb]", "      cases m <;> cases s"]
        for mi in range(len(cs.lms)):
            for s in (0, 1):
                key = (mi, s, par)
                L.append(f"      case l{mi}.{B[s]} =>")
                if key not in left_proof:
                    L.append("        exact trivial")
                    continue
                proof, off = left_proof[key]
                ex = lambda nm, var: (f"exact {nm} {'t ' if var else ''}X Y" if cs_left_refl(cs, nm) else
                                      f"exact ⟨fun _ => rfl, {nm} {'t ' if var else ''}X Y⟩")
                L += u_cases(proof, off, "        ", ex)
    L += ["  last := by", "    intro m b Y", "    obtain ⟨u, rfl | rfl⟩ := nat_eo b"]
    for par in (0, 1):
        bexp = "2 * u" if par == 0 else "2 * u + 1"
        L += [f"    · have hb : sys.lastC m ({bexp}) = lastP m {par} u := by",
              f"        show lastP m (({bexp}) % 2) (({bexp}) / 2) = _",
              f"        rw [show ({bexp}) % 2 = {par} by omega, show ({bexp}) / 2 = u by omega]",
              "      rw [hb]", "      cases m"]
        for mi in range(len(cs.lms)):
            key = (mi, par)
            L.append(f"      case l{mi} =>")
            if key not in last_proof:
                L.append("        exact trivial")
                continue
            proof, off = last_proof[key]
            L += u_cases(proof, off, "        ", lambda nm, var: f"exact {nm} {'t ' if var else ''}Y")
    L += ["  rx := by", "    intro r s g T E X Y", "    cases r <;> cases s <;> cases g"]
    for (ri, s, gi), (proof, t0) in sorted(rx_proof.items()):
        L.append(f"    case r{ri}.{B[s]}.g{gi} =>")
        L.append("      match T, E with")
        pats = {p: (J, nm) for p, J, nm in proof}
        lit = sorted(int(p) for p in pats if p.isdigit())
        top = t0 if t0 is not None else (max(lit) + 1 if lit else 0)
        trows = [(str(v), False) for v in range(top)] + [(upat(top, True), True)]
        for p, var in trows:
            if p in pats and (not var or t0 is not None):
                J, nm = pats[p]
                for v in range(J):
                    L.append(f"      | {p}, {v} => exact trivial")
                ex = (f"exact {nm} {'t ' if var else ''}e X Y" if cs_rx_pass(cs, nm) else
                      f"exact ⟨fun _ => rfl, {nm} {'t ' if var else ''}e X Y⟩")
                L.append(f"      | {p}, e => " + ex if J == 0 else f"      | {p}, e + {J} => " + ex)
            else:
                L.append(f"      | {p}, _ => exact trivial")
    L.append("    all_goals exact trivial")
    return "\n".join(L) + "\n"


_KIND = {}


def cs_left_refl(cs, nm):
    return _KIND.get(nm) == "refl"


def cs_rx_pass(cs, nm):
    return _KIND.get(nm) == "pass"


def trig_ok(proof, tail):
    """trigT_ok / trigL_ok: cases on the first block."""
    T = "T" if tail == "turn" else "L"
    if tail == "turn":
        rs = "W5 (cons false (cons true Y))"
        tl = "cons false (cons true (cons false (cons true Y)))"
        binders = "(x w : Nat) (Y : Tape)"
    else:
        rs, tl, binders = "R0", "cons true (cons false (cons true blank))", "(x w : Nat)"
    L = [f"theorem trig{T}_ok (L L1 : List Item) (h : trig{T} L = some L1) {binders} :",
         "    ∃ k, steps k ⟨rep (2 * w + 2) P (cons false (rep (2 * x + 2) P (cons false (rep 1 P (cons true "
         "(itp L blank)))))),",
         f"        {rs}, .C⟩",
         f"      = some ⟨cons true (itp L1 blank), rep (2 * x + 3) P' (cons false (rep (2 * w + 3) P' ({tl}))), .B⟩ := by",
         "  match L, h with",
         f"  | [], h => simp [trig{T}] at h",
         f"  | [(true, b)], h => simp [trig{T}] at h"]
    yarg = " Y" if tail == "turn" else ""
    for last in (True, False):
        if last:
            L.append("  | [(false, b)], h =>")
        else:
            L.append("  | (s, b) :: x' :: L, h =>")
        L.append("    obtain ⟨u, rfl | rfl⟩ := nat_eo b")
        for par in (0, 1):
            bexp = "2 * u" if par == 0 else "2 * u + 1"
            if last:
                L += [f"    · rw [show trig{T} [(false, {bexp})] = trigP_{tail} false true {par} u by",
                      f"        show trigP_{tail} false true (({bexp}) % 2) (({bexp}) / 2) = _",
                      f"        rw [show ({bexp}) % 2 = {par} by omega, show ({bexp}) / 2 = u by omega]] at h"]
                svals = [0]
            else:
                L += ["    · cases s"]
                svals = [0, 1]
            for s in svals:
                ind = "      " if last else "      · "
                ind2 = "      " if last else "        "
                if not last:
                    sb = "true" if s else "false"
                    L += [f"      · rw [show trig{T} (({sb}, {bexp}) :: x' :: L) = (trigP_{tail} {sb} false {par} u).map "
                          "(· ++ x' :: L) by",
                          f"          show (trigP_{tail} {sb} false (({bexp}) % 2) (({bexp}) / 2)).map (· ++ x' :: L) = _",
                          f"          rw [show ({bexp}) % 2 = {par} by omega, show ({bexp}) / 2 = u by omega]] at h"]
                    ind = "        "
                    ind2 = "        "
                key = (s, par, last)
                rows, off = proof.get(key, ([], None))
                pats = {p: nm for p, nm in rows}
                lit = sorted(int(p) for p in pats if p.isdigit())
                top = off if off is not None else (max(lit) + 1 if lit else 0)
                lines = [f"match u, h with"]
                trows = [(str(v), False) for v in range(top)] + [(upat(top, True), True)]
                for p, var in trows:
                    if p in pats and (not var or off is not None):
                        nm = pats[p]
                        args = ("t " if var else "") + "x w" + ("" if last else " (itp (x' :: L) blank)") + yarg
                        if last:
                            lines.append(f"| {p}, h => simp only [trigP_{tail}, Option.some.injEq] at h; subst h; "
                                         f"exact {nm} {args}")
                        else:
                            lines.append(f"| {p}, h => simp only [trigP_{tail}, Option.map_some, Option.some.injEq] "
                                         f"at h; subst h; rw [itp_append]; exact {nm} {args}")
                    else:
                        lines.append(f"| {p}, h => simp [trigP_{tail}] at h")
                L.append(ind + lines[0])
                L += [ind2 + ln for ln in lines[1:]]
    return "\n".join(L) + "\n"


HEADER = '''import ReworkCore

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! # Wall trips of any list of blocks

Generated by `rework_gen.py` from `rework_cases.txt` (`py/rework.py`); do not edit by hand.

The cases of the rounds of a wall trip (`py/rework.py`): left modes `LM`, right modes `RM`, pieces of tape `GF`, and
what each mode does at a block or a piece (`leftP`, `lastP`, `rxC`), each proved by its symbolic run (`rw_L*`,
`rw_R*`; `rw_ok`).  With `Sys.go_ok` of ReworkCore.lean that gives a round of the copy loop and the work before it
for any list of blocks (`round_ok`), all rounds (`iter_ok`), and with the start (`rw_T*`) and the end, the whole
trip: `wall_turn` (a trip after the counter's walk, through `counter_borrow_ex`) and `wall_last`. -/
'''

SYS = '''theorem rotT (n : Nat) (s : Tape) : rep n Q' (cons true s) = cons true (rep n Q s) := (mvQ0 n s).symm
theorem rotP (n : Nat) (s : Tape) : rep n P' (cons true s) = cons true (rep n P s) := (mv01 n s).symm
theorem pp (n : Nat) (s : Tape) : cons false (cons true (rep n P s)) = rep n P (cons false (cons true s)) :=
  rep_rotate n P P P rfl s

def leftC (m : LM) (s : Bool) (b : Nat) : LRes LM RM GF := leftP m s (b % 2) (b / 2)
def lastC (m : LM) (b : Nat) : LRes LM RM GF := lastP m (b % 2) (b / 2)

/-- The cases as a `Sys`. -/
def sys : Sys where
  LM := LM
  RM := RM
  GF := GF
  lq := LM.q
  llc := LM.lc
  lu := LM.u
  rq := RM.q
  rc := RM.c
  gT := GF.T
  gF := GF.F
  leftC := leftC
  lastC := lastC
  rxC := rxC'''

TAIL = '''/-- One round from a turn: the list at the next turn. -/
def round (n : Nat) (L : List Item) : Option (List Item) :=
  match sys.go n (.sw .l0 L) with
  | some (r, L1) =>
    match sys.go n (.rx r .g0 0 L1) with
    | some (.r0, L2) => some L2
    | _ => none
  | none => none

theorem round_ok (n : Nat) (L L' : List Item) (h : round n L = some L') (x : Nat) (Y : Tape) :
    ∃ k, steps k ⟨cons true (itp L blank), rep (x + 2) P' Y, .B⟩
      = some ⟨cons true (itp L' blank), rep (x + 1) P' Y, .B⟩ := by
  unfold round at h
  cases h1 : sys.go n (.sw .l0 L) with
  | none => simp [h1] at h
  | some p =>
    obtain ⟨r, L1⟩ := p
    simp only [h1] at h
    cases h2 : sys.go n (.rx r .g0 0 L1) with
    | none => simp [h2] at h
    | some p2 =>
      obtain ⟨rr, L2⟩ := p2
      simp only [h2] at h
      cases rr <;> simp at h
      subst h
      obtain ⟨k1, hk1⟩ := sys.go_ok rw_ok n _ r L1 h1 (GF.T .g0 0 (rep x P' Y))
      obtain ⟨k2, hk2⟩ := sys.go_ok rw_ok n _ .r0 L2 h2 (rep x P' Y)
      have h0 : steps 1 ⟨cons true (itp L blank), rep (x + 2) P' Y, .B⟩
          = some ⟨itp L blank, cons true (GF.T .g0 0 (rep x P' Y)), .B⟩ := rfl
      exact ⟨_, steps_seq trans h0 (steps_seq trans hk1 hk2)⟩

/-- `k` rounds, from a turn with a level of `k + 1` pairs to the turn with one pair. -/
def iter (n : Nat) : Nat → List Item → Option (List Item)
  | 0, L => some L
  | k + 1, L =>
    match round n L with
    | some L' => iter n k L'
    | none => none

theorem iter_ok (n : Nat) : ∀ k L L', iter n k L = some L' → ∀ Y : Tape,
    ∃ m, steps m ⟨cons true (itp L blank), rep (k + 1) P' Y, .B⟩ = some ⟨cons true (itp L' blank), rep 1 P' Y, .B⟩ := by
  intro k
  induction k with
  | zero => intro L L' h Y; simp only [iter, Option.some.injEq] at h; subst h; exact ⟨0, rfl⟩
  | succ k ih =>
    intro L L' h Y
    simp only [iter] at h
    cases h1 : round n L with
    | none => simp [h1] at h
    | some L1 =>
      simp only [h1] at h
      obtain ⟨m1, hm1⟩ := round_ok n L L1 h1 k Y
      obtain ⟨m2, hm2⟩ := ih L1 L' h Y
      exact ⟨_, steps_seq trans hm1 hm2⟩

/-- The end of a wall trip from the turn with one pair: the sweeps that make every separator a 1, the head at the
right. -/
def fin (n : Nat) (g : GF) (w : Nat) (L : List Item) : Option (List Item) :=
  match sys.go n (.sw .l0 L) with
  | some (r, L1) =>
    match sys.go n (.rx r g (2 * w + 3) L1) with
    | some (.r1, L2) => some L2
    | _ => none
  | none => none

theorem fin_turn_ok (n w : Nat) (L L' : List Item) (h : fin n .g1 w L = some L') (R : Tape) :
    ∃ k, steps k ⟨cons true (itp L blank),
        rep 1 P' (cons false (rep (2 * w + 3) P' (cons false (cons true (cons false (cons true R)))))), .B⟩
      = some ⟨itp L' blank, R, .C⟩ := by
  unfold fin at h
  cases h1 : sys.go n (.sw .l0 L) with
  | none => simp [h1] at h
  | some p =>
    obtain ⟨r, L1⟩ := p
    simp only [h1] at h
    cases h2 : sys.go n (.rx r .g1 (2 * w + 3) L1) with
    | none => simp [h2] at h
    | some p2 =>
      obtain ⟨rr, L2⟩ := p2
      simp only [h2] at h
      cases rr <;> simp at h
      subst h
      obtain ⟨k1, hk1⟩ := sys.go_ok rw_ok n _ r L1 h1 (GF.T .g1 (2 * w + 3) R)
      obtain ⟨k2, hk2⟩ := sys.go_ok rw_ok n _ .r1 L2 h2 R
      have h0 : steps 1 ⟨cons true (itp L blank),
          rep 1 P' (cons false (rep (2 * w + 3) P' (cons false (cons true (cons false (cons true R)))))), .B⟩
          = some ⟨itp L blank, cons true (GF.T .g1 (2 * w + 3) R), .B⟩ := rfl
      exact ⟨_, steps_seq trans h0 (steps_seq trans hk1 hk2)⟩

theorem fin_last_ok (n w : Nat) (L L' : List Item) (h : fin n .g2 w L = some L') :
    ∃ k, steps k ⟨cons true (itp L blank),
        rep 1 P' (cons false (rep (2 * w + 3) P' (cons true (cons false (cons true blank))))), .B⟩
      = some ⟨itp L' blank, R0, .C⟩ := by
  unfold fin at h
  cases h1 : sys.go n (.sw .l0 L) with
  | none => simp [h1] at h
  | some p =>
    obtain ⟨r, L1⟩ := p
    simp only [h1] at h
    cases h2 : sys.go n (.rx r .g2 (2 * w + 3) L1) with
    | none => simp [h2] at h
    | some p2 =>
      obtain ⟨rr, L2⟩ := p2
      simp only [h2] at h
      cases rr <;> simp at h
      subst h
      obtain ⟨k1, hk1⟩ := sys.go_ok rw_ok n _ r L1 h1 (GF.T .g2 (2 * w + 3) blank)
      obtain ⟨k2, hk2⟩ := sys.go_ok rw_ok n _ .r1 L2 h2 blank
      have e1 : GF.T .g2 (2 * w + 3) blank
          = cons false (cons false (cons false (rep (2 * w + 3) P' (cons true (cons false (cons true blank)))))) := by
        simp only [GF.T, cons_false_blank]
      have e2 : sys.gF (GF.g2 : sys.GF) blank = R0 := by show GF.F .g2 blank = R0; simp only [GF.F, cons_false_blank]
      have h0 : steps 1 ⟨cons true (itp L blank),
          rep 1 P' (cons false (rep (2 * w + 3) P' (cons true (cons false (cons true blank))))), .B⟩
          = some ⟨itp L blank, cons true (GF.T .g2 (2 * w + 3) blank), .B⟩ := by rw [e1]; rfl
      simp only [Sys.Task.fin] at hk2
      rw [e2] at hk2
      exact ⟨_, steps_seq trans h0 (steps_seq trans hk1 hk2)⟩

/-- The start of a wall trip: the first block replaced by the blocks of the first turn. -/
def trigT (L : List Item) : Option (List Item) :=
  match L with
  | [(false, b)] => trigP_turn false true (b % 2) (b / 2)
  | (s, b) :: x :: L => (trigP_turn s false (b % 2) (b / 2)).map (· ++ x :: L)
  | _ => none

def trigL (L : List Item) : Option (List Item) :=
  match L with
  | [(false, b)] => trigP_last false true (b % 2) (b / 2)
  | (s, b) :: x :: L => (trigP_last s false (b % 2) (b / 2)).map (· ++ x :: L)
  | _ => none

TRIGPROOF_turn
TRIGPROOF_last
/-- A wall trip after the counter's walk: the tape left of `0 1 1` at its end. -/
def endT : List Item → Option (List Item)
  | (true, 1) :: (s, b + 1) :: L3 => some ((s, b + 1) :: L3)
  | _ => none

def wallT (n : Nat) (L : List Item) (x w : Nat) : Option (List Item) :=
  match trigT L with
  | some L1 =>
    match iter n (2 * x + 2) L1 with
    | some L2 =>
      match fin n .g1 w L2 with
      | some L4 => endT L4
      | none => none
    | none => none
  | none => none

/-- A wall trip after the counter's walk, for any list of blocks `L` the function covers: the whole trip from the right
end and back, with the levels the walk crosses any list `zs`, as `counter_borrow_ex`. -/
theorem wall_turn (n : Nat) (L : List Item) (x w : Nat) (L' : List Item) (h : wallT n L x w = some L')
    (c d : Nat) (zs : List (Nat × Nat)) :
    ∃ k, steps k ⟨lv false false (2 * c + 2) (2 * d + 2)
        (Zs zs (app Q (rep (2 * w + 2) P (cons false (rep (2 * x + 2) P (cons false (rep 1 P (cons true
          (itp L blank))))))))), R0, .C⟩
      = some ⟨lv true true (2 * c + 3) (2 * d + 3) (Rs zs (itp L' blank)), R0, .C⟩ := by
  unfold wallT at h
  cases h1 : trigT L with
  | none => simp [h1] at h
  | some L1 =>
    simp only [h1] at h
    cases h2 : iter n (2 * x + 2) L1 with
    | none => simp [h2] at h
    | some L2 =>
      simp only [h2] at h
      cases h3 : fin n .g1 w L2 with
      | none => simp [h3] at h
      | some L4 =>
        simp only [h3] at h
        unfold endT at h
        split at h
        · rename_i s b L3
          simp only [Option.some.injEq] at h
          subst h
          refine counter_borrow_ex c d zs (fun R => ?_) ⟨_, rfl⟩
          obtain ⟨k1, hk1⟩ := trigT_ok L L1 h1 x w R
          obtain ⟨k2, hk2⟩ := iter_ok n (2 * x + 2) L1 L2 h2
            (cons false (rep (2 * w + 3) P' (cons false (cons true (cons false (cons true R))))))
          obtain ⟨k3, hk3⟩ := fin_turn_ok n w L2 _ h3 R
          exact ⟨_, steps_seq trans hk1 (steps_seq trans hk2 hk3)⟩
        · simp at h

def wallL (n : Nat) (L : List Item) (x w : Nat) : Option (List Item) :=
  match trigL L with
  | some L1 =>
    match iter n (2 * x + 2) L1 with
    | some L2 => fin n .g2 w L2
    | none => none
  | none => none

/-- A wall trip that is the whole trip from the right end (no walk), for any list of blocks `L` the function
covers. -/
theorem wall_last (n : Nat) (L : List Item) (x w : Nat) (L' : List Item) (h : wallL n L x w = some L') :
    ∃ k, steps k ⟨rep (2 * w + 2) P (cons false (rep (2 * x + 2) P (cons false (rep 1 P (cons true
        (itp L blank)))))), R0, .C⟩ = some ⟨itp L' blank, R0, .C⟩ := by
  unfold wallL at h
  cases h1 : trigL L with
  | none => simp [h1] at h
  | some L1 =>
    simp only [h1] at h
    cases h2 : iter n (2 * x + 2) L1 with
    | none => simp [h2] at h
    | some L2 =>
      simp only [h2] at h
      obtain ⟨k1, hk1⟩ := trigL_ok L L1 h1 x w
      obtain ⟨k2, hk2⟩ := iter_ok n (2 * x + 2) L1 L2 h2
        (cons false (rep (2 * w + 3) P' (cons true (cons false (cons true blank)))))
      obtain ⟨k3, hk3⟩ := fin_last_ok n w L2 L' h
      exact ⟨_, steps_seq trans hk1 (steps_seq trans hk2 hk3)⟩
'''

if __name__ == "__main__":
    main()
