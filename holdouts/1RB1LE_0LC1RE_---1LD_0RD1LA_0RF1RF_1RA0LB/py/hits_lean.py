"""Writes lean/Hits.lean: whole hits on a level, composed from the stretch theorems of lean/Levels.lean.

For every position p of the table (accel.CYC) one theorem `hit<p>`: a hit on the level `W p j Y` (j + 1 blocks, rest
Y) is a hit in the sense of lean/Odo.lean, takes LA[p] (j + 1) + LB[p] steps inside the level and leaves the level at
the next position; at the six passing positions the rest gets a hit, given as a hypothesis.  `level_hit` collects
them.  Then the same for a hit that does not come back (`halt<p>_<kind>`, `level_halt`, the table `haltTab`): the
rest's first call halts (HC) or the fourth call of its H-hit halts (H4).  Last, the front: `frontH`, `frontV` (a
hit and the bounce visit, 107 and 83 steps outside the rest) and the halting forms.

The script reads the statements of Levels.lean (the stretches and their step counts), follows the machine's table
for the single steps between a stretch and a call on the rest, and checks the tape words it writes against
accel.py's tables; Lean checks everything again.

usage: python3 hits_lean.py > ../lean/Hits.lean
"""
import os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from accel import CYC, PASS, INC, SEPW, SIG, LA, LB, PART, FC, FP, FRONT
from words import CELLS, TABLE

HERE = os.path.dirname(os.path.abspath(__file__))
ST = "ABCDEF"
BLOCK = "1111111110"


def wcells(w):
    return "".join(str(CELLS[ch][1]) + str(CELLS[ch][0]) for ch in w)


def blist(s):
    return "[" + ", ".join("true" if c == "1" else "false" for c in s) + "]"


def comp(t):
    t = t.replace("cons true (", "1").replace("cons false (", "0").replace("true", "1").replace("false", "0")
    return re.sub(r"[(), ]", "", t)


def parse_levels():
    """name -> dict(doc, a, b (steps a j + b), left0, right0, q0, left1, right1, q1) with compact tape strings"""
    s = open(os.path.join(HERE, "../lean/Levels.lean")).read()
    out = {}
    for m in re.finditer(r"/-- (.*?) -/\ntheorem (lev\w+) \(j : Nat\) \(L R : Tape\) :\n\s+steps \((.*?)\) ⟨(.*?), "
                         r"(cons.*?|R), \.(\w)⟩ = some ⟨(.*?), (cons.*?|R), \.(\w)⟩ := by", s):
        doc, name, cnt, l0, r0, q0, l1, r1, q1 = m.groups()
        mm = re.fullmatch(r"(?:(\d+) \* j \+ )?(\d+)", cnt)
        out[name] = dict(doc=doc, a=int(mm.group(1) or 0), b=int(mm.group(2)), l0=comp(l0), r0=comp(r0), q0=q0,
                         l1=comp(l1), r1=comp(r1), q1=q1)
    return out


LEV = parse_levels()


def calls(sig):
    return [(sig[i + 1], sig[i + 3]) for i in range(0, len(sig), 4)]


def structure(pos):
    """the from-above calls of a hit at pos: a list (q_in, q_out, items); an item is ("lev", name) or
    ("rest", k, q, x, w, q2, r2): a single step in state q on the symbol x (write w, left, to q2) that starts call k
    on the rest, which returns in r2"""
    t = CYC[pos][1]
    rest_calls = calls(SIG[PASS[pos]]) if pos in PASS else []
    names = sorted((n for n in LEV if n.startswith("lev%d_" % pos)), key=lambda n: int(n.split("_")[1]))
    out, i, k = [], 0, 0
    for ci, (qi, qo) in enumerate(calls(SIG[t])):
        items = []
        d = LEV[names[i]]
        assert d["doc"].split(", ", 2)[2].startswith("call %d from above (in %s)" % (ci + 1, qi)), (pos, names[i])
        while True:
            d = LEV[names[i]]
            items.append(("lev", names[i]))
            i += 1
            if d["r1"] == "R":
                assert d["q1"] == qo
                break
            # the head is on the level's leftmost cell (the first cell of the right tape), the rest is L
            q, x = d["q1"], int(d["r1"][0])
            while True:
                w, mv, q2 = TABLE[ST.index(q), x]
                assert mv == -1 and ST[q2] == rest_calls[k][0], (pos, names[i - 1])
                r2 = rest_calls[k][1]
                items.append(("rest", k + 1, q, x, w, ST[q2], r2))
                k += 1
                # after the return: head on the same cell (now w) in r2; is there a stretch theorem from here?
                nd = LEV.get(names[i]) if i < len(names) else None
                if nd and "after call %d on the rest has returned (in %s)" % (k, r2) in nd["doc"]:
                    break
                q, x = r2, w            # no stretch: the head steps back onto the rest at once
        out.append((qi, qo, items))
    assert i == len(names) and k == len(rest_calls), pos
    return out


def split_rep(s):
    m = re.fullmatch(r"([01]*)repj\[([01]+)\]([01]*)L", s)
    return m.groups()


def end_eq(pos, lsub_bits):
    """the proof term of  W p' j' Y' = 1^g ++ (final left tape): a rotation of the repeated block.  lsub_bits: the
    known first cells of the theorems' L after the hit (1 for a passing level, whose rest ends with its own 1s)"""
    t = CYC[pos][1]
    names = sorted((n for n in LEV if n.startswith("lev%d_" % pos)), key=lambda n: int(n.split("_")[1]))
    pre, w, post = split_rep(LEV[names[-1]]["l1"])
    pre = "1" * (2 if t == "H" else 6) + pre
    k = [k for k in range(10) if BLOCK[k:] + BLOCK[:k] == w]
    assert len(k) == 1
    a = BLOCK[:k[0]]
    assert pre.endswith(a)
    pre0 = pre[:len(pre) - len(a)]
    inc = 1 if pos in INC else 0
    assert pre0 == BLOCK, (pos, pre0)
    p2 = (pos + 1) % 16
    give = "" if pos not in PASS else "1" * (3 if PASS[pos] == "H" else 7)
    assert a + post + lsub_bits == BLOCK * inc + wcells(SEPW[CYC[p2][0]]) + give, (pos, a, post)
    rot = "congrArg (app blockW) (rep_rotate j %s %s blockW rfl _).symm" % (blist(a), blist(w))
    if inc:           # the new block stands behind the repeat
        return "(congrArg (app blockW) (rep_app_comm j blockW _).symm).trans (%s)" % rot
    return rot


def chain(items, j, subst, last=None):
    """nested steps_seq of the items of a call; subst[k] = name of the rest's tape before call k+1 (U0, U1, ...).
    With last = (k, wrap): stop at the rest's call k, which halts (HaltsIn.seq ... via_halt)."""
    terms, cur, cnt_a, cnt_b = [], 0, 0, 0
    for it in items:
        if it[0] == "lev":
            d = LEV[it[1]]
            L = "Y" if subst is None else "(cons true U%d)" % cur
            terms.append(("%s j %s R" % (it[1], L)))
            cnt_a += d["a"]; cnt_b += d["b"]
        else:
            _, k, q, x, w, q2, r2 = it
            args = "(q := .%s) (x := %s) (w := %s) (q2 := .%s)" % (q, "true" if x else "false",
                                                                 "true" if w else "false", q2)
            cnt_b += 1
            if last and k == last:
                terms.append("via_halt %s rfl hc _" % args)
                break
            terms.append("via_call %s rfl c%d _" % (args, k))
            cur = k
    else:
        assert not last
    if last:
        t = terms[-1]
        for x in reversed(terms[:-1]):
            t = "HaltsIn.seq (%s) (%s)" % (x, t)
    else:
        t = terms[-1]
        for x in reversed(terms[:-1]):
            t = "steps_seq trans (%s) (%s)" % (x, t)
    return t, cnt_a, cnt_b


def hit_thm(pos):
    s, t = CYC[pos]
    p2 = (pos + 1) % 16
    inc = " + 1" if pos in INC else ""
    st = structure(pos)
    cost = "%d * (j + 1) + %d" % (LA[pos], LB[pos])
    doc = "/-- A hit at position %d (separator %s, %s-hit)" % (pos, s, t)
    if pos not in PASS:
        head = "%s: absorbed. -/\ntheorem hit%d (j : Nat) (Y : Tape) : Hit%s (W %d j Y) (W %d (j%s) Y) (%s) := by\n" % (
            doc, pos, t, pos, p2, inc, cost)
        subst, pre, lsub = None, "", ""
    else:
        k = PASS[pos]
        head = ("%s: the rest gets %s %s-hit. -/\ntheorem hit%d (j : Nat) {Y Y' : Tape} {m : Nat} (h : Hit%s Y Y' m) :\n"
                "    Hit%s (W %d j Y) (W %d (j%s) Y') (%s + m) := by\n" % (
                    doc, "an" if k == "H" else "a", k, pos, k, t, pos, p2, inc, cost))
        subst = True
        lsub = "1"
        if k == "H":
            pre = "  obtain ⟨U0, U1, U2, U3, U4, U5, m1, m2, m3, m4, m5, rfl, c1, c2, c3, c4, c5, rfl, rfl⟩ := h\n"
        else:
            pre = "  obtain ⟨U0, U1, rfl, c1, rfl⟩ := h\n"
    cs = []
    for qi, qo, items in st:
        if len(items) == 1:
            cs.append("fun R => %s j _ R" % items[0][1])
        else:
            cs.append("fun R => " + chain(items, "j", subst)[0])
    eq = end_eq(pos, lsub)
    if t == "H":
        body = ("  refine ⟨_, _, _, _, _, _, _, _, _, _, _, rfl,\n    %s,\n    ?_, by omega⟩\n  exact %s\n"
                % (",\n    ".join(cs), eq))
    else:
        body = "  refine ⟨_, _, rfl,\n    %s,\n    ?_⟩\n  exact %s\n" % (cs[0], eq)
        if pos in PASS:
            # the count of a V-hit is the count of its one call: restate it
            body = ("  refine ⟨_, _, rfl,\n    fun R => steps_congr trans (by omega) (%s),\n    ?_⟩\n  exact %s\n"
                    % (cs[0][len("fun R => "):], eq))
    return head + pre + body


HKS = {"HC": "obtain ⟨U0, rfl, hc⟩ := h", "H4": "obtain ⟨U0, U1, U2, U3, m1, m2, m3, m4, rfl, c1, c2, c3, hc, rfl⟩ := h"}
HALT = {}          # (pos, hk) -> (hk', a, b): the hit halts after m + a j + b steps (m: the steps of the rest)


def halt_thm(pos, hk):
    """the rest's hit halts in its call 1 (HC) or 4 (H4): the hit on the level halts, in its call 1 or 4"""
    s, t = CYC[pos]
    kr = 1 if hk == "HC" else 4
    st = structure(pos)
    ci = [i for i, (_, _, items) in enumerate(st) if len(items) > 1]
    assert len(ci) == 1 and ci[0] in (0, 3)
    ci = ci[0]
    out_hk = "HC" if ci == 0 else "H4"
    term, a, b = chain(st[ci][2], "j", True, last=kr)
    tot_a, tot_b = a, b
    for qi, qo, items in st[:ci]:
        d = LEV[items[0][1]]
        tot_a += d["a"]; tot_b += d["b"]
    HALT[(pos, hk)] = (out_hk, tot_a, tot_b)
    pa, pb, kin = PART[(pos, kr)]
    assert (tot_a, tot_b) == (pa, pa + pb), (pos, hk)      # accel.PART counts a n + b with n = j + 1 blocks
    assert kin == ci + 1
    head = ("/-- Position %d: if the rest's hit halts (%s), the hit on the level halts (%s). -/\n"
            "theorem halt%d_%s (j : Nat) {Y : Tape} {m : Nat} (h : %s Y m) : %s (W %d j Y) (m + (%d * j + %d)) := by\n"
            "  %s\n" % (pos, hk, out_hk, pos, hk, hk, out_hk, pos, tot_a, tot_b, HKS[hk]))
    if ci == 0:
        body = "  exact ⟨_, rfl, fun R => HaltsIn.congr (by omega) (%s)⟩\n" % term
    else:
        cs = ["fun R => %s j _ R" % items[0][1] for _, _, items in st[:3]]
        body = ("  refine ⟨_, _, _, _, _, _, _, _, rfl,\n    %s,\n    fun R => %s,\n    by omega⟩\n"
                % (",\n    ".join(cs), term))
    return head + body


# ------------------------------------------------------------------ the front
def front_run(t):
    """the hit and the bounce visit on `front Y`, Y = 1 T: segments between the calls on T.
    returns (segments, end): a segment is (steps, right tape before (cells from the head on), state before,
    right tape after, state after)"""
    f = wcells(FRONT[t])
    left = {-(i + 1): int(c) for i, c in enumerate(f + "1")}
    b = -(len(f) + 1)
    tape = dict(left)
    pos, st, n, mx, visits = 0, 0, 0, -1, 0
    cl = calls(SIG[t])
    segs, k = [], 0
    seg_start = (None, "A", 0)

    def right(p):
        hi = max([q for q in tape if tape[q]] + [p - 1, mx])
        return "".join(str(tape.get(q, 0)) for q in range(p, hi + 1))
    while True:
        if pos == b:
            assert ST[st] == cl[k][0] and tape[b] == 1, (t, k, ST[st])
            segs.append((n - seg_start[2], seg_start[0], seg_start[1], right(b + 1), ST[st]))
            st = ST.index(cl[k][1]); pos = b + 1; k += 1
            seg_start = (right(pos), ST[st], n)
            continue
        w, mv, q2 = TABLE[st, tape.get(pos, 0)]
        tape[pos] = w
        mx = max(mx, pos)
        pos += mv; st = q2; n += 1
        if st == 0 and pos > mx:
            visits += 1
            if visits == 2:
                break
    assert k == len(cl)
    endl = "".join(str(tape[q]) for q in range(pos - 1, b - 1, -1))
    o = "V" if t == "H" else "H"
    assert endl == wcells(FRONT[o]) + "1" * (3 if t == "H" else 7), (t, endl)
    segs.append((n - seg_start[2], seg_start[0], seg_start[1], None, "A"))
    assert n == FC[t] and tuple(sum(s[0] for s in segs[:i + 1]) for i in range(len(cl))) == FP[t]
    return segs


def tape_r(s):
    return "blank" if not s.strip("0") and s == "" else "(app %s blank)" % blist(s)


def front_thms(t):
    o = "V" if t == "H" else "H"
    segs = front_run(t)
    out = []
    grow = 3 if t == "H" else 7
    for i, (n, r0, q0, r1, q1) in enumerate(segs):
        if i == 0:
            a = "⟨app f%s (cons true T), blank, .A⟩" % t
        else:
            a = "⟨cons true T, %s, .%s⟩" % (tape_r(r0), q0)
        if i == len(segs) - 1:
            z = "⟨app f%s (%sT%s), blank, .A⟩" % (o, "cons true (" * grow, ")" * grow)
        else:
            z = "⟨T, cons true %s, .%s⟩" % (tape_r(r1), q1)
        out.append("theorem seg%s%d (T : Tape) : steps %d %s = some %s := rfl\n" % (t, i, n, a, z))
    if t == "H":
        ob = "obtain ⟨T0, T1, T2, T3, T4, T5, n1, n2, n3, n4, n5, rfl, c1, c2, c3, c4, c5, rfl, rfl⟩ := h"
        nc = 5
    else:
        ob = "obtain ⟨T0, T1, rfl, c1, rfl⟩ := h"
        nc = 1
    term = "seg%s%d T%d" % (t, nc, nc)
    for i in range(nc - 1, -1, -1):
        term = "steps_seq trans (seg%s%d T%d) (steps_seq trans (c%d _) (%s))" % (t, i, i, i + 1, term)
    out.append("/-- The front `%s`, a hit on the rest and the bounce visit: two visits, %d steps outside the rest. -/\n"
               "theorem front%s {Y Y' : Tape} {n : Nat} (h : Hit%s Y Y' n) :\n"
               "    steps (n + %d) ⟨app f%s Y, blank, .A⟩ = some ⟨app f%s Y', blank, .A⟩ := by\n"
               "  %s\n  exact steps_congr trans (by omega) (%s)\n"
               % ("2 1" if t == "H" else "5", FC[t], t, t, FC[t], t, o, ob, term))
    for hk in (("HC", "H4") if t == "H" else ("HC",)):
        kr = 1 if hk == "HC" else 4
        term = "HaltsIn.seq (seg%s%d T%d) (hc _)" % (t, kr - 1, kr - 1)
        for i in range(kr - 2, -1, -1):
            term = "HaltsIn.seq (seg%s%d T%d) (HaltsIn.seq (c%d _) (%s))" % (t, i, i, i + 1, term)
        ob = HKS[hk].replace("U", "T")
        out.append("/-- The front `%s` when the hit on the rest halts (%s). -/\n"
                   "theorem front%s_%s {Y : Tape} {m : Nat} (h : %s Y m) : HaltsIn (m + %d) ⟨app f%s Y, blank, .A⟩ := by\n"
                   "  %s\n  exact HaltsIn.congr (by omega) (%s)\n"
                   % ("2 1" if t == "H" else "5", hk, t, hk, hk, FP[t][kr - 1], t, ob, term))
    return out


def main():
    out = ["import Levels\nimport Odo\n\n/-! Whole hits on a level and on the front, composed from the stretches of "
           "`Levels.lean`. Generated by `py/hits_lean.py`; do not edit by hand. -/\n\nnamespace H23376\n\n"
           "open TM Levels\n\n"]
    for t in "HV":
        out.append("/-- The front `%s`, as cells, nearest first. -/\ndef f%s : List Bool := %s\n\n"
                   % ("2 1" if t == "H" else "5", t, blist(wcells(FRONT[t]))))
    for pos in range(16):
        out.append(hit_thm(pos) + "\n")
    # level_hit
    out.append("/-- The level table: a hit at position `p`, absorbed or passed on. -/\n"
               "theorem level_hit (p j : Nat) (hp : p < 16) :\n"
               "    (passOf p = none → ∀ Y, Hit (kindOf p) (W p j Y) (W (nxt p) (j + inc p) Y) (la p * (j + 1) + lb p)) ∧\n"
               "    (∀ k, passOf p = some k → ∀ Y Y' m, Hit k Y Y' m →\n"
               "      Hit (kindOf p) (W p j Y) (W (nxt p) (j + inc p) Y') (la p * (j + 1) + lb p + m)) := by\n"
               "  match p, hp with\n")
    for pos in range(16):
        if pos in PASS:
            out.append("  | %d, _ => exact ⟨fun h => (by cases h), fun k hk Y Y' m h => (by cases hk; exact hit%d j h)⟩\n"
                       % (pos, pos))
        else:
            out.append("  | %d, _ => exact ⟨fun _ Y => hit%d j Y, fun k hk => (by cases hk)⟩\n" % (pos, pos))
    out.append("  | n + 16, h => omega\n\n")
    for pos in sorted(PASS):
        for hk in ("HC", "H4"):
            if hk == "H4" and PASS[pos] != "H":
                continue
            out.append(halt_thm(pos, hk) + "\n")
    out.append("/-- A hit that halts: the first call halts, or the fourth call of an H-hit. -/\ninductive HK where\n"
               "  | HC | H4\n  deriving DecidableEq, Repr\n\n"
               "def Dies : HK → Tape → Nat → Prop\n  | .HC => HC\n  | .H4 => H4\n\n"
               "/-- Position and the way the rest's hit halts: the way the level's hit halts, and `(a, b)` for the\n"
               "`a j + b` steps made inside the level before. -/\n"
               "def haltTab : Nat → HK → Option (HK × Nat × Nat)\n")
    for (pos, hk), (o, a, b) in sorted(HALT.items()):
        out.append("  | %d, .%s => some (.%s, %d, %d)\n" % (pos, hk, o, a, b))
    out.append("  | _, _ => none\n\n")
    out.append("theorem level_halt (p j : Nat) (hk hk' : HK) (a b : Nat) (e : haltTab p hk = some (hk', a, b))\n"
               "    {Y : Tape} {m : Nat} (h : Dies hk Y m) : Dies hk' (W p j Y) (m + (a * j + b)) := by\n"
               "  unfold haltTab at e\n  split at e\n")
    for (pos, hk) in sorted(HALT):
        out.append("  · cases e; exact halt%d_%s j h\n" % (pos, hk))
    out.append("  · cases e\n\n")
    for t in "HV":
        out.append("\n".join(front_thms(t)) + "\n")
    out.append("end H23376\n")
    sys.stdout.write("".join(out))


if __name__ == "__main__":
    main()
