"""Write lean/Rules.lean and lean/Clock.lean of a machine of the clock family (see clock.py).

Rules.lean: the sweep and the merge, proved by `bbtools.symtm.prove`.  Clock.lean: the tick theorem for every level
`j` by strong induction, for an arbitrary word, from those two rules and the hypothesis that the word goes through
`2^j` P-steps (one excursion of the head into the word each).

The shape of a clock (see `PARAMS` in clock.py and `SWEEP` here): the block `J j W` read from the head is
`1^(B0+g*j) 0 W` (head on a 1, `h = 1`) or `0 1^(B0+g*j) 0 W` (head on a 0, `h = 0`); a tick eats the `g` zeros left
of the head.  The sweep is `0^g Y> J j W` -> `A 0^(s+g*j) Bp Z> PR W`, the P-step `L 0^(s-1) Bp Z> PR W` ->
`L Y> J 0 W'` and the merge `A 0 Y> h` -> `Y> h 1^g`.  The defaults (`g = 2`, `h = 1`, `A = 1`, `s = B0+1`, `Bp = 1`,
`PR` empty) are the five machines of the first clock batch.

usage (from the repository root): python3 holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/py/gen_clock.py M
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
sys.path.insert(0, os.path.join(ROOT, "tools", "py"))
sys.path.insert(0, HERE)
from bbtools.symtm import prove, rules_file  # noqa: E402
from clock import MIRROR, ONES_FIRST, PARAMS, VISIT, mirror, sweep_spec  # noqa: E402
from bbtools.leangen import machine_lean  # noqa: E402


def chain(cell, k, inner):
    return "".join(f"cons {cell} (" for _ in range(k)) + inner + ")" * k


TEMPLATE = r'''import @IMP@

/-!
# The clock of @M@

`J j W` is the tape `@JT@` right of the head; the head is in state @Y@ on its first cell.  At every visit
of the left end in state @X@ the tape is `@X@>0 @VT@`, one step after `@Y@> J j W` one cell to the right.

A *P-step* `PStep W W' e` is one excursion of the head into the word: `L @PLT@ @Z@> @PRT@W` reaches `L @Y@> @J0T@`
in `e` steps, for every left tape `L`.  `PChain m W W' E`: `m` P-steps in a row, of total cost `E`.

**Theorem `tick`.**  For every level `j`, if `W` reaches `W'` by `2^j` P-steps of total cost `E`, then

    L @ZG@ @Y@> @JT@   reaches   L @Y@> @J1T@   in exactly  E + @C@·2^j − @G@  steps,

for every `L`.  The tick is the sweep (`rule_sweep`: the block becomes 0s), one P-step, the ticks `0, ..., j−1`
(each eats @GW@ of the 0s the sweep left), and the merge (`rule_merge`).  Proved by strong induction on `j`; the word
`W` is arbitrary.  So the block grows by @G@ per tick while the word goes through `2^j` applications of one map P.
-/

namespace @NS@

open TM

/-- `@JT@`, read from the head. -/
def J (j : Nat) (W : Tape) : Tape := cons @H@ (@JB@)

/-- One excursion into the word: `L @PLT@ @Z@> @PRT@W` reaches `L @Y@> @J0T@` in `e` steps, for every `L`. -/
def PStep (W W' : Tape) (e : Nat) : Prop :=
  ∀ L : Tape, steps e ⟨@PL@, @PR@, .@Z@⟩ = some ⟨L, J 0 W', .@Y@⟩

/-- `m` P-steps in a row, of total cost `E`. -/
inductive PChain : Nat → Tape → Tape → Nat → Prop
  | zero (W : Tape) : PChain 0 W W 0
  | succ {m : Nat} {W W1 W2 : Tape} {e E : Nat} : PStep W W1 e → PChain m W1 W2 E → PChain (m + 1) W W2 (e + E)

theorem PChain.split : ∀ (x y : Nat) {W W2 : Tape} {E : Nat}, PChain (x + y) W W2 E →
    ∃ W1 E1 E2, PChain x W W1 E1 ∧ PChain y W1 W2 E2 ∧ E = E1 + E2 := by
  intro x
  induction x with
  | zero => intro y W W2 E h; exact ⟨W, 0, E, .zero W, by simpa using h, by omega⟩
  | succ x ih =>
    intro y W W2 E h
    rw [show x + 1 + y = (x + y) + 1 by omega] at h
    cases h with
    | succ hs hc =>
      obtain ⟨W1, E1, E2, h1, h2, he⟩ := ih y hc
      exact ⟨W1, _ + E1, E2, .succ hs h1, h2, by omega⟩

theorem zeros_cons (n : Nat) (Y : Tape) : rep n [false] (cons false Y) = cons false (rep n [false] Y) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rep_succ, ih]; rfl

/-- The statement of tick `j`. -/
def Tick (j : Nat) : Prop :=
  ∀ (W W' : Tape) (E : Nat), PChain (2 ^ j) W W' E → ∀ L : Tape,
    steps (E + @C@ * 2 ^ j - @G@) ⟨@ZGL@, J j W, .@Y@⟩ = some ⟨L, J (j + 1) W', .@Y@⟩

/-- The number of P-steps of ticks `a, ..., a+m−1` (`2^(a+m) − 2^a`). -/
def NP : Nat → Nat → Nat
  | _, 0 => 0
  | a, m + 1 => 2 ^ a + NP (a + 1) m

/-- Their structural step count (`@C@·(2^(a+m) − 2^a) − @G@m`). -/
def CS : Nat → Nat → Nat
  | _, 0 => 0
  | a, m + 1 => (@C@ * 2 ^ a - @G@) + CS (a + 1) m

theorem NP_eq (m : Nat) : ∀ a, NP a m + 2 ^ a = 2 ^ (a + m) := by
  induction m with
  | zero => intro a; simp [NP]
  | succ m ih =>
    intro a
    have h := ih (a + 1)
    have p : 2 ^ (a + 1) = 2 * 2 ^ a := by rw [Nat.pow_succ]; omega
    simp only [NP]
    rw [show a + (m + 1) = a + 1 + m by omega, ← h]
    omega

theorem CS_eq (m : Nat) : ∀ a, CS a m + @G@ * m + @C@ * 2 ^ a = @C@ * 2 ^ (a + m) := by
  induction m with
  | zero => intro a; simp [CS]
  | succ m ih =>
    intro a
    have h := ih (a + 1)
    have p : 2 ^ (a + 1) = 2 * 2 ^ a := by rw [Nat.pow_succ]; omega
    have p5 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
    simp only [CS]
    rw [show a + (m + 1) = a + 1 + m by omega, ← h]
    omega

/-- Ticks `a, ..., a+m−1` in a row eat `@G@m` zeros: `L 0^(@G@m) @Y@> J a W` reaches `L @Y@> J (a+m) W'`. -/
theorem chain (m : Nat) : ∀ (a : Nat), (∀ i, a ≤ i → i < a + m → Tick i) →
    ∀ (W W' : Tape) (E : Nat), PChain (NP a m) W W' E → ∀ L : Tape,
    steps (E + CS a m) ⟨rep (@G@ * m) [false] L, J a W, .@Y@⟩ = some ⟨L, J (a + m) W', .@Y@⟩ := by
  induction m with
  | zero =>
    intro a _ W W' E h L
    simp only [NP] at h
    cases h
    rfl
  | succ m ih =>
    intro a hT W W' E h L
    simp only [NP] at h
    obtain ⟨W1, E1, E2, h1, h2, he⟩ := PChain.split _ _ h
    have z : rep (@G@ * (m + 1)) [false] L = @ZGM@ := by
      rw [show @G@ * (m + 1) = @G@ * m@P1@ by omega]; rfl
    rw [z]
    have s1 := hT a (by omega) (by omega) W W1 E1 h1 (rep (@G@ * m) [false] L)
    have s2 := ih (a + 1) (fun i h1 h2 => hT i (by omega) (by omega)) W1 W' E2 h2 L
    rw [show a + 1 + m = a + (m + 1) by omega] at s2
    have := steps_seq trans s1 s2
    refine steps_congr trans ?_ this
    simp only [CS]
    have p5 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
    generalize 2 ^ a = q at *
    omega

/-- **The tick**, for every level `j`: `L @ZG@ @Y@> @JT@` reaches `L @Y@> @J1T@` in
`E + @C@·2^j − @G@` steps whenever `2^j` P-steps of total cost `E` take `W` to `W'`. -/
theorem tick (j : Nat) : Tick j := by
  induction j using Nat.strongRecOn with
  | _ j ih =>
    intro W W' E h L
    have hn := NP_eq j 0
    have hc := CS_eq j 0
    simp only [Nat.pow_zero, Nat.zero_add] at hn hc
    rw [show 2 ^ j = 1 + NP 0 j by omega] at h
    obtain ⟨W1, E1, E2, h1, h2, he⟩ := PChain.split _ _ h
    cases h1 with
    | succ hs hz =>
      cases hz
      -- the sweep
      have s0 := rule_sweep j L W
      -- the P-step
      have s1 := hs (rep (@G@ * j) [false] (@ML@))
      -- ticks 0 .. j-1
      have s2 := chain j 0 (fun i _ h2 => ih i (by omega)) W1 W' E2 h2 (@ML@)
      simp only [zeros_cons] at s0 s1 s2
      -- the merge
      have s3 := rule_merge L (@MR@)
      have e3 : @MERGED@ = J (j + 1) W' := by
        unfold J; rw [show @G@ * (j + 1) = @G@ * (0 + j)@P1@ by omega]; rfl
      rw [e3] at s3
      have := steps_seq trans s0 (steps_seq trans s1 (steps_seq trans s2 s3))
      refine steps_congr trans ?_ this
      have p5 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
      generalize 2 ^ j = q at *
      omega

/-- The tick at the left end of the tape (blank to the left); the visits of the left end in state @X@ are one step
after these configurations. -/
theorem tick_left_end (j : Nat) (W W' : Tape) (E : Nat) (h : PChain (2 ^ j) W W' E) :
    steps (E + @C@ * 2 ^ j - @G@) ⟨blank, J j W, .@Y@⟩ = some ⟨blank, J (j + 1) W', .@Y@⟩ := by
  have := tick j W W' E h blank
  rwa [@CFB@] at this

end @NS@
'''


BRIDGE = r'''import Machine
import MirrorClock

/-!
# From the mirror image back to @MO@

`MirrorClock.lean` proves the clock for the mirror image `@NS@M` of the machine (L and R swapped).  Here: the
mirror of a configuration (`mir`: the head stays on its cell, the two sides swap) turns every run of the mirror
machine into a run of the machine (`steps_mir`), so the tick holds for the machine itself, at the right end of the
tape (`tick_right_end`).
-/

namespace @NS@B

open TM

/-- The mirror image of a configuration, with the states renamed by `f`: the head stays on its cell, the left
side becomes the right side and back. -/
def mir {Q Q' : Type} (f : Q → Q') (c : Cfg Q) : Cfg Q' := ⟨tail c.r, cons (c.r 0) c.l, f c.st⟩

theorem cons_tail (s : Tape) : cons (s 0) (tail s) = s := by
  funext n; cases n <;> rfl

def flipD : Dir → Dir
  | .L => .R
  | .R => .L

/-- One step of a machine and its mirror image. -/
theorem step_mir {Q Q' : Type} (δ : Q → Bool → Option (Bool × Dir × Q)) (δ' : Q' → Bool → Option (Bool × Dir × Q'))
    (f : Q → Q') (hδ : ∀ q b, δ' (f q) b = (δ q b).map (fun t => (t.1, flipD t.2.1, f t.2.2))) (c : Cfg Q) :
    step δ' (mir f c) = (step δ c).map (mir f) := by
  obtain ⟨l, r, q⟩ := c
  rcases h : δ q (r 0) with _ | ⟨w, d, s⟩
  · simp [step, mir, hδ, h]
  · cases d
    · simp [step, mir, hδ, h, flipD]
      exact (cons_tail l).symm
    · simp [step, mir, hδ, h, flipD]

theorem steps_mir {Q Q' : Type} (δ : Q → Bool → Option (Bool × Dir × Q)) (δ' : Q' → Bool → Option (Bool × Dir × Q'))
    (f : Q → Q') (hδ : ∀ q b, δ' (f q) b = (δ q b).map (fun t => (t.1, flipD t.2.1, f t.2.2))) :
    ∀ (n : Nat) (c : Cfg Q), steps δ' n (mir f c) = (steps δ n c).map (mir f) := by
  intro n
  induction n with
  | zero => intro c; rfl
  | succ n ih =>
    intro c
    simp only [steps, step_mir δ δ' f hδ c]
    rcases step δ c with _ | c'
    · rfl
    · exact ih c'

/-- The states of the mirror machine as those of the machine. -/
def st : @NS@M.St → @NS@.St
  | .A => .A | .B => .B | .C => .C | .D => .D | .E => .E | .F => .F

theorem trans_mir : ∀ q b, @NS@.trans (st q) b =
    (@NS@M.trans q b).map (fun t => (t.1, flipD t.2.1, st t.2.2)) := by
  intro q b; cases q <;> cases b <;> rfl

/-- Every run of the mirror machine is, mirrored, a run of the machine. -/
theorem of_mirror {n : Nat} {c d : @NS@M.Config} (h : @NS@M.steps n c = some d) :
    @NS@.steps n (mir st c) = some (mir st d) := by
  have := steps_mir @NS@M.trans @NS@.trans st trans_mir n c
  show steps @NS@.trans n (mir st c) = _
  rw [this]
  show Option.map _ (@NS@M.steps n c) = _
  rw [h]; rfl

/-- **The tick of the machine**, at the right end: the mirror image of `@NS@M.tick_left_end`. -/
theorem tick_right_end (j : Nat) (W W' : Tape) (E : Nat) (h : @NS@M.PChain (2 ^ j) W W' E) :
    @NS@.steps (E + @C@ * 2 ^ j - @G@) (mir st ⟨blank, @NS@M.J j W, .@Y@⟩) =
      some (mir st ⟨blank, @NS@M.J (j + 1) W', .@Y@⟩) :=
  of_mirror (@NS@M.tick_left_end j W W' E h)

/-- The tick of the machine for every tape to the right of the @G@ 0s it eats. -/
theorem tick (j : Nat) (W W' : Tape) (E : Nat) (h : @NS@M.PChain (2 ^ j) W W' E) (L : Tape) :
    @NS@.steps (E + @C@ * 2 ^ j - @G@)
      (mir st ⟨@ZGL@, @NS@M.J j W, .@Y@⟩) =
      some (mir st ⟨L, @NS@M.J (j + 1) W', .@Y@⟩) :=
  of_mirror (@NS@M.tick j W W' E h L)

end @NS@B
'''


def lchain(cells, inner):
    """Cells nearest to the head first, consed onto `inner`, without parentheses around a bare name."""
    if not cells:
        return inner
    s = " (".join(f"cons {'true' if c else 'false'}" for c in cells)
    return s + " " + inner + ")" * (len(cells) - 1)


def cells_txt(cells):
    return " ".join(str(c) for c in cells)


def params(m):
    p = PARAMS[m]
    X, Y, B0 = p[:3]
    g, h = (p[3], p[4]) if len(p) > 3 else (2, 1)
    A, s, Bp, PR, pz = sweep_spec(m)
    return X, Y, B0, g, h, A, s, Bp, PR, pz


def main(m):
    X, Y, B0, g, h, A, s, Bp, PR, pz = params(m)
    ML = A + [0] * (s - pz)
    d = os.path.join(ROOT, "holdouts", m, "lean")
    ns = re.search(r"^namespace (\w+)", open(os.path.join(d, "Machine.lean")).read(), re.M).group(1)
    m_orig, pre, title = m, "", m
    if m in MIRROR:                     # the clock is at the right end: prove it for the mirror image
        m, pre, ns = mirror(m_orig), "Mirror", ns + "M"
        title = f"{m}, the mirror image of {m_orig}"
        open(os.path.join(d, "MirrorMachine.lean"), "w").write(machine_lean(
            m, ns, doc=f"The mirror image of {m_orig} (L and R swapped), whose clock is at the right end; "
                       "see `MirrorBridge.lean` for the correspondence of the runs."))
    n1 = B0 - 1 if h else B0            # the 1s of J 0 after the head cell
    hd = "" if h else "0 "              # the head cell in the text forms, when it is not part of the block
    ones = " ".join(["1"] * n1)
    zg = " ".join(["0"] * g)
    after = " ".join(x for x in [cells_txt(Bp), "{z}>", cells_txt(PR)] if x)
    of = m_orig in ONES_FIRST                # the fixed 1s of the block before its repeat (symtm cannot split a repeat)
    lhs = f"L {zg} {Y}> {h} {ones} 1^{g}*n 0 R" if of else f"L {zg} {Y}> {h} 1^{g}*n {ones} 0 R"
    if of:
        jb = chain("true", n1, f"rep ({g} * j) [true] (cons false W)")
        mr = chain("true", n1, f"rep ({g} * (0 + j)) [true] (cons false W')")
    else:
        jb = f"rep ({g} * j) [true] (" + chain("true", n1, "cons false W") + ")"
        mr = f"rep ({g} * (0 + j)) [true] (" + chain("true", n1, "cons false W'") + ")"
    rhs = f"L {cells_txt(A)} 0^{g}*n+{s} {after} R"
    sdoc = (f"The sweep: `{zg} {Y}> {hd}1^({B0}+{g}n) 0` becomes `{cells_txt(A)} 0^({s}+{g}n) {after}`.")
    Z = None
    for z in "ABCDEF":
        try:
            sw, _ = prove(m, "rule_sweep", lhs, rhs.format(z=z), doc=sdoc.format(z=z))
            Z = z
            break
        except Exception:  # noqa: BLE001
            continue
    assert Z, "no sweep"
    s0 = int(re.search(r"steps \(%d \* n \+ (\d+)\)" % g, sw).group(1))
    a0 = cells_txt(ML)
    gones = " ".join(["1"] * g)
    mg, _ = prove(m, "rule_merge", f"L {a0} {Y}> {h} R", f"L {Y}> {h} {gones} R",
                  doc=f"The merge: `{a0} {Y}> {h}` becomes `{Y}> {h} {gones}`.")
    m0 = int(re.search(r"steps \((\d+)\)", mg).group(1))
    rn = pre + "Rules"                  # a Rules.lean of other rules (not written here) is kept: use ClockRules.lean
    rp = os.path.join(d, rn + ".lean")
    if os.path.exists(rp) and "gen_clock.py" not in open(rp).read():
        rn = pre + "ClockRules"
    open(os.path.join(d, rn + ".lean"), "w").write(rules_file(
        pre + "Machine", ns, [sw, mg], "The two local rules of the tick, written by `bbtools.symtm.prove` "
        "(from `holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/py/gen_clock.py`)."))
    C = s0 + m0 + g
    tb = lambda x: "true" if x else "false"  # noqa: E731
    plc = list(reversed([0] * pz + Bp))
    v = VISIT.get(m_orig, 0)
    sub = {
        "@IMP@": rn, "@M@": title, "@NS@": ns, "@X@": X, "@Y@": Y, "@Z@": Z, "@C@": str(C), "@G@": str(g),
        "@GW@": {2: "two", 3: "three"}.get(g, str(g)), "@H@": tb(h),
        "@JT@": f"{hd}1^({B0}+{g}j) 0 W", "@J1T@": f"{hd}1^({B0}+{g}j+{g}) 0 W'", "@J0T@": f"{hd}1^{B0} 0 W'",
        "@VT@": "0 " * v + f"1^({B0 + 1 - h - v}+{g}j) 0 W",
        "@PLT@": " ".join(x for x in [f"0^{pz}", cells_txt(Bp)] if x),
        "@PRT@": "".join(f"{c} " for c in PR),
        "@PL@": chain_nl(plc, "L"), "@PR@": chain_nl(list(PR), "W") if PR else "W",
        "@ZG@": zg, "@ZGL@": lchain([0] * g, "L"),
        "@ZGM@": "cons false (" * g + f"rep ({g} * m) [false] L" + ")" * g,
        "@P1@": " + 1" * g,
        "@ML@": lchain(list(reversed(ML)), "L"),
        "@JB@": jb, "@MR@": mr, "@MERGED@": f"cons {tb(h)} (" + "cons true (" * g + mr + ")" * (g + 1),
        "@CFB@": ", ".join(["cons_false_blank"] * g),
    }
    txt = TEMPLATE
    for k, v in sub.items():
        txt = txt.replace(k, v)
    assert "@" not in txt.replace("@[", ""), re.findall(r"@\w+@", txt)
    open(os.path.join(d, pre + "Clock.lean"), "w").write(txt)
    if pre:
        bt = BRIDGE
        for k, v in [("@MO@", m_orig), ("@NS@", ns[:-1]), ("@C@", str(C)), ("@G@", str(g)), ("@Y@", Y),
                     ("@ZGL@", lchain([0] * g, "L"))]:
            bt = bt.replace(k, v)
        open(os.path.join(d, "MirrorBridge.lean"), "w").write(bt)
    ck = os.path.join(d, "check.sh")
    s = open(ck).read()
    if pre + "Clock.lean" not in s:
        extra = " MirrorMachine.lean" if pre else ""
        s = s.rstrip("\n") + f"{extra} {rn}.lean {pre}Clock.lean" + (" MirrorBridge.lean" if pre else "") + "\n"
        open(ck, "w").write(s)
    print(m, "Y", Y, "Z", Z, "B0", B0, "g", g, "h", h, "sweep cost %dn+%d" % (g, s0), "merge", m0, "C", C)


def chain_nl(cells, inner):
    """Cells nearest to the head first, consed onto `(inner)`, the form of `chain`."""
    return "".join(f"cons {'true' if c else 'false'} (" for c in cells) + inner + ")" * len(cells)


if __name__ == "__main__":
    main(sys.argv[1])
