"""Write lean/Transients.lean for a machine of the family 1RB?RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_X---: the shapes of the
anomaly (the word has become one block, or one block and a single 1) as shift rules proved by `bbtools.symtm.prove`,
restated on the Q configurations of `Macro.lean`; and a Q configuration of the regular form from which the machine
halts (so the word-and-gap shape alone is not an invariant).

The first two shapes read neither A1 nor F0, so the same statements hold for all six machines (Lean checks each).
The third (a block and a single 1, a one-unit counter) goes through an F event; it ends in a regular Q
configuration of the stated form only for 1RB0RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_0LC---, and is left out for the others.

usage (from the repository root):
  python3 holdouts/1RB0RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_0LC---/py/gen_transients.py MACHINE > holdouts/MACHINE/lean/Transients.lean
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "../../../tools/py"))
from bbtools.symtm import ProofError, prove  # noqa: E402

RULES = [
    ("anom_one", "0^inf (11)^c+1 0 (111)^a+1 B> 0 R", "0^inf 1 1 0 (10)^c 1 1 1 B> 0 (000)^a 1 R",
     "anomaly, the word is one block of 2c+2: the run 1^(3(a+1)) is erased, the block slides one cell right and is "
     "rewritten as 1 1 (0 1)^c, one cell further left"),
    ("anom_two", "0^inf (11)^c+1 0 1 0 (111)^a+2 B> 0 R", "0^inf 1 1 0 (10)^c 1 1 1 0 1 1 1 B> 0 0 (000)^a 1 R",
     "anomaly, the word is a block of 2c+2 and a single 1, the counter's low part has a+2 >= 2 units"),
    ("anom_unit", "0^inf (11)^c+1 0 1 0 1 1 1 B> 0 0 0 (000)^p+1 1 R",
     "0^inf 1 1 0 (10)^c 1 1 1 1 1 0 1 1 1 B> 0 0 0 (000)^p 1 R",
     "anomaly, the word is a block of 2c+2 and a single 1, the counter's low part has one unit and its first gap "
     "has length 3(p+1)+2"),
]

UNIT = r'''
/-- The anomaly from a block and a single 1, counter low part one unit, first gap `3(p+1)+2`: the new word is
`[2, 1, …, 1, 5]`, the low part stays one unit and the first gap loses three cells; the result is a regular Q
configuration again. -/
theorem anomaly_unit (c p : Nat) (P : List Nat) (T : Tape) :
    steps (8 * c + 57) (qc [1, 2 * c + 2] 1 ((p + 1) :: P) T)
      = some (qc (5 :: (List.replicate c 1 ++ [2])) 1 (p :: P) T) := by
  have h := anom_unit c p (pt P T)
  have e0 : qc [1, 2 * c + 2] 1 ((p + 1) :: P) T = ⟨rep 1 [true, true, true] (cons false (cons true (cons false
      (rep (c + 1) [true, true] blank)))), cons false (pt ((p + 1) :: P) T), .B⟩ := by
    simp only [qc]; rw [wl_cons, wl_block]; rfl
  have e1 : qc (5 :: (List.replicate c 1 ++ [2])) 1 (p :: P) T = ⟨rep 1 [true, true, true] (cons false
      (rep 5 [true] (rep c [false, true] (cons false (cons true (cons true blank)))))), cons false (pt (p :: P) T),
      .B⟩ := by
    simp only [qc]; rw [wl_cons, wl_new]
  rw [e0, e1]
  exact h

'''

MACRO = r'''
/-! ## The anomaly on Q configurations

`qc W a P T` (see `Macro.lean`) lists the word last block first.  In each case the new word is
`[2, 1, …, 1]` (c ones), followed by a 3 or a 5 in the second and third case, and the counter's low part is one
unit.  In the first two cases a gap that is *not* of the form `3p + 2` appears in front of the old gaps: `3a` cells
(first case) or `3a + 1` cells (second case) — the misaligned gap whose overflows later cause the collisions.  In the
third case (proved here only for the machines where it ends in a regular Q configuration; for the others it goes
through an F event and depends on A1 and F0) the first gap loses three cells. -/

theorem rep_ones_even (n : Nat) (s : Tape) : rep (2 * n) [true] s = rep n [true, true] s := by
  induction n with
  | zero => rfl
  | succ n ih => rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega, rep_succ, rep_succ, ih]; rfl

theorem wl_block (c : Nat) : wl [2 * c + 2] = rep (c + 1) [true, true] blank := by
  simp only [wl, cons_false_blank]
  rw [show 2 * c + 2 = 2 * (c + 1) by omega, rep_ones_even]

theorem wl_new (c : Nat) :
    cons false (wl (List.replicate c 1 ++ [2])) = rep c [false, true] (cons false (cons true (cons true blank))) := by
  rw [sep_ones c [2]]; simp only [wl, rep_succ, rep_zero, cons_false_blank]; rfl

/-- The anomaly from a word of one block: the new word is `[2, 1, …, 1]` and a misaligned gap of `3a` cells
appears in front of the old gaps `P`. -/
theorem anomaly_one (a c : Nat) (P : List Nat) (T : Tape) :
    steps (3 * a + 8 * c + 17) (qc [2 * c + 2] (a + 1) P T)
      = some ⟨rep 1 [true, true, true] (cons false (wl (List.replicate c 1 ++ [2]))),
          cons false (rep a [false, false, false] (cons true (pt P T))), .B⟩ := by
  have h := anom_one a c (pt P T)
  have e0 : qc [2 * c + 2] (a + 1) P T
      = ⟨rep (a + 1) [true, true, true] (cons false (rep (c + 1) [true, true] blank)), cons false (pt P T), .B⟩ := by
    simp only [qc, wl_block]
  rw [e0, wl_new]
  exact h

/-- The anomaly from a block and a single 1, counter low part `a + 2`: the new word is `[2, 1, …, 1, 3]` and a
misaligned gap of `3a + 1` cells appears in front of the old gaps. -/
theorem anomaly_two (a c : Nat) (P : List Nat) (T : Tape) :
    steps (3 * a + 8 * c + 46) (qc [1, 2 * c + 2] (a + 2) P T)
      = some ⟨rep 1 [true, true, true] (cons false (wl (3 :: (List.replicate c 1 ++ [2])))),
          cons false (cons false (rep a [false, false, false] (cons true (pt P T)))), .B⟩ := by
  have h := anom_two a c (pt P T)
  have e0 : qc [1, 2 * c + 2] (a + 2) P T = ⟨rep (a + 2) [true, true, true] (cons false (cons true (cons false
      (rep (c + 1) [true, true] blank)))), cons false (pt P T), .B⟩ := by
    simp only [qc]; rw [wl_cons, wl_block]; rfl
  rw [e0, wl_cons, wl_new]
  exact h

<<UNIT>>/-! ## The word-and-gap shape is not enough

A Q configuration with a valid word (first block even, the others odd), a one-unit counter and no gaps at all,
from which every machine of the family halts: `1^2 0 1^3 0 1^3 B>0`, then blank tape.  Its word is short, so it
runs out (an anomaly) before the gap left behind by the previous one is cleared.  So a proof of non-halting cannot
rest on the shape of the word and of the gaps alone: it has to carry the sizes along (the race between the word's
`N(W)` and the collision cascade). -/

theorem qc_short_eq : qc [3, 2] 1 [] blank = (⟨[true, true, true, false, true, true, true, false, true, true, false],
    [false], .B⟩ : FCfg St).toCfg := rfl

/-- A run of lists that ends in a halt within `m` steps (`none`) is a halt of the machine. -/
theorem halts_of_fsteps_none : ∀ (m : Nat) (c : FCfg St), TM.fsteps trans m c = none → TM.Halts trans c.toCfg
  | 0, _, h => by cases h
  | m + 1, c, h => by
    simp only [TM.fsteps] at h
    cases e : TM.fstep trans c with
    | none => exact ⟨0, c.toCfg, rfl, by rw [FCfg.step_eq, e]; rfl⟩
    | some c' =>
      rw [e] at h
      obtain ⟨k, d, h₁, h₂⟩ := halts_of_fsteps_none m c' h
      exact ⟨k + 1, d, by rw [TM.steps_succ_of_step trans k (by rw [FCfg.step_eq, e]; rfl)]; exact h₁, h₂⟩

/-- From `1^2 0 1^3 0 1^3 B>0` and blank tape the machine halts (at step 190 in the bbchallenge count). -/
theorem qc_short_halts : TM.Halts trans (qc [3, 2] 1 [] blank) := by
  rw [qc_short_eq]
  exact halts_of_fsteps_none 190 _ (by decide +kernel)
'''


def main():
    m = sys.argv[1]
    mach = open(os.path.join(HERE, "../../", m, "lean/Machine.lean")).read()
    ns = re.search(r"^namespace (\w+)", mach, re.M).group(1)
    out = ["import Macro", "",
           f"/-! The irregular phase *anomaly* of {m}: the rules generated by `py/gen_transients.py` in the folder of "
           "1RB0RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_0LC--- (the shared scripts of the family); do not edit by hand. -/", "",
           f"namespace {ns}", "", "open TM", ""]
    unit = True
    for name, a, b, doc in RULES:
        try:
            t, _ = prove(m, name, a, b, doc=doc + ".", count_first=True, max_seg=40, rotate=True)
        except ProofError:
            # the third shape reads the counter and goes through an F event: it depends on A1 and F0, and only
            # for some machines of the family it ends in a regular Q configuration of this form
            assert name == "anom_unit"
            unit = False
            continue
        out.append(t)
    out.append(MACRO.replace("<<UNIT>>", UNIT if unit else ""))
    out.append(f"end {ns}")
    print("\n".join(out))


if __name__ == "__main__":
    main()
