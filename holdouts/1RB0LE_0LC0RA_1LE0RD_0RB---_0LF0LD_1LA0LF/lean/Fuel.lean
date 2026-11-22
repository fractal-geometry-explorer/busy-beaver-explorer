import Link
import Need

/-! # How many visits a defect needs, and the reduction corrected to start at round 9

Machine: 1RB0LE_0LC0RA_1LE0RD_0RB---_0LF0LD_1LA0LF, read on the mirrored tape (see the README of this folder and
`Tokens.lean`, `Total.lean`, `Link.lean`, which this file builds on). The machine-independent part (`nx`, `ne`,
`n0`, `fuel`, `dies`, `a9`, `R9`) is in `Need.lean`, so that the twin 1RB0LF_1LC1RC_0RA0LD_0LE1RE_0RF0LC_1RC---
can use it too (its `lean/Link.lean`, `K83189.nonhalt_of_need`).

* `nx`, `ne`, `n0`: the **fuel** a defect needs. `nx W` is a number of visits of A after which `x W` (W a tape of
  words) has no defect left; `ne`, `n0` are the same for the tapes that `Eh` and `E0` leave. They are computed by a
  plain recursion over the words of W (`nx (O W) = 2 nx W + 1`, `nx (L W) = ⌈nx W / 2⌉`, `nx (I W) = ne W + 1`, ...),
  so whether a defect dies is decided by the tape it sits on, without running the visits.
* `fuel`: if `nx W ≤ n`, then n visits of A on `x W` leave a clean tape (and the same for `1 W`, and for the tapes
  of `Eh`, `E0`). In particular `dies`: if `nx W ≤ 1`, the round's single visit kills the defect `x` put in front.
* `old_hyp_false`: the hypothesis of `L36869.nonhalt_of_clean` (every round's defect dies, counted from blank tape)
  is false: the defect of round 2 survives (`A(x L O I) = L I x I`). The early rounds are not one-defect tapes, so
  that theorem was vacuous.
* `round9`: the machine reaches the start of round 9, `0 x A(S_8)` with `A(S_8)` the clean tape `a9` below, at step
  5,848 from blank tape (kernel evaluation).
* `nonhalt_of_need`: the corrected reduction. If for every round from 9 on the defect needs at most one visit
  (`nx W ≤ 1` on the round's tape `x W`), the machine never halts from blank tape.

What is left open is exactly the hypothesis of `nonhalt_of_need`. In the run the margin is huge: the round tape is
`x L^m U`, so `nx (L^m U) = ⌈nx U / 2^m⌉`, and `nx U = 3` in every round from 12 to 3,000 that was checked
(`py/fuel.py`), against `2^m` with m about k/2.
-/

namespace F36869

open Z36869

/-! ## The old reduction was vacuous -/

/-- The hypothesis of `L36869.nonhalt_of_clean` is false: from blank tape, `S_2 = x L O I` and the defect survives
round 2 (`A(x L O I) = L I x I`). -/
theorem old_hyp_false : ¬ (∀ w a, L36869.Reach w → TV .A w a → Clean a) := by
  intro H
  have r1 : L36869.Reach [.x, .I] := L36869.Reach.next L36869.Reach.nil TV.aNil
  have r2 : L36869.Reach [.x, .L, .O, .I] := L36869.Reach.next r1 (TV.axI TV.hNil)
  have t2 : TV .A [.x, .L, .O, .I] [.L, .I, .x, .I] := TV.axL (TV.axO [.I]) (TV.aO [.x, .I])
  have hx := H _ _ r2 t2 .x (by simp)
  simp at hx

/-- The bits of a word list, head first. -/
def flat : List T → List Bool
  | [] => []
  | t :: w => bits t ++ flat w

theorem pre_eq (l : List Bool) (s : Tape) : pre l s = TM.app l s := by
  induction l with
  | nil => rfl
  | cons b l ih => show Z36869.cons b (pre l s) = TM.cons b (TM.app l s); rw [ih, L36869.zc]

theorem enc_eq (w : List T) : enc w = TM.app (flat w) TM.blank := by
  induction w with
  | nil => rfl
  | cons t w ih => show pre (bits t) (enc w) = _; rw [pre_eq, ih, flat, TM.app_app]

/-- The left half tape at the start of round 9, as the list simulator leaves it (no trailing blanks). -/
def l9 : List Bool := (false :: flat (.x :: a9)).dropLast.dropLast

theorem l9_eq : false :: flat (.x :: a9) = l9 ++ [false, false] := by decide

theorem round9_f : H36869.fsteps 5848 (TM.FCfg.blank .A) = some ⟨l9, [false], .A⟩ := by decide +kernel

/-- From blank tape the machine reaches the start of round 9 at step 5,848. -/
theorem round9 : H36869.steps 5848 H36869.init = some ⟨TM.cons false (enc (.x :: a9)), TM.blank, .A⟩ := by
  have h := TM.blank_reaches H36869.trans round9_f
  show TM.steps H36869.trans 5848 (TM.blankCfg .A) = _
  rw [h]
  have e1 : TM.app l9 TM.blank = TM.cons false (enc (.x :: a9)) := by
    rw [enc_eq, ← TM.app_cons, l9_eq, ← TM.app_app]
    show TM.app l9 TM.blank = TM.app l9 (TM.cons false (TM.cons false TM.blank))
    rw [TM.cons_false_blank, TM.cons_false_blank]
  have e2 : TM.app [false] TM.blank = TM.blank := TM.cons_false_blank
  show some (⟨TM.app l9 TM.blank, TM.app [false] TM.blank, .A⟩ : H36869.Config) = _
  rw [e1, e2]

theorem runs9 (H : ∀ W, R9 W → nx W ≤ 1) :
    ∀ k, ∃ W n, R9 W ∧ k ≤ n ∧ H36869.steps n H36869.init = some ⟨TM.cons false (enc (.x :: W)), TM.blank, .A⟩ := by
  intro k
  induction k with
  | zero => exact ⟨a9, 5848, R9.base, by omega, round9⟩
  | succ k ih =>
    obtain ⟨W, n, hW, hk, hn⟩ := ih
    have hg : Good (.x :: W) := Or.inr ⟨[], .x, W, clean_nil, Or.inl rfl, r9_clean H hW, rfl⟩
    obtain ⟨a, ha⟩ := L36869.step_of_good hg
    have hv : L36869.Vis .A (enc (.x :: W)) (enc a) := L36869.link (sound ha)
    obtain ⟨m, hm1, hm⟩ := L36869.round hv
    refine ⟨a, n + m, R9.next hW ha, by omega, ?_⟩
    rw [L36869.enc_x]; exact L36869.seq hn hm

/-- **The corrected reduction.** If in every round from round 9 on the defect in front needs at most one visit
(`nx W ≤ 1` on the round tape `x W`), the machine never halts from blank tape. -/
theorem nonhalt_of_need (H : ∀ W, R9 W → nx W ≤ 1) : ¬ H36869.HaltsFromBlank := by
  apply TM.not_halts_of_forall
  apply TM.forall_of_unbounded _ (fun m => ∃ W, H36869.steps m H36869.init =
    some ⟨TM.cons false (enc (.x :: W)), TM.blank, .A⟩)
  · intro n
    obtain ⟨W, m, _, hm, h⟩ := runs9 H n
    exact ⟨m, hm, W, h⟩
  · rintro m ⟨W, h⟩
    exact ⟨_, h⟩

end F36869
