import Phases
import TM.Fin

/-!
# 1RB1RF_1LC1LF_0RE1LD_0LB1LD_---1RC_1RA0RD and its mirror partner 1RB1LF_1RC1RF_0LD1RE_---1LC_0RB1RE_1LA0LE

Mirrored (left and right swapped) and with states D and E renamed, the table of the partner
1RB1LF_1RC1RF_0LD1RE_---1LC_0RB1RE_1LA0LE is the table of this machine except for one entry: A0 moves left instead of
right.  Both halt only on the same transition (D0 of the partner, E0 here).  Do they halt together from blank tape?

This file shows that no argument about the two tables alone can say so.  It takes two tapes `c` of the shape of this
machine's pass starts, and the partner's mirror images `mirror c` of them:

* from `PS 0 39` this machine reaches a configuration of its own run from blank tape (`ps_0_39_iff`), so it halts
  from there exactly if it halts from blank tape; the partner halts from `mirror (PS 0 39)` after 44,274 steps
  (`partner_halts_39`);
* from `PS 22 3` this machine halts (`ps_22_3_halts`); the partner, from `mirror (PS 22 3)`, reaches after
  1,499,945 steps the configuration of its own run from blank tape at step 730,147 (`partner_iff_22_3`).

So if the two machines halted together on these two pairs of tapes, both would halt from blank tape
(`together_forces_halts`).  Neither is known to halt; both are open BB(6) holdouts, and both phase maps run 10^8
phases or more without a halt.  An equivalence proof therefore has to use the particular runs from blank tape, not the
tables (see `holdouts/EQUIVALENCES.md`).  The partner's runs are evaluated by the list simulator of `TM.Fin`; the two
long ones by `native_decide`.
-/

namespace H149707

open TM

/-! ## Runs that meet -/

theorem steps_add {Q : Type} (δ : Q → Bool → Option (Bool × Dir × Q)) :
    ∀ (a b : Nat) (c : Cfg Q), TM.steps δ (a + b) c = (TM.steps δ a c).bind (TM.steps δ b)
  | 0, b, c => by simp
  | a + 1, b, c => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    cases hs : TM.step δ c with
    | none => simp [TM.steps, hs]
    | some d => rw [TM.steps_succ_of_step δ _ hs, TM.steps_succ_of_step δ _ hs]; exact steps_add δ a b d

/-- A machine halts from `c` exactly if it halts from any configuration that its run from `c` reaches. -/
theorem halts_iff_of_steps {Q : Type} (δ : Q → Bool → Option (Bool × Dir × Q)) {n : Nat} {c c' : Cfg Q}
    (h : TM.steps δ n c = some c') : TM.Halts δ c ↔ TM.Halts δ c' := by
  constructor
  · rintro ⟨m, d, hm, hd⟩
    by_cases hnm : n ≤ m
    · refine ⟨m - n, d, ?_, hd⟩
      have := steps_add δ n (m - n) c
      rw [show n + (m - n) = m by omega, hm, h] at this
      simpa using this.symm
    · have := steps_add δ m (n - m) c
      rw [show m + (n - m) = n by omega, h, hm] at this
      obtain ⟨k, hk⟩ : ∃ k, n - m = k + 1 := ⟨n - m - 1, by omega⟩
      rw [hk] at this
      simp [TM.steps, hd] at this
  · rintro ⟨m, d, hm, hd⟩
    exact ⟨n + m, d, TM.steps_seq δ h hm, hd⟩

/-! ## This machine -/

theorem iter_39 : iter 25 (.ps 0 39) = some (.q 3 2 46) := by decide
theorem iter_blank_83 : iter 83 (.ps 0 2) = some (.q 3 2 46) := by decide

/-- From `PS 0 39` the machine joins its own run from blank tape (in phase 83 of it, at `Q 3 2 46`). -/
theorem ps_0_39_iff : TM.Halts trans (PS 0 39) ↔ HaltsFromBlank := by
  obtain ⟨n1, -, h1⟩ := reach_iter 25 _ _ iter_39
  obtain ⟨n2, -, h2⟩ := reach_iter 83 _ _ iter_blank_83
  exact (halts_iff_of_steps trans h1).trans (halts_iff_of_steps trans (steps_seq trans init_ps h2)).symm

theorem iter_22_3 : iter 17 (.ps 22 3) = some (.ps 30 1) := by decide

/-- From `PS 22 3` the machine halts (17 phases to `PS 30 1`). -/
theorem ps_22_3_halts : TM.Halts trans (PS 22 3) := by
  obtain ⟨n, -, h⟩ := reach_iter 17 _ _ iter_22_3
  exact (halts_iff_of_steps trans h).2 (ps_halts 30 1 (by omega))

/-! ## The partner 1RB1LF_1RC1RF_0LD1RE_---1LC_0RB1RE_1LA0LE (bbchallenge id 21883) -/

namespace Partner

/-- The states. -/
inductive St where
  | A | B | C | D | E | F
  deriving DecidableEq, Repr

/-- The transition table of 1RB1LF_1RC1RF_0LD1RE_---1LC_0RB1RE_1LA0LE, as in its own folder's `Machine.lean`. -/
def trans : St → Bool → Option (Bool × Dir × St)
  | .A, false => some (true, .R, .B)
  | .A, true => some (true, .L, .F)
  | .B, false => some (true, .R, .C)
  | .B, true => some (true, .R, .F)
  | .C, false => some (false, .L, .D)
  | .C, true => some (true, .R, .E)
  | .D, false => none
  | .D, true => some (true, .L, .C)
  | .E, false => some (false, .R, .B)
  | .E, true => some (true, .R, .E)
  | .F, false => some (true, .L, .A)
  | .F, true => some (false, .L, .E)

/-- The partner halts from blank tape. -/
abbrev HaltsFromBlank : Prop := TM.Halts trans (TM.blankCfg .A)

end Partner

/-- The states of this machine as the partner's, after mirroring: D and E swap. -/
def ren : St → Partner.St
  | .A => .A | .B => .B | .C => .C | .D => .E | .E => .D | .F => .F

/-- The mirror image of a configuration (the head stays on its cell, left and right swap), states renamed. -/
def mirror (c : Config) : TM.Cfg Partner.St := ⟨tail c.r, cons (c.r 0) c.l, ren c.st⟩

/-! The two mirrored tapes as lists, for the list simulator. -/

/-- `mirror (PS 0 39)` = `0^inf 1^39 0 B> 0 0^inf` (the partner's right-end visit with a pool of 39 and no pairs). -/
def x39 : FCfg Partner.St := ⟨false :: List.replicate 39 true, [], .B⟩

/-- `mirror (PS 22 3)` = `0^inf 1^3 0 (10)^22 B> 0 0^inf`. -/
def x22 : FCfg Partner.St := ⟨(List.replicate 22 [false, true]).flatten ++ [false, true, true, true], [], .B⟩

theorem app_replicate (n : Nat) (w : List Bool) (s : Tape) : app (List.replicate n w).flatten s = rep n w s := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ← app_app, ih]

theorem rep_tf_eq (n : Nat) (s : Tape) : cons false (rep n [true, false] s) = rep n [false, true] (cons false s) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [← ih]

theorem mirror_39 : mirror (PS 0 39) = x39.toCfg := by
  simp only [mirror, PS, x39, FCfg.toCfg, tail_cons, cons_zero, rep_zero, app_cons, app_nil, ren]
  rw [cons_false_blank, show List.replicate 39 true = (List.replicate 39 [true]).flatten by decide, app_replicate]

theorem mirror_22 : mirror (PS 22 3) = x22.toCfg := by
  simp only [mirror, PS, x22, FCfg.toCfg, tail_cons, cons_zero, ← app_app, app_replicate, app_nil, rep_tf_eq, ren]
  rw [cons_false_blank]
  rfl

/-! ## The partner's runs -/

/-- A list configuration with its trailing blank cells dropped; `toCfg` does not see them. -/
def trim : List Bool → List Bool
  | [] => []
  | a :: l => if trim l = [] ∧ a = false then [] else a :: trim l

theorem app_trim : ∀ l : List Bool, app (trim l) blank = app l blank
  | [] => rfl
  | a :: l => by
    by_cases h : trim l = [] ∧ a = false
    · rw [trim, ite_eq_left_of_eq_true _ _ (eq_true h), app_cons, ← app_trim l, h.1, h.2]; exact cons_false_blank.symm
    · rw [trim, ite_eq_right_of_eq_false _ _ (eq_false h), app_cons, app_cons, app_trim l]

/-- Two list configurations that differ only in trailing blank cells. -/
def same (c d : FCfg Partner.St) : Bool := trim c.l == trim d.l && trim c.r == trim d.r && c.st == d.st

theorem toCfg_of_same {c d : FCfg Partner.St} (h : same c d = true) : c.toCfg = d.toCfg := by
  simp only [same, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hl, hr⟩, hs⟩ := h
  simp only [FCfg.toCfg]
  rw [← app_trim c.l, ← app_trim c.r, ← app_trim d.l, ← app_trim d.r, hl, hr, hs]

/-- `n` list steps from `c` end at a configuration that halts. -/
def haltsAt (n : Nat) (c : FCfg Partner.St) : Bool :=
  match TM.fsteps Partner.trans n c with
  | some d => (TM.fstep Partner.trans d).isNone
  | none => false

theorem halts_of_haltsAt {n : Nat} {c : FCfg Partner.St} (h : haltsAt n c = true) :
    TM.Halts Partner.trans c.toCfg := by
  unfold haltsAt at h
  split at h
  · rename_i d hd
    refine ⟨n, d.toCfg, by rw [FCfg.steps_eq, hd]; rfl, ?_⟩
    rw [FCfg.step_eq]
    cases e : TM.fstep Partner.trans d with
    | none => rfl
    | some _ => simp [e] at h
  · cases h

/-- `n` list steps from `c` and `m` from `d` end at the same configuration. -/
def meetAt (n : Nat) (c : FCfg Partner.St) (m : Nat) (d : FCfg Partner.St) : Bool :=
  match TM.fsteps Partner.trans n c, TM.fsteps Partner.trans m d with
  | some c', some d' => same c' d'
  | _, _ => false

theorem halts_iff_of_meetAt {n m : Nat} {c d : FCfg Partner.St} (h : meetAt n c m d = true) :
    TM.Halts Partner.trans c.toCfg ↔ TM.Halts Partner.trans d.toCfg := by
  unfold meetAt at h
  split at h
  · rename_i c' d' hc hd
    have h1 : TM.steps Partner.trans n c.toCfg = some c'.toCfg := by rw [FCfg.steps_eq, hc]; rfl
    have h2 : TM.steps Partner.trans m d.toCfg = some d'.toCfg := by rw [FCfg.steps_eq, hd]; rfl
    rw [halts_iff_of_steps _ h1, halts_iff_of_steps _ h2, toCfg_of_same h]
  · cases h

/-- From `mirror (PS 0 39)` the partner halts: its pool of 39 runs down to 1 (39 right-end visits, 44,274 steps). -/
theorem partner_halts_39 : TM.Halts Partner.trans (mirror (PS 0 39)) := by
  rw [mirror_39]; exact halts_of_haltsAt (n := 44274) (by native_decide)

/-- From `mirror (PS 22 3)` the partner reaches, after 1,499,945 steps, the configuration of its run from blank tape at
step 730,147 (the right-end visit `0^inf 1^204 0 (10)^58 B> 0`). -/
theorem partner_iff_22_3 : TM.Halts Partner.trans (mirror (PS 22 3)) ↔ Partner.HaltsFromBlank := by
  rw [mirror_22]; exact halts_iff_of_meetAt (n := 1499945) (m := 730147) (d := FCfg.blank .A) (by native_decide)

/-- **Halting together on two pairs of mirror-image tapes would force both machines to halt from blank tape.**  So
whether this machine and its partner halt together from blank tape is not decided by their tables. -/
theorem together_forces_halts
    (h39 : TM.Halts trans (PS 0 39) ↔ TM.Halts Partner.trans (mirror (PS 0 39)))
    (h22 : TM.Halts trans (PS 22 3) ↔ TM.Halts Partner.trans (mirror (PS 22 3))) :
    HaltsFromBlank ∧ Partner.HaltsFromBlank :=
  ⟨ps_0_39_iff.1 (h39.2 partner_halts_39), partner_iff_22_3.1 (h22.1 ps_22_3_halts)⟩

end H149707
