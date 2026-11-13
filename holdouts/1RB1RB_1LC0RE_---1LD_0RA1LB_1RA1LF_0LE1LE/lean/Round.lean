import Pieces

/-!
# The round map of 1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE

At the start of each round the head is at the right end of the tape in state B, and the tape is

  `R1 i j = 0^∞ 1^(2i) 0 1^(2j) 0 11 B> 0^∞`   or   `R2 i j = 0^∞ 1^(2i) 0 1^(2j) 0 11 0 11 B> 0^∞`.

The round is a three-block bouncer `K3`: blocks `a = 2p+2`, `b = 2q+1`, `c = 2r+e` at the left end; each inner
pass takes `a` and `b` down by 2 and `c` up by 6, until `a` or `b` runs out.  `next` is the resulting map on
`(i, j, J)` (`J = false` for `R1`, `true` for `R2`); it is `none` exactly when `i = j` or `i + 1 = j`, and then the
machine halts (`round`).  `halts_iff`: the machine halts from blank tape iff the orbit of `(3, 1, false)` under
`next` reaches `none`.  Everything here is checked by Lean's kernel (no `native_decide`).
-/

namespace H159080

open TM

abbrev tt : List Bool := [true, true]

/-- `0^∞ (11)^i 0 (11)^j 0 11 B> 0^∞`. -/
def R1 (i j : Nat) : Config := ⟨cons true (cons true (cons false (rep j tt (cons false (rep i tt blank))))), blank, .B⟩
/-- `0^∞ (11)^i 0 (11)^j 0 11 0 11 B> 0^∞`. -/
def R2 (i j : Nat) : Config :=
  ⟨cons true (cons true (cons false (cons true (cons true (cons false (rep j tt (cons false (rep i tt blank)))))))),
    blank, .B⟩
/-- `0^∞ (11)^p 0 11 B> 0^∞`, met inside two kinds of round. -/
def S (p : Nat) : Config := ⟨cons true (cons true (cons false (rep p tt blank))), blank, .B⟩
/-- The end of the last block: nothing, or one more 1. -/
def cend : Bool → Tape
  | false => blank
  | true => cons true blank
/-- `0^∞ E> 0 (11)^(p+1) 0 1 (11)^q 0 (11)^r [1] 0^∞`: blocks `2p+2`, `2q+1`, `2r+e`. -/
def K3 (p q r : Nat) (e : Bool) : Config :=
  ⟨blank, cons false (rep (p + 1) tt (cons false (cons true (rep q tt (cons false (rep r tt (cend e))))))), .E⟩
/-- The configuration at the start of a round. -/
def Rc (i j : Nat) : Bool → Config
  | false => R1 i j
  | true => R2 i j

def Reach (a b : Config) : Prop := ∃ n, steps n a = some b
/-- Reaches in at least one step. -/
def Adv (a b : Config) : Prop := ∃ n, 0 < n ∧ steps n a = some b

theorem reach_trans {a b c : Config} (h₁ : Reach a b) (h₂ : Reach b c) : Reach a c := by
  obtain ⟨n, h₁⟩ := h₁; obtain ⟨m, h₂⟩ := h₂; exact ⟨n + m, steps_seq trans h₁ h₂⟩

theorem adv_of_reach {a b c : Config} (h₁ : Reach a b) (h₂ : Adv b c) : Adv a c := by
  obtain ⟨n, h₁⟩ := h₁; obtain ⟨m, hm, h₂⟩ := h₂; exact ⟨n + m, by omega, steps_seq trans h₁ h₂⟩

theorem adv_trans {a b c : Config} (h₁ : Adv a b) (h₂ : Adv b c) : Adv a c := by
  obtain ⟨n, hn, h₁⟩ := h₁; obtain ⟨m, _, h₂⟩ := h₂; exact ⟨n + m, by omega, steps_seq trans h₁ h₂⟩

theorem reach_of_eq {n : Nat} {a b b' : Config} (h : steps n a = some b) (e : b = b') : Reach a b' :=
  ⟨n, e ▸ h⟩

theorem adv_of_eq {n : Nat} {a b b' : Config} (h : steps n a = some b) (hn : 0 < n) (e : b = b') : Adv a b' :=
  ⟨n, hn, e ▸ h⟩

theorem halts_of_reach {a b : Config} (h₁ : Reach a b) (h₂ : TM.Halts trans b) : TM.Halts trans a := by
  obtain ⟨n, h₁⟩ := h₁; obtain ⟨m, c, h₂, h₃⟩ := h₂; exact ⟨n + m, c, steps_seq trans h₁ h₂, h₃⟩

/-- `1 (11)^p 1 = (11)^(p+1)`. -/
theorem T1 (p : Nat) (s : Tape) : cons true (rep p tt (cons true s)) = rep (p + 1) tt s := by
  have h := rep_rotate p [true] tt tt rfl (cons true s)
  simp only [app] at h
  rw [h, ← rep_app_comm]; rfl

/-! ## One inner pass, and many -/

theorem pass_e (p q r : Nat) : Reach (K3 (p + 1) (q + 2) r false) (K3 p (q + 1) (r + 3) false) := by
  have h := inner_e p q r
  rw [cons_false_blank] at h
  exact reach_of_eq h (by unfold K3; rw [← T1 p] <;> rfl)

theorem pass_o (p q r : Nat) : Reach (K3 (p + 1) (q + 2) r true) (K3 p (q + 1) (r + 3) true) := by
  have h := inner_o p q r
  rw [cons_false_blank] at h
  exact reach_of_eq h (by unfold K3; rw [← T1 p] <;> rfl)

theorem pass1_e (p r : Nat) : Reach (K3 (p + 1) 1 r false) (K3 p 0 (r + 3) false) := by
  have h := inner1_e p r
  rw [cons_false_blank] at h
  exact reach_of_eq h (by unfold K3; rw [← T1 p] <;> rfl)

theorem pass1_o (p r : Nat) : Reach (K3 (p + 1) 1 r true) (K3 p 0 (r + 3) true) := by
  have h := inner1_o p r
  rw [cons_false_blank] at h
  exact reach_of_eq h (by unfold K3; rw [← T1 p] <;> rfl)

theorem pass (p q r : Nat) (e : Bool) : Reach (K3 (p + 1) (q + 1) r e) (K3 p q (r + 3) e) := by
  cases q with
  | zero => cases e; exact pass1_e p r; exact pass1_o p r
  | succ q => cases e; exact pass_e p q r; exact pass_o p q r

/-- `m` inner passes. -/
theorem passes (m : Nat) : ∀ (p q r : Nat) (e : Bool), Reach (K3 (p + m) (q + m) r e) (K3 p q (r + 3 * m) e) := by
  induction m with
  | zero => intro p q r e; exact ⟨0, rfl⟩
  | succ m ih =>
    intro p q r e
    have h₁ := pass (p + m) (q + m) r e
    have h₂ := ih p q (r + 3) e
    rw [show r + 3 + 3 * m = r + 3 * (m + 1) by omega] at h₂
    exact reach_trans h₁ h₂

/-! ## The ends of a round -/

theorem end_b (p r : Nat) (e : Bool) : Adv (K3 (p + 3) 0 r e) (Rc (p + 1) (r + 5) e) := by
  cases e
  · have h := eb_e p r
    rw [cons_false_blank] at h
    exact adv_of_eq h (by omega) (by simp only [Rc, R1]; rw [rep_add r 5, ← rep_app_comm p] <;> rfl)
  · have h := eb_o p r
    rw [cons_false_blank] at h
    exact adv_of_eq h (by omega) (by simp only [Rc, R2]; rw [rep_add r 5, ← rep_app_comm p] <;> rfl)

theorem s_run (p : Nat) : Adv (S (p + 3)) (R2 (p + 1) 3) := by
  have h := s3 p
  exact adv_of_eq h (by omega) (by simp only [R2]; rw [← rep_app_comm p] <;> rfl)

theorem end_b2 (r : Nat) (e : Bool) :
    Adv (K3 2 0 r e) (match e with | false => R2 (r + 3) 3 | true => R1 (r + 5) 1) := by
  cases e
  · have h := eb2_e r
    rw [cons_false_blank] at h
    have h₁ : Adv (K3 2 0 r false) (S (r + 2 + 3)) := by
      exact adv_of_eq h (by omega) (by simp only [S]; rw [rep_add r 5] <;> rfl)
    exact adv_trans h₁ (s_run (r + 2))
  · have h := eb2_o r
    rw [cons_false_blank] at h
    exact adv_of_eq h (by omega) (by simp only [R1]; rw [rep_add r 5] <;> rfl)

theorem end_a (q r : Nat) (e : Bool) :
    Adv (K3 0 (q + 2) r e) (match e with | false => R2 (q + 1) (r + 3) | true => R1 (q + 1) (r + 4)) := by
  cases e
  · have h := ea_e q r
    rw [cons_false_blank] at h
    exact adv_of_eq h (by omega) (by simp only [R2]; rw [rep_add r 3, ← rep_app_comm q] <;> rfl)
  · have h := ea_o q r
    rw [cons_false_blank] at h
    exact adv_of_eq h (by omega) (by
      simp only [R1]
      rw [show r + 4 = 1 + (r + 3) by omega, rep_add 1 (r + 3), rep_add r 3, ← rep_app_comm q] <;> rfl)

theorem end_a1 (r : Nat) (e : Bool) :
    Adv (K3 0 1 r e) (match e with | false => R1 (r + 3) 1 | true => R2 (r + 2) 3) := by
  cases e
  · have h := ea1_e r
    rw [cons_false_blank] at h
    exact adv_of_eq h (by omega) (by simp only [R1]; rw [rep_add r 3] <;> rfl)
  · have h := ea1_o r
    rw [cons_false_blank] at h
    have h₁ : Adv (K3 0 1 r true) (S (r + 1 + 3)) := by
      exact adv_of_eq h (by omega) (by
        simp only [S]; rw [show r + 1 + 3 = 1 + (r + 3) by omega, rep_add 1 (r + 3), rep_add r 3] <;> rfl)
    exact adv_trans h₁ (s_run (r + 1))

theorem halt_1 (r : Nat) (e : Bool) : TM.Halts trans (K3 1 0 r e) := by
  cases e
  · have h := halt1_e r; rw [cons_false_blank] at h; exact ⟨_, _, h, rfl⟩
  · have h := halt1_o r; rw [cons_false_blank] at h; exact ⟨_, _, h, rfl⟩

theorem halt_0 (r : Nat) (e : Bool) : TM.Halts trans (K3 0 0 r e) := by
  cases e
  · have h := halt0_e r; rw [cons_false_blank] at h; exact ⟨_, _, h, rfl⟩
  · have h := halt0_o r; rw [cons_false_blank] at h; exact ⟨_, _, h, rfl⟩

/-- The last block after the start of a round: `c = 6` or `c = 9`. -/
def r0 : Bool → Nat
  | false => 3
  | true => 4

/-- The start of a round with `j ≥ 2`: `c = 6` after an `R1`, `c = 9` after an `R2`. -/
theorem start (i j : Nat) (J : Bool) :
    Reach (Rc (i + 1) (j + 2) J) (K3 i j (r0 J) J) := by
  cases J
  · have h := start1 i j
    exact reach_of_eq h (by simp only [K3, cend, r0]; rw [← T1 i] <;> rfl)
  · have h := start2 i j
    exact reach_of_eq h (by simp only [K3, cend, r0]; rw [← T1 i] <;> rfl)

/-! ## The round map -/

/-- One round, on `(i, j, J)`; `none`: the machine halts during the round. -/
def next (i j : Nat) (J : Bool) : Option (Nat × Nat × Bool) :=
  if i = j ∨ i + 1 = j then none
  else if j + 2 ≤ i then some (i - j - 1, (match J with | false => 3 * j + 2 | true => 3 * j + 3), J)
  else if i = j + 1 then (match J with | false => some (3 * i - 3, 3, true) | true => some (3 * i, 1, false))
  else if i + 2 = j then (match J with | false => some (3 * i + 3, 1, false) | true => some (3 * i + 3, 3, true))
  else some (j - i - 2, (match J with | false => 3 * i + 3 | true => 3 * i + 5), !J)

/-- The states that occur: `R2` only with `j ≥ 2`. -/
def Valid (i j : Nat) (J : Bool) : Prop := 1 ≤ i ∧ 1 ≤ j ∧ (J = true → 2 ≤ j)

/-- Close `next a b J = x` for concrete branches: split every `if` and let `omega` pick the branch. -/
macro "nextcases" : tactic => `(tactic| (repeat' split) <;> first
  | contradiction
  | (exfalso; omega)
  | rfl
  | (simp only [Option.some.injEq, Prod.mk.injEq, and_true, true_and, Bool.not_false, Bool.not_true]; omega)
  | (simp only [Option.some.injEq, Prod.mk.injEq, and_true, true_and, Bool.not_false, Bool.not_true]))

/-- What a round does: the machine goes from round to round as `next` says, or halts when `next` is `none`. -/
def RoundOk (i j : Nat) (J : Bool) : Prop :=
  match next i j J with
  | none => TM.Halts trans (Rc i j J)
  | some (i', j', J') => Adv (Rc i j J) (Rc i' j' J') ∧ Valid i' j' J'

/-- The rounds from `R1 i 1`. -/
theorem round_j1 (i : Nat) (hi : 1 ≤ i) : RoundOk i 1 false := by
  match i, hi with
  | 1, _ =>
    show TM.Halts trans (R1 1 1)
    exact ⟨_, _, r1_11, rfl⟩
  | 2, _ =>
    show Adv (R1 2 1) (R2 3 3) ∧ Valid 3 3 true
    refine ⟨?_, ⟨by omega, by omega, by intro h; first | omega | cases h⟩⟩
    have h₁ : Adv (R1 2 1) (S (2 + 3)) := ⟨_, by omega, r1_21⟩
    exact adv_trans h₁ (s_run 2)
  | p + 3, _ =>
    have hn : next (p + 3) 1 false = some (p + 1, 5, false) := by
      simp only [next]
      rw [if_neg (by omega), if_pos (by omega)]
      try (simp only [Option.some.injEq, Prod.mk.injEq, and_true, true_and, Bool.not_false, Bool.not_true]; try omega)
    unfold RoundOk; rw [hn]; dsimp only
    refine ⟨?_, ⟨by omega, by omega, by intro h; first | omega | cases h⟩⟩
    have h := r1j1 p
    exact adv_of_eq h (by omega) (by simp only [Rc, R1]; rw [← rep_app_comm p] <;> rfl)

theorem round_ok (i j : Nat) (J : Bool) (hv : Valid i j J) : RoundOk i j J := by
  obtain ⟨hi, hj, hJ⟩ := hv
  by_cases j1 : j = 1
  · subst j1
    cases J
    · exact round_j1 i hi
    · exact absurd (hJ rfl) (by omega)
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 2 := ⟨j - 2, by omega⟩
  have hs := start i' j' J
  -- inner passes until a or b runs out
  by_cases hab : j' ≤ i'
  · obtain ⟨p, rfl⟩ : ∃ p, i' = p + j' := ⟨i' - j', by omega⟩
    have hk := passes j' p 0 (r0 J) J
    simp only [Nat.zero_add] at hk
    have hk' := reach_trans hs hk
    -- now K3 p 0 r J with r = r0 + 3 j'
    match p with
    | 0 =>
      have hn : next (0 + j' + 1) (j' + 2) J = none := by unfold next; nextcases
      unfold RoundOk; rw [hn]; exact halts_of_reach hk' (halt_0 _ _)
    | 1 =>
      have hn : next (1 + j' + 1) (j' + 2) J = none := by unfold next; nextcases
      unfold RoundOk; rw [hn]; exact halts_of_reach hk' (halt_1 _ _)
    | 2 =>
      have he := adv_of_reach hk' (end_b2 _ J)
      cases J
      · have hn : next (2 + j' + 1) (j' + 2) false = some (3 * j' + 6, 3, true) := by
          unfold next; nextcases
        unfold RoundOk; rw [hn]; dsimp only
        refine ⟨?_, ⟨by omega, by omega, by intro h; first | omega | cases h⟩⟩
        simp only [Rc]; rw [show 3 * j' + 6 = 3 + 3 * j' + 3 by omega]; exact he
      · have hn : next (2 + j' + 1) (j' + 2) true = some (3 * j' + 9, 1, false) := by
          unfold next; nextcases
        unfold RoundOk; rw [hn]; dsimp only
        refine ⟨?_, ⟨by omega, by omega, by intro h; first | omega | cases h⟩⟩
        simp only [Rc]; rw [show 3 * j' + 9 = 4 + 3 * j' + 5 by omega]; exact he
    | p + 3 =>
      have he := adv_of_reach hk' (end_b p _ J)
      cases J
      · have hn : next (p + 3 + j' + 1) (j' + 2) false = some (p + 1, 3 * j' + 8, false) := by
          unfold next; nextcases
        unfold RoundOk; rw [hn]; dsimp only
        refine ⟨?_, ⟨by omega, by omega, by intro h; first | omega | cases h⟩⟩
        rw [show 3 * j' + 8 = 3 + 3 * j' + 5 by omega]; exact he
      · have hn : next (p + 3 + j' + 1) (j' + 2) true = some (p + 1, 3 * j' + 9, true) := by
          unfold next; nextcases
        unfold RoundOk; rw [hn]; dsimp only
        refine ⟨?_, ⟨by omega, by omega, by intro h; first | omega | cases h⟩⟩
        rw [show 3 * j' + 9 = 4 + 3 * j' + 5 by omega]; exact he
  · obtain ⟨q, rfl⟩ : ∃ q, j' = i' + q + 1 := ⟨j' - i' - 1, by omega⟩
    have hk := passes i' 0 (q + 1) (r0 J) J
    simp only [Nat.zero_add] at hk
    rw [show q + 1 + i' = i' + q + 1 by omega] at hk
    have hk' := reach_trans hs hk
    cases q with
    | zero =>
      have he := adv_of_reach hk' (end_a1 _ J)
      cases J
      · have hn : next (i' + 1) (i' + 0 + 1 + 2) false = some (3 * i' + 6, 1, false) := by
          unfold next; nextcases
        unfold RoundOk; rw [hn]; dsimp only
        refine ⟨?_, ⟨by omega, by omega, by intro h; first | omega | cases h⟩⟩
        simp only [Rc]; rw [show 3 * i' + 6 = 3 + 3 * i' + 3 by omega]; exact he
      · have hn : next (i' + 1) (i' + 0 + 1 + 2) true = some (3 * i' + 6, 3, true) := by
          unfold next; nextcases
        unfold RoundOk; rw [hn]; dsimp only
        refine ⟨?_, ⟨by omega, by omega, by intro h; first | omega | cases h⟩⟩
        simp only [Rc]; rw [show 3 * i' + 6 = 4 + 3 * i' + 2 by omega]; exact he
    | succ q =>
      have he := adv_of_reach hk' (end_a q _ J)
      cases J
      · have hn : next (i' + 1) (i' + (q + 1) + 1 + 2) false = some (q + 1, 3 * i' + 6, true) := by
          unfold next; nextcases
        unfold RoundOk; rw [hn]; dsimp only
        refine ⟨?_, ⟨by omega, by omega, by intro h; first | omega | cases h⟩⟩
        simp only [Rc]; rw [show 3 * i' + 6 = 3 + 3 * i' + 3 by omega]; exact he
      · have hn : next (i' + 1) (i' + (q + 1) + 1 + 2) true = some (q + 1, 3 * i' + 8, false) := by
          unfold next; nextcases
        unfold RoundOk; rw [hn]; dsimp only
        refine ⟨?_, ⟨by omega, by omega, by intro h; first | omega | cases h⟩⟩
        simp only [Rc]; rw [show 3 * i' + 8 = 4 + 3 * i' + 4 by omega]; exact he

/-! ## From blank tape -/

/-- The orbit of the first round state under `next`. -/
def orb : Nat → Option (Nat × Nat × Bool)
  | 0 => some (3, 1, false)
  | n + 1 => match orb n with
    | none => none
    | some (i, j, J) => next i j J

theorem init_reach : steps 74 init = some (Rc 3 1 false) := init_run

theorem orb_reach (n : Nat) : ∀ i j J, orb n = some (i, j, J) →
    Valid i j J ∧ ∃ m, n ≤ m ∧ steps m init = some (Rc i j J) := by
  induction n with
  | zero =>
    intro i j J h
    simp only [orb, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨⟨by omega, by omega, by intro h; first | omega | cases h⟩, 74, by omega, init_reach⟩
  | succ n ih =>
    intro i' j' J' h
    simp only [orb] at h
    cases ho : orb n with
    | none => rw [ho] at h; cases h
    | some s =>
      obtain ⟨i, j, J⟩ := s
      rw [ho] at h
      obtain ⟨hv, m, hm, hr⟩ := ih i j J ho
      have hr2 := round_ok i j J hv
      unfold RoundOk at hr2
      simp only at h
      rw [h] at hr2
      obtain ⟨⟨k, hk, hs⟩, hv'⟩ := hr2
      exact ⟨hv', m + k, by omega, steps_seq trans hr hs⟩

theorem orb_none (n : Nat) (h : orb n = none) : ∃ k i j J, orb k = some (i, j, J) ∧ next i j J = none := by
  induction n with
  | zero => simp [orb] at h
  | succ n ih =>
    cases ho : orb n with
    | none => exact ih ho
    | some s =>
      obtain ⟨i, j, J⟩ := s
      simp only [orb, ho] at h
      exact ⟨n, i, j, J, ho, h⟩

/-- **The reduction.**  The machine halts from blank tape iff the orbit of `(3, 1, false)` under `next` reaches a
state with `i = j` or `i + 1 = j`. -/
theorem halts_iff : HaltsFromBlank ↔ ∃ n, orb n = none := by
  constructor
  · intro hh
    apply Classical.byContradiction
    intro hno
    have hall : ∀ n, ∃ s, orb n = some s := by
      intro n
      cases ho : orb n with
      | none => exact absurd ⟨n, ho⟩ hno
      | some s => exact ⟨s, rfl⟩
    apply not_halts_of_forall trans _ hh
    apply forall_of_unbounded trans (fun m => ∃ c, steps m init = some c)
    · intro n
      obtain ⟨⟨i, j, J⟩, hs⟩ := hall n
      obtain ⟨_, m, hm, hr⟩ := orb_reach n i j J hs
      exact ⟨m, hm, _, hr⟩
    · intro m hm; exact hm
  · intro ⟨n, hn⟩
    obtain ⟨k, i, j, J, hk, hnext⟩ := orb_none n hn
    obtain ⟨hv, m, _, hr⟩ := orb_reach k i j J hk
    have hr2 := round_ok i j J hv
    unfold RoundOk at hr2
    rw [hnext] at hr2
    exact halts_of_reach ⟨m, hr⟩ hr2

end H159080
