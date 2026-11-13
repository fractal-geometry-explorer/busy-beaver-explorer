import Machine
import Rules
import Blank

/-!
# 1RB1RE_1LC1LD_---1LA_1LB1LE_0RF0RA_1LD1RF: the run as an arithmetic iteration

Written by hand on top of the generated `Rules.lean`.  `P c u x` is the configuration

    0^inf 1^c (01)^u 0 0 (10)^x F> 0^inf

(state F just right of the tape).  One *phase* takes `P (c+4) u x` to `P c u' x'` with
`X = x + u + 4`, `u' = 2 + X % 2`, `x' = 3 (X / 2) - 1` (`phase`): the run of 1s on the left loses 4 cells and the
block on the right grows by a factor 3/2.  An *epoch* starts at `P c 3 5` and makes `c / 4` phases; then
`c % 4` and `u` decide (`ends`): a new epoch `P c' 3 5`, or a halt.  The main theorem `halts_iff` says that the
machine halts from blank tape exactly when the epoch iteration `epochs` reaches `none`.
-/

namespace H116538

open TM

/-- `0^inf 1^c (01)^u 0 0 (10)^x F> 0^inf`. -/
def P (c u x : Nat) : Config :=
  ⟨rep x [false, true] (cons false (cons false (rep u [true, false] (rep c [true] blank)))), blank, .F⟩

/-! ## Tape identities -/

theorem rot_ft (y : Nat) (T : Tape) : cons false (rep y [true, false] T) = rep y [false, true] (cons false T) :=
  rep_rotate y [false] [true, false] [false, true] rfl T

theorem rot_tf (y : Nat) (T : Tape) : cons true (rep y [false, true] T) = rep y [true, false] (cons true T) :=
  rep_rotate y [true] [false, true] [true, false] rfl T

theorem rep_ft_cons (n : Nat) (s : Tape) :
    rep n [false, true] (cons false (cons true s)) = rep (n + 1) [false, true] s :=
  rep_app_comm n [false, true] s

theorem rep_tf_cons (n : Nat) (s : Tape) :
    rep n [true, false] (cons true (cons false s)) = rep (n + 1) [true, false] s :=
  rep_app_comm n [true, false] s

theorem rep_t_cons (n : Nat) (s : Tape) : rep n [true] (cons true s) = rep (n + 1) [true] s :=
  rep_app_comm n [true] s

theorem rep_tt (n : Nat) (s : Tape) : rep n [true, true] s = rep (2 * n) [true] s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega]
    show cons true (cons true (rep n [true, true] s)) = cons true (rep (2 * n + 1) [true] s)
    rw [ih]; rfl

theorem cons_t_rep (n : Nat) (s : Tape) : cons true (rep n [true] s) = rep (n + 1) [true] s := rfl

/-! ## One bounce, and k bounces -/

theorem bounce' (x y : Nat) (L : Tape) :
    steps (4 * y + 18) ⟨rep (y + 1) [false, true] (cons false (cons false (rep (x + 2) [true, false] L))), blank, .F⟩ =
      some ⟨rep (y + 4) [false, true] (cons false (cons false (rep x [true, false] L))), blank, .F⟩ := by
  have h := bounce x y L
  rw [rot_ft y, rep_ft_cons, rep_ft_cons, rep_ft_cons] at h
  exact h

theorem bounce_iter (k x y : Nat) (L : Tape) : ∃ n,
    steps n ⟨rep (y + 1) [false, true] (cons false (cons false (rep (x + 2 * k) [true, false] L))), blank, .F⟩ =
      some ⟨rep (y + 1 + 3 * k) [false, true] (cons false (cons false (rep x [true, false] L))), blank, .F⟩ := by
  induction k generalizing y with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    obtain ⟨n, hn⟩ := ih (y + 3)
    refine ⟨4 * y + 18 + n, ?_⟩
    have hb := bounce' (x + 2 * k) y L
    rw [show x + 2 * (k + 1) = x + 2 * k + 2 by omega, show y + 1 + 3 * (k + 1) = y + 3 + 1 + 3 * k by omega]
    exact steps_seq trans hb hn

/-! ## One phase -/

/-- The phase map on `(u, x)`. -/
def ph (p : Nat × Nat) : Nat × Nat :=
  (2 + (p.2 + p.1 + 4) % 2, 3 * ((p.2 + p.1 + 4) / 2) - 1)

theorem glue2' (c x : Nat) : steps (12 * x + 88) (P (c + 4) 2 (x + 1)) =
    some ⟨rep 2 [false, true] (cons false (cons false (rep (x + 7) [true, false] (rep c [true] blank)))), blank, .F⟩ := by
  have h := glue2 c x
  rw [rot_tf x, rep_tf_cons, rep_tf_cons, rep_tf_cons, rep_tf_cons, rep_tf_cons, rep_tf_cons, rep_tf_cons] at h
  exact h

theorem glue3' (c x : Nat) : steps (12 * x + 96) (P (c + 4) 3 (x + 1)) =
    some ⟨rep 2 [false, true] (cons false (cons false (rep (x + 8) [true, false] (rep c [true] blank)))), blank, .F⟩ := by
  have h := glue3 c x
  rw [rot_tf x, rep_tf_cons, rep_tf_cons, rep_tf_cons, rep_tf_cons, rep_tf_cons, rep_tf_cons, rep_tf_cons, rep_tf_cons] at h
  exact h

/-- From the configuration after the glue, with `X` units on the left, to the next `P`. -/
theorem after_glue (c X : Nat) (hX : 4 ≤ X) : ∃ n,
    steps n ⟨rep 2 [false, true] (cons false (cons false (rep X [true, false] (rep c [true] blank)))), blank, .F⟩ =
      some (P c (2 + X % 2) (3 * (X / 2) - 1)) := by
  obtain ⟨n, hn⟩ := bounce_iter (X / 2 - 1) (2 + X % 2) 1 (rep c [true] blank)
  refine ⟨n, ?_⟩
  rw [show 2 + X % 2 + 2 * (X / 2 - 1) = X by omega, show 1 + 1 + 3 * (X / 2 - 1) = 3 * (X / 2) - 1 by omega] at hn
  exact hn

def Good (p : Nat × Nat) : Prop := (p.1 = 2 ∨ p.1 = 3) ∧ 16 ≤ p.2

theorem phase (c : Nat) (p : Nat × Nat) (hp : p.1 = 2 ∨ p.1 = 3) (hx : 1 ≤ p.2) :
    ∃ n, 1 ≤ n ∧ steps n (P (c + 4) p.1 p.2) = some (P c (ph p).1 (ph p).2) := by
  obtain ⟨u, x⟩ := p
  obtain ⟨x, rfl⟩ : ∃ x', x = x' + 1 := ⟨x - 1, by simp at hx; omega⟩
  simp only at hp
  rcases hp with rfl | rfl
  · obtain ⟨n, hn⟩ := after_glue c (x + 7) (by omega)
    refine ⟨12 * x + 88 + n, by omega, ?_⟩
    have e : (ph (2, x + 1)) = (2 + (x + 7) % 2, 3 * ((x + 7) / 2) - 1) := by
      simp only [ph] <;> omega
    rw [e]
    exact steps_seq trans (glue2' c x) hn
  · obtain ⟨n, hn⟩ := after_glue c (x + 8) (by omega)
    refine ⟨12 * x + 96 + n, by omega, ?_⟩
    have e : (ph (3, x + 1)) = (2 + (x + 8) % 2, 3 * ((x + 8) / 2) - 1) := by
      simp only [ph] <;> omega
    rw [e]
    exact steps_seq trans (glue3' c x) hn

theorem ph_good (p : Nat × Nat) (h : Good p) : Good (ph p) := by
  obtain ⟨u, x⟩ := p
  simp only [Good, ph] at *
  omega

/-- `n` phases. -/
def phN : Nat → Nat × Nat → Nat × Nat
  | 0, p => p
  | n + 1, p => phN n (ph p)

theorem phN_good (n : Nat) (p : Nat × Nat) (h : Good p) : Good (phN n p) := by
  induction n generalizing p with
  | zero => exact h
  | succ n ih => exact ih (ph p) (ph_good p h)

theorem phases (N r : Nat) (p : Nat × Nat) (h : Good p) :
    ∃ n, steps n (P (4 * N + r) p.1 p.2) = some (P r (phN N p).1 (phN N p).2) := by
  induction N generalizing p with
  | zero => exact ⟨0, by simp [phN]⟩
  | succ N ih =>
    obtain ⟨n₁, -, h₁⟩ := phase (4 * N + r) p h.1 (by have := h.2; omega)
    obtain ⟨n₂, h₂⟩ := ih (ph p) (ph_good p h)
    refine ⟨n₁ + n₂, ?_⟩
    rw [show 4 * (N + 1) + r = 4 * N + r + 4 by omega]
    exact steps_seq trans h₁ h₂

/-! ## Epoch ends -/

/-- How an epoch ends, from `P r u x` (`r < 4`): `some c'` for the next epoch `P c' 3 5`, `none` for a halt. -/
def endv (r u x : Nat) : Option Nat :=
  if r = 3 then some (2 * x + 4 + 2 * u)
  else if (r = 0 ∧ u = 3) ∨ (r = 1 ∧ u = 2) then some (2 * x + 5)
  else none

/-- The epoch from `P c 3 5`: `some c'` for the next epoch `P c' 3 5`, `none` for a halt. -/
def ends (c : Nat) : Option Nat :=
  let p := phN (c / 4) (3, 5)
  endv (c % 4) p.1 p.2

theorem ones_eq (a b : Nat) : rep a [true, true] (rep b [true] (cons false blank)) = rep (2 * a + b) [true] blank := by
  rw [cons_false_blank, rep_tt, ← rep_add]

theorem P12 (x : Nat) : P 1 2 x = P 0 3 x := by
  unfold P
  rw [show rep 2 [true, false] (rep 1 [true] blank) = rep 3 [true, false] (rep 0 [true] blank) by
    show cons true (cons false (cons true (cons false (cons true blank)))) =
      cons true (cons false (cons true (cons false (cons true (cons false blank)))))
    rw [cons_false_blank]]

theorem P_end03 (x : Nat) : ∃ n, 1 ≤ n ∧ steps n (P 0 3 (x + 16)) = some (P (2 * (x + 16) + 5) 3 5) := by
  refine ⟨8 * x + 259, by omega, ?_⟩
  unfold P
  rw [show 2 * (x + 16) + 5 = (2 * (x + 13) + 10) + 1 by omega, ← cons_t_rep, ← ones_eq]
  exact end03 x

theorem P_end32 (x : Nat) : ∃ n, 1 ≤ n ∧ steps n (P 3 2 (x + 16)) = some (P (2 * (x + 16) + 4 + 2 * 2) 3 5) := by
  refine ⟨12 * x + 349, by omega, ?_⟩
  unfold P
  rw [show 2 * (x + 16) + 4 + 2 * 2 = 2 * (x + 14) + 12 by omega, ← ones_eq]
  exact end32 x

theorem P_end33 (x : Nat) : ∃ n, 1 ≤ n ∧ steps n (P 3 3 (x + 16)) = some (P (2 * (x + 16) + 4 + 2 * 3) 3 5) := by
  refine ⟨12 * x + 357, by omega, ?_⟩
  unfold P
  rw [show 2 * (x + 16) + 4 + 2 * 3 = 2 * (x + 14) + 14 by omega, ← ones_eq]
  exact end33 x

theorem halts_of {n : Nat} {c : Config} {l r : Tape} (h : steps n c = some ⟨l, cons false r, .C⟩) : Halts trans c :=
  ⟨n, _, h, (step_none_iff _).2 ⟨rfl, rfl⟩⟩

theorem halts_seq {n : Nat} {c c' : Config} (h : steps n c = some c') (h' : Halts trans c') : Halts trans c := by
  obtain ⟨m, d, hm, hd⟩ := h'
  exact ⟨n + m, d, steps_seq trans h hm, hd⟩

theorem end_some (r u x c' : Nat) (hr : r < 4) (hu : u = 2 ∨ u = 3) (hx : 16 ≤ x) (h : endv r u x = some c') :
    ∃ n, 1 ≤ n ∧ steps n (P r u x) = some (P c' 3 5) := by
  obtain ⟨x, rfl⟩ : ∃ y, x = y + 16 := ⟨x - 16, by omega⟩
  have : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl <;> rcases hu with rfl | rfl <;> simp [endv] at h <;> subst h
  · exact P_end03 x
  · rw [P12]; exact P_end03 x
  · exact P_end32 x
  · exact P_end33 x

theorem end_none (r u x : Nat) (hr : r < 4) (hu : u = 2 ∨ u = 3) (hx : 16 ≤ x) (h : endv r u x = none) :
    Halts trans (P r u x) := by
  obtain ⟨x, rfl⟩ : ∃ y, x = y + 16 := ⟨x - 16, by omega⟩
  have : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl <;> rcases hu with rfl | rfl <;> simp [endv] at h
  · exact halts_of (end02 x)
  · exact halts_of (end13 x)
  · exact halts_of (end22 x)
  · exact halts_of (end23 x)

/-! ## Epochs -/

/-- The first epoch, `P 3 3 5`, makes no phase. -/
theorem P_first : steps 225 (P 3 3 5) = some (P 20 3 5) := by
  unfold P
  rw [show (20 : Nat) = 2 * 3 + 14 by rfl, ← ones_eq]
  exact first

theorem P_start : steps 139 init = some (P 3 3 5) := by
  have h := start
  rw [cons_false_blank] at h
  exact h

theorem ph35 : ph (3, 5) = (2, 17) := rfl

/-- One epoch, from `P c 3 5`. -/
theorem epoch (c : Nat) (hc : c = 3 ∨ 4 ≤ c) :
    (∀ c', ends c = some c' → 4 ≤ c' ∧ ∃ n, 1 ≤ n ∧ steps n (P c 3 5) = some (P c' 3 5)) ∧
      (ends c = none → Halts trans (P c 3 5)) := by
  rcases hc with rfl | hc
  · have e : ends 3 = some 20 := rfl
    rw [e]
    refine ⟨fun c' h => ?_, fun h => nomatch h⟩
    cases h
    exact ⟨by omega, 225, by omega, P_first⟩
  obtain ⟨M, r, hr, rfl⟩ : ∃ M r, r < 4 ∧ c = 4 * M + r + 4 := ⟨c / 4 - 1, c % 4, by omega, by omega⟩
  have e : ends (4 * M + r + 4) = endv r (phN M (2, 17)).1 (phN M (2, 17)).2 := by
    simp only [ends]
    rw [show (4 * M + r + 4) / 4 = M + 1 by omega, show (4 * M + r + 4) % 4 = r by omega]
    rfl
  have hg := phN_good M (2, 17) ⟨Or.inl rfl, by omega⟩
  obtain ⟨n₁, hn₁, h₁⟩ := phase (4 * M + r) (3, 5) (Or.inr rfl) (by omega)
  rw [ph35] at h₁
  obtain ⟨n₂, h₂⟩ := phases M r (2, 17) ⟨Or.inl rfl, by omega⟩
  have h₁₂ := steps_seq trans h₁ h₂
  rw [e]
  refine ⟨fun c' h => ?_, fun h => halts_seq h₁₂ (end_none r _ _ hr hg.1 hg.2 h)⟩
  obtain ⟨n₃, hn₃, h₃⟩ := end_some r _ _ c' hr hg.1 hg.2 h
  refine ⟨?_, n₁ + n₂ + n₃, by omega, steps_seq trans h₁₂ h₃⟩
  have := hg.2
  simp only [endv] at h
  split at h
  · cases h; omega
  · split at h
    · cases h; omega
    · cases h

/-- The epoch iteration: `epochs k` is the `c` of the `k`-th epoch `P c 3 5`, or `none` after a halt. -/
def epochs : Nat → Option Nat
  | 0 => some 3
  | k + 1 => (epochs k).bind ends

theorem reach (k : Nat) :
    (∀ c, epochs k = some c → (c = 3 ∨ 4 ≤ c) ∧ ∃ n, k ≤ n ∧ steps n init = some (P c 3 5)) ∧
      (epochs k = none → Halts trans init) := by
  induction k with
  | zero =>
    refine ⟨fun c h => ?_, fun h => nomatch h⟩
    cases h
    exact ⟨Or.inl rfl, 139, by omega, P_start⟩
  | succ k ih =>
    cases hk : epochs k with
    | none =>
      have hh := ih.2 hk
      exact ⟨fun c h => by simp [epochs, hk] at h, fun _ => hh⟩
    | some c =>
      obtain ⟨hc, n, hn, h⟩ := ih.1 c hk
      have ee := epoch c hc
      have e : epochs (k + 1) = ends c := by simp [epochs, hk]
      rw [e]
      refine ⟨fun c' h' => ?_, fun h' => halts_seq h (ee.2 h')⟩
      obtain ⟨hc', m, hm, h''⟩ := ee.1 c' h'
      exact ⟨Or.inr hc', n + m, by omega, steps_seq trans h h''⟩

/-- **The machine halts from blank tape exactly when the epoch iteration reaches `none`.** -/
theorem halts_iff : HaltsFromBlank ↔ ∃ k, epochs k = none := by
  constructor
  · intro hH
    apply Classical.byContradiction
    intro hne
    apply not_halts_of_forall trans _ hH
    apply forall_of_unbounded trans (fun m => ∃ c', steps m init = some c')
    · intro k
      cases hk : epochs k with
      | none => exact absurd ⟨k, hk⟩ hne
      | some c =>
        obtain ⟨-, n, hn, h⟩ := (reach k).1 c hk
        exact ⟨n, hn, _, h⟩
    · exact fun _ h => h
  · rintro ⟨k, hk⟩
    exact (reach k).2 hk

/-- The first epochs, evaluated by the kernel: `P 3 3 5`, `P 20 3 5`, `P 297 3 5`, `P 459271258863231 3 5`. -/
theorem epochs_first : epochs 1 = some 20 ∧ epochs 2 = some 297 ∧ epochs 3 = some 459271258863231 := by
  decide +kernel

/-- Epoch 3 ends with a new epoch too (`459271258863231 % 4 = 3`), whatever its phases do. -/
theorem epochs_4 : (epochs 4).isSome := by
  have e : epochs 4 = ends 459271258863231 := by
    show (epochs 3).bind ends = _
    rw [epochs_first.2.2]; rfl
  rw [e]
  simp only [ends, endv, show 459271258863231 % 4 = 3 by rfl, ite_true, Option.isSome_some]

end H116538
