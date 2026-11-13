import Map

/-!
# 1RB0RB_1LC1RE_1LF0LD_1RA1LD_1RC1RB_---1LC: no halt in the first 10^3669 steps

Hand-written. The proved hole map (`Map.lean`) is followed from the first sample `S 2 2` (step 11) for 30,000
samples, adding up the proved step counts `cost`; the kernel evaluates the orbit (`decide +kernel`, numbers of up to
3,670 digits). Each sample is reached by a proved run, so the machine runs at least that many steps without halting.
-/

namespace H53489
open TM

/-- `n` more samples from `(p, r)` reached at step `t`: the sample and step reached, or `none` if the map halts. -/
def go : Nat → Nat × Nat × Nat → Option (Nat × Nat × Nat)
  | 0, x => some x
  | n + 1, (p, r, t) => match f p r with
    | some (p', r') => go n (p', r', t + cost p r)
    | none => none

theorem go_reach (n : Nat) : ∀ p r t p' r' t', 1 ≤ p → 1 ≤ r → steps t init = some (S p r) →
    go n (p, r, t) = some (p', r', t') → steps t' init = some (S p' r') := by
  induction n with
  | zero =>
    intro p r t p' r' t' _ _ ht h
    simp only [go, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ht
  | succ n ih =>
    intro p r t p' r' t' hp hr ht h
    simp only [go] at h
    have hs := sample_step p r hp hr
    split at h
    · rename_i p₁ r₁ hf
      rw [hf] at hs
      obtain ⟨hp₁, hr₁⟩ := f_dom p r p₁ r₁ hr hf
      exact ih p₁ r₁ _ p' r' t' hp₁ hr₁ (steps_seq trans ht hs) h
    · cases h

def check (n b : Nat) : Bool :=
  match go n (2, 2, 11) with
  | some (_, _, t) => decide (b ≤ t)
  | none => false

theorem no_halt_of_check (n b : Nat) (h : check n b = true) : ∃ c, steps b init = some c := by
  unfold check at h
  split at h
  · rename_i p r t hg
    have ht := go_reach n 2 2 11 p r t (by omega) (by omega) start_S hg
    have hb : b ≤ t := by simpa using h
    have e : t = b + (t - b) := by omega
    rw [e] at ht
    exact steps_le trans ht
  · cases h

theorem check_30000 : check 30000 (10 ^ 3669) = true := by decide +kernel

/-- **No halt in the first 10^3669 steps** from blank tape (Lean's kernel, through the proved map). -/
theorem no_halt_10_3669 : ∃ c, steps (10 ^ 3669) init = some c := no_halt_of_check _ _ check_30000

end H53489
