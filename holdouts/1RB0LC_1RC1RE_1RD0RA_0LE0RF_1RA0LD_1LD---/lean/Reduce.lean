import RunLong

/-!
# Halting needs a sweep the proved rules do not cover

`nextR` covers every sweep of the counter except the start of a nested run (a carry through every digit into a
leftmost block whose length is not 3 or `6j+9`) and the other phase of the right end with a last digit other than 1.
Every sweep takes at least one step (`nextR_pos`), so if the run of `nextR` from the end of the first nested run never
stops, the machine runs forever.  Hence (`halts_imp_uncovered`): **if the machine halts from blank tape, the counter,
run sweep by sweep from step 231,327,122, reaches a sweep that the proved rules do not cover** (in practice a carry
into an even leftmost block, the start of a nested run).  The C program `c/dsim.c` runs the same sweep program for
2,121,320,341 sweeps (to step 1.8·10¹⁹) without meeting such a sweep.

Everything here is checked by Lean's kernel (it uses `reach_B` of `RunLong.lean`, which rests on `native_decide`).
-/

namespace H115779

open TM

theorem nextR_pos (s s' : MR) (n : Nat) (h : nextR s = some (s', n)) : 1 ≤ n := by
  unfold nextR at h
  split at h
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
    · cases h
  · simp only at h
    split at h
    · split at h
      · split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
        · cases h
      · split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
        · cases h
    · split at h
      · split at h
        · split at h
          · split at h
            · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
            · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
          · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
        · split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
          · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
      · cases h

theorem runR_le : ∀ (k : Nat) (s : MR) (t : Nat) (s' : MR) (t' : Nat), runR k s t = some (s', t') → t + k ≤ t'
  | 0, s, t, s', t', h => by simp [runR] at h; omega
  | k + 1, s, t, s', t', h => by
    simp only [runR] at h
    split at h
    · cases h
    · rename_i s1 n hn
      have := runR_le k s1 (t + n) s' t' h
      have := nextR_pos s s1 n hn
      omega

/-- If the sweep program never meets an uncovered sweep, the machine runs forever. -/
theorem not_halts_of_runR {s : MR} {t : Nat} (h0 : steps t init = some s.cfg)
    (h : ∀ k, runR k s t ≠ none) : ¬ HaltsFromBlank := by
  apply not_halts_of_forall
  intro n
  cases e : runR n s t with
  | none => exact absurd e (h n)
  | some x =>
    obtain ⟨s', t'⟩ := x
    have h1 := runR_sound n s t s' t' e h0
    have h2 := runR_le n s t s' t' e
    rw [show t' = n + (t' - n) by omega] at h1
    exact steps_le trans h1

/-- **Reduction**: a halt from blank tape needs the counter, from the end of the first nested run, to reach a sweep
that the proved rules do not cover. -/
theorem halts_imp_uncovered (hH : HaltsFromBlank) : ∃ k, runR k sB 231327122 = none := by
  apply Classical.byContradiction
  intro hn
  exact not_halts_of_runR reach_B (fun k hk => hn ⟨k, hk⟩) hH

end H115779
