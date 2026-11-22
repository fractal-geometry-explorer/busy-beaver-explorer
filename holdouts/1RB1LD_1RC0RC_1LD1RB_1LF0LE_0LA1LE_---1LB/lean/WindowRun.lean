import ZoneCascade
import Window

/-!
# 1RB1LD_1RC0RC_1LD1RB_1LF0LE_0LA1LE_---1LB: no halt in the first 1.5e+39 steps, by windows of the cascade

`Window.lean` (machine-independent): the first `m` cells of the word, fed the block's three letters, are run once
per cell, twice when the cell's bit is not back (`wfold`); what leaves them covers `3 · 2^d` sweeps, `d` the number
of cells that needed two passes, and is then run through the rest of the word (`window_of_check`).

* `window_runs` (compiled evaluation): at zone step 3 · 10^7, cut after 135 cells, the window has `d = 63` and
  nothing leaves the word: no halt and no reset for `3 · 2^63` more sweeps;
* `corb_quiet_t`: while nothing leaves the word, every sweep takes at least `4 n` steps;
* `blank_runs_window`: **no halt in the first 1500000000000000000000000000000000000000 steps from blank tape**.
-/

namespace H117020

open TM hiding run
open XS

/-- What compiled evaluation checks at zone step 3 · 10^7. -/
def wgood : Option (Nat × Nat × List Bool × List Bool) → Bool
  | some (_, n, Z, []) => windowCheck n 135 63 Z && decide (29000000 ≤ n)
  | _ => false

theorem window_runs : wgood (H117020.crun 30000000 (3, 0, [false], [])) = true := by native_decide

theorem corb_quiet_t {j t n : Nat} {Z : List Bool} (hj : corb j = some (t, n, Z, [])) :
    ∀ k, (run Z (evs n k)).2 = [] →
      ∃ t', corb (j + k) = some (t', n + k, (run Z (evs n k)).1, []) ∧ t + 4 * (n * k) + 2 * (k * k) ≤ t' + 2 * k
  | 0, _ => ⟨t, by simpa [evs, run] using hj, by omega⟩
  | k + 1, h => by
    rw [evs_add, run_append] at h
    have h1 := (List.append_eq_nil_iff.mp h).1
    have h2 := (List.append_eq_nil_iff.mp h).2
    obtain ⟨t', ht', hle⟩ := corb_quiet_t hj k h1
    have e1 : evs (n + k) 1 = [.P (pat (n + k))] := rfl
    rw [e1] at h2
    have hn := feed_none_of_run _ _ h2
    obtain ⟨d, hd⟩ := swr_feed_ok (pat (n + k)) _ hn
    refine ⟨t' + (4 * (n + k + d) + 12), ?_, ?_⟩
    · rw [show j + (k + 1) = (j + k) + 1 by omega]
      show (match corb (j + k) with
        | none => none
        | some (t, n, Z, r) => _) = _
      rw [ht']
      simp only [cstep, hd, evs_add, run_append, e1, run_one, show n + (k + 1) = n + k + 1 by omega]
    · have a1 : n * (k + 1) = n * k + n := Nat.mul_succ n k
      have a2 : (k + 1) * (k + 1) = k * k + 2 * k + 1 := by
        rw [Nat.succ_mul, Nat.mul_succ]; omega
      rw [a1, a2]; omega

/-- **No halt in the first 1500000000000000000000000000000000000000 steps from blank tape.** -/
theorem blank_runs_window : ∃ c, steps 1500000000000000000000000000000000000000 init = some c := by
  have hz := window_runs
  rw [← corb_eq_crun] at hz
  cases hc : corb 30000000 with
  | none => rw [hc] at hz; simp [wgood] at hz
  | some p =>
    obtain ⟨t, n, Z, r⟩ := p
    cases r with
    | cons _ _ => rw [hc] at hz; simp [wgood] at hz
    | nil =>
      rw [hc] at hz
      simp only [wgood, Bool.and_eq_true, decide_eq_true_eq] at hz
      obtain ⟨hw, -⟩ := hz
      have hq := window_of_check hw (3 * 2 ^ 63) (Nat.le_refl _)
      obtain ⟨t', ht', hle⟩ := corb_quiet_t hc _ hq
      have hs := (corb_sound _ _ _ _ _ ht').1
      have hbig : 1500000000000000000000000000000000000000 ≤ t' := by
        have e1 : 3 * 2 ^ 63 = 27670116110564327424 := rfl
        have e2 : 27670116110564327424 * 27670116110564327424 = 765635325572111542792592866721478475776 := rfl
        rw [e1, e2] at hle
        omega
      rw [show t' = 1500000000000000000000000000000000000000 + (t' - 1500000000000000000000000000000000000000) by omega] at hs
      exact steps_le trans hs

end H117020
