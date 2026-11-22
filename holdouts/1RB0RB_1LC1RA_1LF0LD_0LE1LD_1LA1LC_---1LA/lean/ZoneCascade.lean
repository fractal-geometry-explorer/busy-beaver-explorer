import Zone
import Cascade

/-!
# 1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA: the zone orbit as a cascade, and its period

`Cascade.lean` (machine-independent) shows that a sweep of the zone orbit at the right end is one event fed to a
row of one-bit cells, and that a row of `m` cells fed the block's letters is back after `3 · 2^m` sweeps.  Here:

* `corb_quiet`: while no event leaves the word, the zone orbit (`Zone.lean`) is the cascade, sweep for sweep;
* `never_halts_of_quiet`: if, from some state `(n, Z)` of the zone orbit at the right end, nothing leaves the word
  in `3 · 2^|Z|` sweeps, the machine never halts.  Halting is thus decided by one period of the word: either a
  sweep gets through the whole word (a halt or a reset) within `3 · 2^|Z|` sweeps, or none ever does.
-/

namespace H50378

open TM hiding run
open XS

theorem cstep_feed (n : Nat) (Z : List Bool) (h : (feed Z (.P (pat n))).2 = none) :
    ∃ k, cstep n Z [] = some (k, n + 1, (feed Z (.P (pat n))).1, []) := by
  obtain ⟨d, hd⟩ := swr_feed_ok (pat n) Z h
  exact ⟨4 * (n + d) + 12, by simp only [cstep, hd]⟩

theorem run_one (Z : List Bool) (e : Ev) : run Z [e] = ((feed Z e).1, (feed Z e).2.toList) := by
  simp [run]

theorem feed_none_of_run (Z : List Bool) (e : Ev) (h : (run Z [e]).2 = []) : (feed Z e).2 = none := by
  rw [run_one] at h
  cases hf : (feed Z e).2 with
  | none => rfl
  | some _ => rw [hf] at h; cases h

/-- While nothing leaves the word, the zone orbit is the cascade. -/
theorem corb_quiet {j t n : Nat} {Z : List Bool} (hj : corb j = some (t, n, Z, [])) :
    ∀ k, (run Z (evs n k)).2 = [] → ∃ t', corb (j + k) = some (t', n + k, (run Z (evs n k)).1, [])
  | 0, _ => ⟨t, by simpa [evs, run] using hj⟩
  | k + 1, h => by
    rw [evs_add, run_append] at h
    have h1 := (List.append_eq_nil_iff.mp h).1
    have h2 := (List.append_eq_nil_iff.mp h).2
    obtain ⟨t', ht'⟩ := corb_quiet hj k h1
    have e1 : evs (n + k) 1 = [.P (pat (n + k))] := rfl
    rw [e1] at h2
    have hn := feed_none_of_run _ _ h2
    obtain ⟨k', hk'⟩ := cstep_feed (n + k) _ hn
    refine ⟨t' + k', ?_⟩
    rw [show j + (k + 1) = (j + k) + 1 by omega]
    show (match corb (j + k) with
      | none => none
      | some (t, n, Z, r) => _) = _
    rw [ht']
    simp only [hk', evs_add, run_append, e1, run_one, show n + (k + 1) = n + k + 1 by omega]

/-- **One period decides.** If the zone orbit reaches a state `(n, Z)` at the right end and nothing leaves the
word during the next `3 · 2^|Z|` sweeps, the machine never halts. -/
theorem never_halts_of_quiet {j t n : Nat} {Z : List Bool} (hj : corb j = some (t, n, Z, []))
    (hq : (run Z (evs n (3 * 2 ^ Z.length))).2 = []) : ¬ HaltsFromBlank := by
  rw [halts_iff_zone]
  rintro ⟨k, t0, n0, Z0, r0, h1, h2⟩
  by_cases hk : k < j
  · have hn : corb (k + 1) = none := by
      show (match corb k with
        | none => none
        | some (t, n, Z, r) => _) = none
      rw [h1]; simp only [h2]
    have := corb_none (k + 1) (j - (k + 1)) hn
    rw [show k + 1 + (j - (k + 1)) = j by omega, hj] at this; cases this
  · obtain ⟨t', ht'⟩ := corb_quiet hj (k - j) (never_of_quiet n Z hq (k - j))
    rw [show j + (k - j) = k by omega, h1] at ht'
    simp only [Option.some.injEq, Prod.mk.injEq] at ht'
    obtain ⟨-, rfl, rfl, rfl⟩ := ht'
    have hn := never_of_quiet n Z hq (k - j + 1)
    rw [evs_add, run_append] at hn
    have hf := feed_none_of_run _ _ (List.append_eq_nil_iff.mp hn).2
    obtain ⟨k', hk'⟩ := cstep_feed _ _ hf
    rw [hk'] at h2; cases h2

end H50378
