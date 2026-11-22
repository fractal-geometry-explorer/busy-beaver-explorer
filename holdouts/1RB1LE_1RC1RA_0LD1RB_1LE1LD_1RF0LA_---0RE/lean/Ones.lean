import Fatal

/-!
# A halt needs an all-ones tape of a fatal length

The run from blank tape halts **if and only if** its phase orbit reaches an all-ones tape `PR 0 n` whose length `n`
is fatal (`Fatal n`, the explicit sparse list of `Fatal.lean`).  This combines, for every length and every phase,
`ones_safe_all` (from a non-fatal all-ones tape the run cannot halt before the tape is all ones again) and
`ones_fate` (a fatal all-ones tape halts), by strong induction on the number of phases: the last all-ones tape
before a halt is fatal (`fatal_before`).  `halt_needs_ones` is the iff on the phase orbit, `halt_passes_ones` the
same as a statement about the machine's own steps.

So the halting problem of ``1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_---0RE`` is exactly: does the orbit of the doubling map ever produce an all-ones
tape whose length is in the fatal list?
-/

namespace H137865

open TM

/-- Before any halting phase reached from an all-ones tape there is an all-ones tape (possibly the first one) of
fatal length. -/
theorem fatal_before (k : Nat) : ∀ n x z, z ≤ 1 → iter k (.r 0 n) = some (.e x z) →
    ∃ i m, i ≤ k ∧ Fatal m ∧ iter i (.r 0 n) = some (.r 0 m) := by
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro n x z hz hk
    by_cases hf : Fatal n
    · exact ⟨0, n, Nat.zero_le _, hf, rfl⟩
    · obtain ⟨i, hi0, hik, m, hm⟩ := ones_safe_all n hf k x z hz hk
      obtain ⟨d, rfl⟩ : ∃ d, k = i + d := ⟨k - i, by omega⟩
      rw [iter_add, hm, Option.bind_some] at hk
      obtain ⟨j, m', hj, hf', hj'⟩ := ih d (by omega) m x z hz hk
      exact ⟨i + j, m', by omega, hf', by rw [iter_add, hm, Option.bind_some]; exact hj'⟩

/-- **The machine halts from blank tape if and only if the phase orbit of `.r 0 2` reaches an all-ones tape of
fatal length.** -/
theorem halt_needs_ones : HaltsFromBlank ↔ ∃ i n, Fatal n ∧ iter i (.r 0 2) = some (.r 0 n) := by
  rw [halts_iff]
  constructor
  · rintro ⟨k, x, z, hz, hk⟩
    obtain ⟨i, m, -, hf, hi⟩ := fatal_before k _ x z hz hk
    exact ⟨i, m, hf, hi⟩
  · rintro ⟨i, n, hf, hi⟩
    obtain ⟨f, hfate⟩ := ones_fate n
    rcases hfate with ⟨h, -⟩ | ⟨-, h⟩
    · obtain ⟨k, x, z, hz, hk⟩ := fate_true _ _ h
      exact ⟨i + k, x, z, hz, by rw [iter_add, hi, Option.bind_some]; exact hk⟩
    · exact absurd hf h

/-- **If the machine halts from blank tape, its run passes through an all-ones tape `PR 0 n` with `n` fatal.** -/
theorem halt_passes_ones (h : HaltsFromBlank) : ∃ t n, Fatal n ∧ steps t init = some (Ph.r 0 n).cfg := by
  obtain ⟨i, n, hf, hi⟩ := halt_needs_ones.mp h
  obtain ⟨s, -, hs⟩ := reach_iter i _ _ hi
  exact ⟨2 + s, n, hf, steps_seq trans init_r hs⟩

end H137865
