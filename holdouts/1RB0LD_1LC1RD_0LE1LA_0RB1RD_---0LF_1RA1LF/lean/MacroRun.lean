import Reduce

/-!
# 1RB0LD_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF: the macro machine run far, by compiled evaluation

`runN` is the macro machine with a step counter, tail-recursive so compiled code runs it in constant stack;
`runN_sound` (kernel) says what it computes is a run of the machine.  `macro_runs` evaluates 20,000,000 macro steps
(9,122,017 sweeps) with `native_decide`: no halt, and the machine is then 221,196,908,934,683 steps in
(`blank_runs_macro`).
-/

namespace H141594

open TM

/-- n macro steps from `gap b ls rs` at machine step t: the gap reached and its machine step, or `none` if the
macro machine halts or gets stuck. -/
def runN : Nat → Nat → List Nat → List Nat → Nat → Option (Nat × List Nat × List Nat × Nat)
  | 0, b, ls, rs, t => some (b, ls, rs, t)
  | n + 1, b, ls, rs, t =>
    match mstep b ls rs with
    | .gap b' ls' rs' => runN n b' ls' rs' (t + mcost b rs)
    | _ => none

theorem runN_sound : ∀ (n b : Nat) (ls rs : List Nat) (t b' : Nat) (ls' rs' : List Nat) (t' : Nat),
    runN n b ls rs t = some (b', ls', rs', t') → ∃ k, t' = t + k ∧ steps k (gap b ls rs) = some (gap b' ls' rs')
  | 0, b, ls, rs, t, b', ls', rs', t', h => by
    simp only [runN, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact ⟨0, rfl, rfl⟩
  | n + 1, b, ls, rs, t, b', ls', rs', t', h => by
    simp only [runN] at h
    split at h
    · rename_i b1 ls1 rs1 hm
      obtain ⟨k, hk, hs⟩ := runN_sound n b1 ls1 rs1 _ b' ls' rs' t' h
      exact ⟨mcost b rs + k, by omega, steps_seq trans (mstep_sound hm) hs⟩
    · cases h

/-- The check: 20,000,000 macro steps from the first gap, reaching at least machine step 221,196,908,934,683. -/
def runCheck (n T : Nat) : Bool :=
  match runN n 3 [] [] 7 with
  | some (_, _, _, t) => decide (T ≤ t)
  | none => false

theorem macro_runs : runCheck 20000000 221196908934683 = true := by native_decide

theorem blank_runs_of_check {n T : Nat} (h : runCheck n T = true) : ∃ c, steps T init = some c := by
  unfold runCheck at h
  split at h
  · rename_i b ls rs t hr
    obtain ⟨k, hk, hs⟩ := runN_sound n 3 [] [] 7 b ls rs t hr
    have h1 := steps_seq trans init_gap hs
    have hT : T ≤ 7 + k := by simpa [hk] using h
    have e : 7 + k = T + (7 + k - T) := by omega
    rw [e] at h1
    exact steps_le trans h1
  · cases h

/-- No halt in the first 221,196,908,934,683 steps from blank tape. -/
theorem blank_runs_macro : ∃ c, steps 221196908934683 init = some c := blank_runs_of_check macro_runs

end H141594
