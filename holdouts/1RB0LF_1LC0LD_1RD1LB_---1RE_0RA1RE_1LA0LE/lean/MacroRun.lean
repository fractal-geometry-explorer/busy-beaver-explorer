import Reduce

/-!
# 1RB0LF_1LC0LD_1RD1LB_---1RE_0RA1RE_1LA0LE: the macro machine run far, by compiled evaluation

`runN` is the macro machine with a step counter, tail-recursive; `runN_sound` (kernel) says what it computes is a
run of the machine.  `macro_runs` evaluates 20,000,000 macro steps with `native_decide`: no halt, and the machine is
then 191,906,825,348,151 steps in (`blank_runs_macro`).
-/

namespace H15252

open TM

def runN : Nat → Q → Nat → Option (Q × Nat)
  | 0, s, t => some (s, t)
  | n + 1, s, t =>
    match mstep s with
    | .go s' k => runN n s' (t + k)
    | _ => none

theorem runN_sound : ∀ (n : Nat) (s : Q) (t : Nat) (s' : Q) (t' : Nat),
    runN n s t = some (s', t') → ∃ k, t' = t + k ∧ steps k (cfg s) = some (cfg s')
  | 0, s, t, s', t', h => by
    simp only [runN, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨0, rfl, rfl⟩
  | n + 1, s, t, s', t', h => by
    simp only [runN] at h
    split at h
    · rename_i s1 k hm
      obtain ⟨j, hj, hs⟩ := runN_sound n s1 (t + k) s' t' h
      exact ⟨k + j, by omega, steps_seq trans (mstep_sound s hm) hs⟩
    · cases h

def runCheck (n T : Nat) : Bool :=
  match runN n s0 102 with
  | some (_, t) => decide (T ≤ t)
  | none => false

theorem macro_runs : runCheck 20000000 191906825348151 = true := by native_decide

theorem blank_runs_of_check {n T : Nat} (h : runCheck n T = true) : ∃ c, steps T init = some c := by
  unfold runCheck at h
  split at h
  · rename_i s t hr
    obtain ⟨k, hk, hs⟩ := runN_sound n s0 102 s t hr
    have h1 := steps_seq trans init_cfg hs
    have hT : T ≤ 102 + k := by simpa [hk] using h
    have e : 102 + k = T + (102 + k - T) := by omega
    rw [e] at h1
    exact steps_le trans h1
  · cases h

/-- No halt in the first 191,906,825,348,151 steps from blank tape. -/
theorem blank_runs_macro : ∃ c, steps 191906825348151 init = some c := blank_runs_of_check macro_runs

end H15252
