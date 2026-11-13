import Blank
import Rules

/-!
# The even rounds in closed form, and the first rounds from blank tape

A *round start* is `0^∞ B> 0 0 1^n 0^∞` (`E n`): the head in state B at the left end, then one block of `n` ones.
For even `n ≥ 4` the round is a sweep (`entry`, `pass`, `end1`/`end0` in Rules.lean): the machine reaches
`E (5n/2 + 1)` (`even_round`, for every even `n ≥ 4`, by induction on the number of sweeps).  From blank tape the
machine reaches `E 2`, `E 6`, `E 16`, `E 41`, then two blocks `36, 7`, then `E 106`, and by six even rounds `E 26041`
(`reaches_26041`), about 1.6·10⁸ steps in.  Odd rounds are not in closed form here (see the README).
Checked by Lean's kernel.
-/

namespace H135376

open TM

/-- `c` reaches `c'` in some number of steps. -/
def Run (c c' : Config) : Prop := ∃ n, steps n c = some c'

theorem Run.trans {a b c : Config} (h₁ : Run a b) (h₂ : Run b c) : Run a c := by
  obtain ⟨n, hn⟩ := h₁
  obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, steps_seq H135376.trans hn hm⟩

theorem run_of_eq {n : Nat} {c c' d : Config} (h : steps n c = some c') (e : c' = d) : Run c d := ⟨n, e ▸ h⟩

abbrev w5 : List Bool := [true, false, true, false, true]

/-- The round start `0^∞ B> 0 0 1^n 0^∞`. -/
def E (n : Nat) : Config := ⟨blank, cons false (cons false (rep n [true] blank)), .B⟩

/-- Inside an even round: `0^∞ (10101)^j 0 (01)^k 0 A> 0^∞`. -/
def W (j k : Nat) : Config := ⟨cons false (rep k [true, false] (cons false (rep j w5 blank))), blank, .A⟩

theorem rep_one_two (p : Nat) (s : Tape) : rep (2 * p) [true] s = rep p [true, true] s := by
  induction p with
  | zero => rfl
  | succ p ih => rw [show 2 * (p + 1) = 2 * p + 1 + 1 by omega, rep_succ, rep_succ, ih]; rfl

theorem ones_comm (n : Nat) (s : Tape) : cons true (rep n [true] s) = rep n [true] (cons true s) :=
  rep_rotate n [true] [true] [true] rfl s

theorem rep_one_five (j : Nat) (s : Tape) : rep j [true, true, true, true, true] s = rep (5 * j) [true] s := by
  induction j generalizing s with
  | zero => rfl
  | succ j ih =>
    rw [← rep_app_comm, ih, show 5 * (j + 1) = 5 * j + 5 by omega, rep_add]
    rfl

theorem passes (i : Nat) : ∀ j k, Run (W j (k + 1 + i)) (W (j + i) (k + 1)) := by
  induction i with
  | zero => intro j k; exact ⟨0, rfl⟩
  | succ i ih =>
    intro j k
    have h1 : Run (W j (k + i + 2)) (W (j + 1) (k + i + 1)) :=
      run_of_eq (pass j (k + i)) (by simp only [W, rep_succ, app_cons, app_nil])
    have h2 := ih (j + 1) k
    rw [show k + 1 + (i + 1) = k + i + 2 by omega, show j + (i + 1) = j + 1 + i by omega]
    rw [show k + 1 + i = k + i + 1 by omega] at h2
    exact h1.trans h2

/-- **The even rounds**: from `E (2p + 4)` the machine reaches `E (5p + 11)`, for every `p`. -/
theorem start (p : Nat) : Run (E (2 * p + 4)) (W 1 p) := by
  have h := entry p
  have e : E (2 * p + 4) = ⟨blank, cons false (cons false (rep (p + 2) [true, true] blank)), .B⟩ := by
    simp only [E]; rw [show 2 * p + 4 = 2 * (p + 2) by omega, rep_one_two]
  rw [e]
  exact run_of_eq h (by simp only [W, rep_succ, rep_zero, app_cons, app_nil])

theorem finish (j : Nat) : Run (W j 1) (E (5 * j + 11)) := by
  refine run_of_eq (end1 j) ?_
  simp only [E, rep_one_five, ones_comm]
  rw [rep_add]
  simp only [rep_succ, rep_zero, app_cons, app_nil]

theorem finish0 (j : Nat) : Run (W j 0) (E (5 * j + 6)) := by
  refine run_of_eq (end0 j) ?_
  simp only [E, rep_one_five, ones_comm]
  rw [rep_add]
  simp only [rep_succ, rep_zero, app_cons, app_nil]

/-- **The even rounds**: from `E (2p + 4)` the machine reaches `E (5p + 11)`, for every `p`. -/
theorem even_round (p : Nat) : Run (E (2 * p + 4)) (E (5 * p + 11)) := by
  cases p with
  | zero => exact (start 0).trans (finish0 1)
  | succ i =>
    have h2 := passes i 1 0
    rw [show 0 + 1 + i = i + 1 by omega] at h2
    have h3 := finish (i + 1)
    exact (start (i + 1)).trans (h2.trans h3)

theorem even_round' (n m : Nat) (p : Nat) (hn : n = 2 * p + 4) (hm : m = 5 * p + 11) : Run (E n) (E m) := by
  subst hn hm; exact even_round p

/-- From blank tape the machine reaches `E 26041`: rounds 2 → 6 → 16 → 41 → (36, 7) → 106 → 266 → 666 → 1666 → 4166
→ 10416 → 26041 (161,622,801 steps by simulation). -/
theorem reaches_26041 : Run init (E 26041) := by
  refine (run_of_eq blank_start rfl).trans ?_
  refine (run_of_eq round2 rfl).trans ?_
  refine (even_round' 6 16 1 rfl rfl).trans ?_
  refine (even_round' 16 41 6 rfl rfl).trans ?_
  refine (run_of_eq round41 rfl).trans ?_
  refine (run_of_eq round36_7 rfl).trans ?_
  refine (even_round' 106 266 51 rfl rfl).trans ?_
  refine (even_round' 266 666 131 rfl rfl).trans ?_
  refine (even_round' 666 1666 331 rfl rfl).trans ?_
  refine (even_round' 1666 4166 831 rfl rfl).trans ?_
  refine (even_round' 4166 10416 2081 rfl rfl).trans ?_
  exact even_round' 10416 26041 5206 rfl rfl

end H135376
