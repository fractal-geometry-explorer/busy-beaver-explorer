import Chain

/-!
# The first rounds of the orbit, checked exactly

`halts_iff` (MapThm) reduces halting from blank tape to the orbit of `(7, 1, 0)` under `mstep`, and
`halts_iff_chain` (Chain) says a halt can only come at the end of a doubling chain that uses up its pairs exactly.
The chance-of-a-hit heuristic (`py/heuristic.py`) puts almost all of the chance of such a hit in the first rounds.
This file follows the orbit exactly through those rounds.

* `jstep`: one step of the map, except that a whole B phase (m even, x >= 1: x steps of rule B) is one jump.
  `jstep_ok`: a jump of `d` map steps is `iter d`; the B phase by induction on x (`bphase`).
* `jrun n p c r`: `n` jumps from `p`, counting map steps in `c` and R steps (rounds) in `r`.
  `jrun_ok`: what it returns is `iter` of the counted number of map steps.
* `orbit_round20`, `orbit_round200`: after `T` map steps the orbit is still defined (no H), and those steps
  contain 20 (200) R steps, by kernel evaluation (`decide +kernel`) of `jrun`.
* `no_halt_round200`: the machine runs at least `T200 > 10^35` steps from blank tape without halting.

Written by hand; the numbers come from `py/rounds.py`.
-/

namespace H26350

open TM

/-- One jump: a whole B phase at once, otherwise one step of the map; with the number of map steps it makes. -/
def jstep (x m : Nat) (s : Bool) : Option (Nat × (Nat × Nat × Bool)) :=
  if m % 2 = 0 ∧ 1 ≤ x then some (x, (0, m + 4 * x, if x % 2 = 0 then s else !s))
  else match mstep x m s with
    | none => none
    | some q => some (1, q)

/-- `n` jumps from `p`, adding the map steps to `c` and the R steps (m even, x = 0) to `r`. -/
def jrun : Nat → Nat × Nat × Bool → Nat → Nat → Option (Nat × Nat × (Nat × Nat × Bool))
  | 0, p, c, r => some (c, r, p)
  | n + 1, (x, m, s), c, r =>
    match jstep x m s with
    | none => none
    | some (d, q) => jrun n q (c + d) (if m % 2 = 0 ∧ x = 0 then r + 1 else r)

theorem iter_add (a : Nat) : ∀ b p, iter (a + b) p = (iter a p).bind (iter b) := by
  induction a with
  | zero => intro b p; rw [Nat.zero_add]; rfl
  | succ a ih =>
    intro b ⟨x, m, s⟩
    rw [show a + 1 + b = (a + b) + 1 by omega]
    show (match mstep x m s with | none => none | some q => iter (a + b) q) =
      (match mstep x m s with | none => none | some q => iter a q).bind (iter b)
    cases mstep x m s with
    | none => rfl
    | some q => exact ih b q

/-- A B phase: from `(x, 2n, s)`, x steps of rule B to `(0, 2n + 4x, s xor (x odd))`. -/
theorem bphase (x : Nat) : ∀ n s, iter x (x, 2 * n, s) =
    some (0, 2 * n + 4 * x, if x % 2 = 0 then s else !s) := by
  induction x with
  | zero => intro n s; rfl
  | succ x ih =>
    intro n s
    have h1 : mstep (x + 1) (2 * n) s = some (x, 2 * (n + 2), !s) := by
      unfold mstep
      rw [if_pos (by omega), if_pos (by omega)]
      simp only [Nat.add_sub_cancel, Option.some.injEq, Prod.mk.injEq, true_and, and_true]
      omega
    show (match mstep (x + 1) (2 * n) s with | none => none | some q => iter x q) = _
    rw [h1]
    show iter x (x, 2 * (n + 2), !s) = _
    rw [ih (n + 2) (!s)]
    simp only [Option.some.injEq, Prod.mk.injEq, true_and]
    refine ⟨by omega, ?_⟩
    rcases Nat.mod_two_eq_zero_or_one x with h | h
    · rw [if_pos h, if_neg (by omega)]
    · rw [if_neg (by omega), if_pos (by omega)]; cases s <;> rfl

theorem jstep_ok (x m : Nat) (s : Bool) : ∀ d q, jstep x m s = some (d, q) → iter d (x, m, s) = some q := by
  intro d q h
  unfold jstep at h
  by_cases hb : m % 2 = 0 ∧ 1 ≤ x
  · rw [if_pos hb] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨n, rfl⟩ : ∃ n, m = 2 * n := ⟨m / 2, by omega⟩
    exact bphase x n s
  · rw [if_neg hb] at h
    cases e : mstep x m s with
    | none => rw [e] at h; simp at h
    | some q' =>
      rw [e] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      show (match mstep x m s with | none => none | some q => iter 0 q) = _
      rw [e]; rfl

theorem jrun_ok (n : Nat) : ∀ p c r c' r' q, jrun n p c r = some (c', r', q) →
    c ≤ c' ∧ iter (c' - c) p = some q := by
  induction n with
  | zero =>
    intro p c r c' r' q h
    simp only [jrun, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -, rfl⟩ := h
    exact ⟨Nat.le_refl _, by rw [Nat.sub_self]; rfl⟩
  | succ n ih =>
    intro ⟨x, m, s⟩ c r c' r' q h
    simp only [jrun] at h
    cases e : jstep x m s with
    | none => rw [e] at h; simp at h
    | some dq =>
      obtain ⟨d, q1⟩ := dq
      rw [e] at h
      obtain ⟨hc, hi⟩ := ih q1 (c + d) _ c' r' q h
      refine ⟨by omega, ?_⟩
      rw [show c' - c = d + (c' - (c + d)) by omega, iter_add, jstep_ok x m s d q1 e]
      exact hi

/-- If `jrun` from the start point returns, the orbit is defined after the counted number of map steps. -/
theorem orbit_of_jrun {n T r : Nat} {q : Nat × Nat × Bool} (h : jrun n (7, 1, false) 0 0 = some (T, r, q)) :
    orbit T = some q := by
  obtain ⟨-, hi⟩ := jrun_ok n _ 0 0 T r q h
  rw [Nat.sub_zero] at hi
  rw [← Nat.zero_add T, orbit_add T 0 (7, 1, false) rfl]
  exact hi

/-- A defined orbit point means the machine has not halted: it runs at least `t` steps from blank tape. -/
theorem runs_of_orbit {t : Nat} {q : Nat × Nat × Bool} (h : orbit t = some q) : ∃ c, steps t init = some c := by
  obtain ⟨x, m, s⟩ := q
  obtain ⟨N, hN, hr⟩ := orbit_reach t x m s h
  exact TM.steps_le trans (show TM.steps trans (t + (N - t)) init = _ by rw [show t + (N - t) = N by omega]; exact hr)

/-! ## The first 20 rounds -/

/-- 271 jumps from `(7, 1, 0)`: 109,233 map steps with 20 R steps, ending at `(109379, 3, 0)`. -/
theorem jrun_round20 : jrun 271 (7, 1, false) 0 0 = some (109233, 20, (109379, 3, false)) := by decide +kernel

theorem orbit_round20 : orbit 109233 = some (109379, 3, false) := orbit_of_jrun jrun_round20

/-! ## The first 200 rounds -/

/-- 12,815 jumps: T200 map steps with 200 R steps. -/
theorem jrun_round200 : jrun 12815 (7, 1, false) 0 0 =
    some (91065045402056075917728632641862099, 200, (91065045402056075917728632641863651, 3, false)) := by
  decide +kernel

theorem orbit_round200 :
    orbit 91065045402056075917728632641862099 = some (91065045402056075917728632641863651, 3, false) :=
  orbit_of_jrun jrun_round200

/-- The machine runs more than 9 * 10^34 steps from blank tape without halting (it is past round 200). -/
theorem no_halt_round200 : ∃ c, steps 91065045402056075917728632641862099 init = some c :=
  runs_of_orbit orbit_round200

end H26350
