import DMMap

/-!
# When DeepMind's map stops

`next` stops only at `C 2 0 (u + 2)`, and the only state that `next` sends there is `C 1 k 0`.  A state
`C (m + 3) k (b + 1)` always takes the last clause of `next`, `C (m + 3) k (b + 1) ↦ C m (k + 2) b`: the sweep that
trades three ones on the left and one on the right for two more `10` pairs.  So from `C (3 B + 1) k B` the sweep runs
`B` times to `C 1 (k + 2 B) 0`, and two more steps stop the map.  Together:

`halts_iff_visits`: the machine halts from blank tape if and only if the orbit of `next` from `start` visits a state
`C (3 B + 1) k B` (`B = 0` is the state `C 1 k 0` itself).
-/

set_option autoImplicit false

namespace H9516

open DM

/-- `j` steps of `next`. -/
def iter : Nat → Option State → Option State
  | 0, s => s
  | j + 1, s => iter j (Option.bind s next)

theorem iter_none (j : Nat) : iter j none = none := by
  induction j with
  | zero => rfl
  | succ j ih => exact ih

theorem orbit_add (n j : Nat) : orbit (n + j) = iter j (orbit n) := by
  induction j generalizing n with
  | zero => rfl
  | succ j ih =>
    rw [show n + (j + 1) = (n + 1) + j by omega, ih]
    rfl

theorem next_none_iff (s : State) : next s = none ↔ ∃ u, s = .C 2 0 (u + 2) := by
  rcases s with ⟨m, k, b⟩
  constructor
  · intro h
    rcases b with _ | _ | b <;> rcases m with _ | _ | _ | m <;> rcases k with _ | _ | k <;>
      simp [next] at h ⊢
  · rintro ⟨u, h⟩
    injection h with h1 h2 h3
    subst h1 h2 h3; rfl

theorem next_to_halting {s : State} {u : Nat} (h : next s = some (.C 2 0 (u + 2))) : ∃ k, s = .C 1 k 0 := by
  rcases s with ⟨m, k, b⟩
  rcases b with _ | _ | b <;> rcases m with _ | _ | _ | m <;> rcases k with _ | _ | k <;>
    simp [next] at h ⊢ <;> omega

theorem next_sweep (x k y : Nat) : next (.C (x + 3) k (y + 1)) = some (.C x (k + 2) y) := by
  rcases y with _ | y <;> rfl

/-- The sweep: `j` steps from `C (m + 3 j) k (b + j)` reach `C m (k + 2 j) b`. -/
theorem sweep (j m k b : Nat) : iter j (some (.C (m + 3 * j) k (b + j))) = some (.C m (k + 2 * j) b) := by
  induction j generalizing k with
  | zero => rfl
  | succ j ih =>
    show iter j (next (.C ((m + 3 * j) + 3) k ((b + j) + 1))) = _
    rw [show next (.C ((m + 3 * j) + 3) k ((b + j) + 1)) = some (.C (m + 3 * j) (k + 2) (b + j)) from next_sweep _ _ _, ih]
    rw [show k + 2 + 2 * j = k + 2 * (j + 1) by omega]

/-- From `C (3 B + 1) k B` the map stops after `B + 2` steps. -/
theorem stops_from (B k : Nat) : iter (B + 2) (some (.C (3 * B + 1) k B)) = none := by
  have h := sweep B 1 k 0
  rw [show 1 + 3 * B = 3 * B + 1 by omega, show 0 + B = B by omega] at h
  rw [show B + 2 = B + 1 + 1 by omega]
  have e : ∀ j (s : Option State), iter (j + 1) s = Option.bind (iter j s) next := by
    intro j; induction j with
    | zero => intro s; rfl
    | succ j ih => intro s; show iter (j + 1) (Option.bind s next) = _; rw [ih]; rfl
  rw [e, e, h]
  rfl

/-- **Halting criterion.**  The machine halts from blank tape if and only if the orbit of DeepMind's map visits a
state `C (3 B + 1) k B`. -/
theorem halts_iff_visits : HaltsFromBlank ↔ ∃ n B k, orbit n = some (.C (3 * B + 1) k B) := by
  rw [deepmind_halts_iff]
  constructor
  · rintro ⟨n, hn⟩
    have key : ∀ n, orbit n = none → ∃ n B k, orbit n = some (.C (3 * B + 1) k B) := by
      intro n
      induction n with
      | zero => intro h; cases h
      | succ n ih =>
        intro h
        cases hs : orbit n with
        | none => exact ih hs
        | some s =>
          have h1 : next s = none := by simpa [orbit, hs] using h
          obtain ⟨u, rfl⟩ := (next_none_iff s).mp h1
          cases n with
          | zero => cases hs
          | succ n =>
            cases hs' : orbit n with
            | none => simp [orbit, hs'] at hs
            | some s' =>
              have h2 : next s' = some (.C 2 0 (u + 2)) := by simpa [orbit, hs'] using hs
              obtain ⟨k, rfl⟩ := next_to_halting h2
              exact ⟨n, 0, k, hs'⟩
    exact key n (by simpa using hn)
  · rintro ⟨n, B, k, h⟩
    refine ⟨n + (B + 2), ?_⟩
    rw [orbit_add, h, stops_from]; rfl

end H9516
