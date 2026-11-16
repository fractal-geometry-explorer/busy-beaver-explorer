import Map

/-!
# 1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_---1LC halts iff a doubling map with a growing modulus hits 2u = m at a reset

`Map.lean` proves that the machine halts iff the orbit of the visit `(0, 1, 1)` under the visit map `F` reaches
`none`.  This file proves, by arithmetic alone, that `F` is the doubling map `op` of `py/model.py`:

    2u < m           (c, u, m) ↦ (c, 2u, m + 1)                          a visit
    2u > m, c ≥ 1    (c, u, m) ↦ (c − 1, 2u − m, m + 1)                  carry
    2u = m, c ≥ 1    (c, u, m) ↦ (c − 1, 1, m + 2)                       carry that empties the fast wheel
    2u > m, c = 0    (c, u, m) ↦ (2(m − u − 1), 2u − m, 2u − m + 3)      reset
    2u = m, c = 0    halt

read on the visit `S(c, 2p+2, b)` as `(c, u, m) = (c, b + 1, p + b + 3)` (`phi`), and inside a sweep `Rc c p k z` as
`(c, k + z + 2, p + 2k + z + 4)` (`psi`): a round does not move `psi`, a carry or a reset is one operation, and the
end of a sweep is the doubling.

Main result, `halts_iff_op`: **the machine halts from blank tape iff the doubling map, started at
`(c, u, m) = (0, 2, 5)`, reaches the halt**, that is, a reset with 2u = m.  Nothing else about the run is assumed.
-/

namespace H50923

/-- One operation of the doubling map; `none` is the halt. -/
def op : Nat × Nat × Nat → Option (Nat × Nat × Nat)
  | (c, u, m) =>
    if 2 * u < m then some (c, 2 * u, m + 1)
    else match c with
      | c + 1 => if 2 * u = m then some (c, 1, m + 2) else some (c, 2 * u - m, m + 1)
      | 0 => if 2 * u = m then none else some (2 * (m - u - 1), 2 * u - m, 2 * u - m + 3)

/-- `n` operations. -/
def opIter : Nat → Nat × Nat × Nat → Option (Nat × Nat × Nat)
  | 0, s => some s
  | n + 1, s => (op s).bind (opIter n)

theorem opIter_add (a b : Nat) (s : Nat × Nat × Nat) : opIter (a + b) s = (opIter a s).bind (opIter b) := by
  induction a generalizing s with
  | zero => simp [opIter]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [opIter]
    cases op s with
    | none => rfl
    | some s' => exact ih s'

theorem opIter_one (s : Nat × Nat × Nat) : opIter 1 s = op s := by
  simp only [opIter]; cases op s <;> rfl

/-- The doubling-map state of the visit `S c p b`. -/
def phi (v : Nat × Nat × Nat) : Nat × Nat × Nat := (v.1, v.2.2 + 1, v.2.1 + v.2.2 + 3)

/-- The doubling-map state of `Rc c p k z` (the visit it will be once the current doubling is done). -/
def psi (c p k z : Nat) : Nat × Nat × Nat := (c, k + z + 2, p + 2 * k + z + 4)

/-- What `inner`/`F` say in terms of `op`. -/
def OpSem (s : Nat × Nat × Nat) : Option (Nat × Nat × Nat) → Prop
  | some v => ∃ n, opIter (n + 1) s = some (phi v)
  | none => ∃ n, opIter n s = none

theorem opsem_one {s t : Nat × Nat × Nat} {o : Option (Nat × Nat × Nat)} (h : op s = some t) (ht : OpSem t o) :
    OpSem s o := by
  cases o with
  | none =>
    obtain ⟨n, hn⟩ := ht
    exact ⟨1 + n, by rw [opIter_add, opIter_one, h]; exact hn⟩
  | some v =>
    obtain ⟨n, hn⟩ := ht
    exact ⟨n + 1, by rw [show n + 1 + 1 = 1 + (n + 1) by omega, opIter_add, opIter_one, h]; exact hn⟩

/-- Close `some (..) = some (..)` between explicit states. -/
macro "fin" : tactic => `(tactic| all_goals ((simp only [phi, psi, Option.some.injEq, Prod.mk.injEq, true_and, and_true]) <;> omega))

theorem op_lt (c u m : Nat) (h : 2 * u < m) : op (c, u, m) = some (c, 2 * u, m + 1) := by
  simp [op, h]
theorem op_carry (c u m : Nat) (h : m < 2 * u) : op (c + 1, u, m) = some (c, 2 * u - m, m + 1) := by
  simp [op, show ¬ 2 * u < m by omega, show 2 * u ≠ m by omega]
theorem op_empty (c u m : Nat) (h : 2 * u = m) : op (c + 1, u, m) = some (c, 1, m + 2) := by
  simp [op, h]
theorem op_reset (u m : Nat) (h : m < 2 * u) :
    op (0, u, m) = some (2 * (m - u - 1), 2 * u - m, 2 * u - m + 3) := by
  simp [op, show ¬ 2 * u < m by omega, show 2 * u ≠ m by omega]
theorem op_halt (u m : Nat) (h : 2 * u = m) : op (0, u, m) = none := by
  simp [op, h]

theorem opIter_two (s : Nat × Nat × Nat) : opIter 2 s = (op s).bind op := by
  rw [show (2 : Nat) = 1 + 1 from rfl, opIter_add, opIter_one]
  cases op s with
  | none => rfl
  | some t => exact opIter_one t

theorem inner_op (z : Nat) : ∀ c p k, OpSem (psi c p k z) (inner c p k z) := by
  induction z using Nat.strongRecOn with
  | ind z ih =>
    intro c p k
    match c, p, z with
    | c, p + 1, z + 1 =>
      have e : psi c (p + 1) k (z + 1) = psi c p (k + 1) z := by
        simp only [psi, Prod.mk.injEq, true_and]; omega
      simp only [inner]; rw [e]; exact ih z (by omega) c p (k + 1)
    | c, p + 1, 0 =>
      refine ⟨0, ?_⟩
      rw [opIter_one]
      show op (c, k + 0 + 2, p + 1 + 2 * k + 0 + 4) = some (phi (c, p, 2 * k + 3))
      rw [op_lt _ _ _ (by omega)]; fin
    | c + 1, 0, z + 3 =>
      simp only [inner]
      refine opsem_one ?_ (ih z (by omega) c (2 * k + 2) 1)
      show op (c + 1, k + (z + 3) + 2, 0 + 2 * k + (z + 3) + 4) = some (psi c (2 * k + 2) 1 z)
      rw [op_carry _ _ _ (by omega)]; fin
    | c + 1, 0, 2 =>
      refine ⟨1, ?_⟩
      rw [opIter_two]
      show (op (c + 1, k + 2 + 2, 0 + 2 * k + 2 + 4)).bind op = some (phi (c, 2 * k + 2, 3))
      rw [op_carry _ _ _ (by omega), Option.bind_some, op_lt _ _ _ (by omega)]
      fin
    | c + 1, 0, 1 =>
      refine ⟨1, ?_⟩
      rw [opIter_two]
      show (op (c + 1, k + 1 + 2, 0 + 2 * k + 1 + 4)).bind op = some (phi (c, 2 * k + 3, 1))
      rw [op_carry _ _ _ (by omega), Option.bind_some, op_lt _ _ _ (by omega)]
      fin
    | c + 1, 0, 0 =>
      refine ⟨1, ?_⟩
      rw [opIter_two]
      show (op (c + 1, k + 0 + 2, 0 + 2 * k + 0 + 4)).bind op = some (phi (c, 2 * k + 3, 1))
      rw [op_empty _ _ _ (by omega), Option.bind_some, op_lt _ _ _ (by omega)]
      fin
    | 0, 0, z + 2 =>
      simp only [inner]
      refine opsem_one ?_ (ih z (by omega) (2 * k + 2) 1 0)
      show op (0, k + (z + 2) + 2, 0 + 2 * k + (z + 2) + 4) = some (psi (2 * k + 2) 1 0 z)
      rw [op_reset _ _ (by omega)]; fin
    | 0, 0, 1 =>
      refine ⟨1, ?_⟩
      rw [opIter_two]
      show (op (0, k + 1 + 2, 0 + 2 * k + 1 + 4)).bind op = some (phi (2 * k + 2, 1, 1))
      rw [op_reset _ _ (by omega), Option.bind_some, op_lt _ _ _ (by omega)]
      fin
    | 0, 0, 0 =>
      refine ⟨1, ?_⟩
      rw [opIter_one]
      show op (0, k + 0 + 2, 0 + 2 * k + 0 + 4) = none
      rw [op_halt _ _ (by omega)]

/-- **`F` is the doubling map**: one visit is one or more operations of `op`, and `F` halts iff `op` does. -/
theorem F_op (v : Nat × Nat × Nat) : OpSem (phi v) (F v) := by
  obtain ⟨c, p, b⟩ := v
  cases b with
  | zero =>
    refine ⟨0, ?_⟩
    rw [opIter_one]
    show op (c, 0 + 1, p + 0 + 3) = some (phi (c, p, 1))
    rw [op_lt _ _ _ (by omega)]; fin
  | succ n =>
    have e : phi (c, p, n + 1) = psi c p 0 n := by simp only [phi, psi, Prod.mk.injEq, true_and]; omega
    simp only [F]; rw [e]; exact inner_op n c p 0

theorem opIter_some_prefix {a b : Nat} {s t : Nat × Nat × Nat} (h : opIter (a + b) s = some t) :
    opIter a s ≠ none := by
  intro h0; rw [opIter_add, h0] at h; cases h

theorem orbit_op (v : Nat × Nat × Nat) : (∃ k, orbit v k = none) ↔ ∃ n, opIter n (phi v) = none := by
  constructor
  · rintro ⟨k, hk⟩
    induction k generalizing v with
    | zero => simp [orbit] at hk
    | succ k ih =>
      have hr := F_op v
      cases hF : F v with
      | none => rw [hF] at hr; exact hr
      | some v' =>
        rw [hF] at hr
        obtain ⟨j, hj⟩ := hr
        have hk' : orbit v' k = none := by simpa [orbit, hF] using hk
        obtain ⟨n, hn⟩ := ih v' hk'
        exact ⟨j + 1 + n, by rw [opIter_add, hj]; exact hn⟩
  · rintro ⟨n, hn⟩
    refine Classical.byContradiction fun hne => ?_
    have key : ∀ n, ∀ v, (∀ k, orbit v k ≠ none) → opIter n (phi v) ≠ none := by
      intro n
      induction n using Nat.strongRecOn with
      | ind n ih =>
        intro v hs
        have hr := F_op v
        cases hF : F v with
        | none => exact absurd (by simp [orbit, hF]) (hs 1)
        | some v' =>
          rw [hF] at hr
          obtain ⟨j, hj⟩ := hr
          have hs' : ∀ k, orbit v' k ≠ none := fun k h => hs (k + 1) (by simp [orbit, hF, h])
          by_cases hle : n ≤ j + 1
          · obtain ⟨d, hd⟩ : ∃ d, j + 1 = n + d := ⟨j + 1 - n, by omega⟩
            rw [hd] at hj
            exact opIter_some_prefix hj
          · obtain ⟨d, rfl⟩ : ∃ d, n = j + 1 + d := ⟨n - (j + 1), by omega⟩
            rw [opIter_add, hj]
            exact ih d (by omega) v' hs'
    exact key n v (fun k h => hne ⟨k, h⟩) hn

/-- **Main theorem.** 1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_---1LC halts from blank tape iff the doubling map `op`,
started at `(c, u, m) = (0, 2, 5)`, reaches the halt: a reset (c = 0) with 2u = m. -/
theorem halts_iff_op : HaltsFromBlank ↔ ∃ n, opIter n (0, 2, 5) = none := by
  rw [halts_iff, orbit_op]; rfl

/-! ## The orbit, evaluated -/

theorem opIter_ne_of_le {k N : Nat} {s : Nat × Nat × Nat} (hk : k ≤ N) (h : opIter N s ≠ none) :
    opIter k s ≠ none := by
  intro h0; apply h
  obtain ⟨d, rfl⟩ : ∃ d, N = k + d := ⟨N - k, by omega⟩
  rw [opIter_add, h0]; rfl

set_option maxRecDepth 100000 in
/-- The first 10,000 operations of the doubling map do not halt (Lean's kernel). -/
theorem op_kernel : ∀ k ≤ 10000, opIter k (0, 2, 5) ≠ none :=
  fun _ hk => opIter_ne_of_le hk (by decide +kernel)

/-- The first 10^7 operations of the doubling map do not halt (compiled evaluation). -/
theorem op_native : ∀ k ≤ 10000000, opIter k (0, 2, 5) ≠ none :=
  fun _ hk => opIter_ne_of_le hk (by native_decide)

end H50923
