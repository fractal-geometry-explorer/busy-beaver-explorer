import Pile

/-!
# Non-halting from a statement about integers only

`Stack.lean` proves the counter-stack step wherever `res` answers, and `Pile.lean` proves that the closed empty
counters stay in one pile.  Here the two are joined with a converse of `res_model`:

* `res_complete`: on a good wall (`Pile.lean`) `res` answers whenever `mstep` (the integer model of
  `py/stackmodel.py`) answers and the block it returns is not empty.  So the buffers of the cell-level rules are
  always enough; the only thing that can stop the rules is the model itself.
* `stepRes_complete`: the whole step, for `N ≥ 5`.
* `morbit`: the orbit of the integer model `mstepN` from the wall `K(2)` and `N = 48`, which is the step start
  `11101101111101 A> 0 b^48 1` that blank tape reaches in 10,206 steps (`blank_to_start`).
* **`not_halts_of_model`**: if every wall of `morbit` exists, has `N ≥ 5`, and has no `K(0)` away from the pile
  (`okO`), the machine does not halt from blank tape.

So the open question is now a statement about one explicit recursion on lists of integers: along the orbit, no
rebuilt count `3k/2 + om` is negative, or zero anywhere but directly on the pile.  No simulator, no tape.
-/

namespace H3292

open TM

/-- What an item passes up is never less than the part of it that came from below (`om ≥ orr`). -/
theorem mstep_gap : ∀ (ws : List It) (s : Bool) (ws' : List It) (om orr : Int),
    mstep ws s = some (ws', om, orr) → orr ≤ om
  | [], false, _, _, _, h => by simp only [mstep, Option.some.injEq, Prod.mk.injEq] at h; omega
  | [], true, _, _, _, h => by simp only [mstep, Option.some.injEq, Prod.mk.injEq] at h; omega
  | .o k :: V, false, _, _, _, h => by simp only [mstep, Option.some.injEq, Prod.mk.injEq] at h; omega
  | .o k :: V, true, _, _, _, h => by
    simp only [mstep] at h
    cases e : mstep V (k % 2 == 1) with
    | none => rw [e] at h; cases h
    | some r =>
      obtain ⟨V', om', orr'⟩ := r
      rw [e] at h; simp only at h
      split at h
      · cases h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
  | .c 0 :: V, true, _, _, _, h => by simp only [mstep, Option.some.injEq, Prod.mk.injEq] at h; omega
  | .c 0 :: V, false, _, _, _, h => by
    simp only [mstep] at h
    split at h
    · cases h
    · next V' om' orr' e =>
      have := mstep_gap V _ V' om' orr' e
      simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
  | .c (j + 1) :: V, s, _, _, _, h => by
    simp only [mstep] at h
    split at h
    · cases h
    · next V' om' orr' e =>
      have := mstep_gap V _ V' om' orr' e
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      split at h <;> push_cast at h <;> omega

/-- `f` answers wherever the model answers with a non-empty block. -/
def CompOK (ws : List It) (f : Bool → Nat → Option Res) : Prop :=
  ∀ (s : Bool) (n : Nat) (ws' : List It) (om orr : Int), mstep ws s = some (ws', om, orr) →
    1 ≤ (n : Int) + om - (if s then 0 else 2) → ∃ r, f s n = some r

theorem goX_complete (ws : List It) (f : Bool → Nat → Option Res) (hf : CompOK ws f) (x y : Nat)
    (ws' : List It) (om orr : Int) (hy : 1 ≤ y) (h : mstep ws (x % 2 == 0) = some (ws', om, orr))
    (hR : 1 ≤ (y : Int) + 3 * (x / 2 : Nat) + (if x % 2 = 0 then 0 else 2) + om) :
    ∃ r, goX f x y = some r := by
  unfold goX
  split
  · next hx =>
    have h' : mstep ws true = some (ws', om, orr) := by simpa [hx] using h
    obtain ⟨r, e⟩ := hf true (y + 3 * (x / 2)) ws' om orr h'
      (by rw [ite_t rfl]; rw [ite_t hx] at hR; push_cast at hR ⊢; omega)
    exact ⟨_, by rw [e]; rfl⟩
  · next hx =>
    rw [ite_t (by omega)]
    have hb : (x % 2 == 0) = false := by simp [hx]
    have h' : mstep ws false = some (ws', om, orr) := by rw [← hb]; exact h
    obtain ⟨r, e⟩ := hf false (y + 3 * (x / 2) + 4) ws' om orr h'
      (by rw [ite_f Bool.false_ne_true]; rw [ite_f hx] at hR; push_cast at hR ⊢; omega)
    exact ⟨_, by rw [e]; rfl⟩

/-- **The cell-level rules cover the model.**  On a good wall, `res` answers whenever `mstep` does and the block
it returns is not empty. -/
theorem res_complete : ∀ ws : List It, good ws = true → CompOK ws (res ws) := by
  intro ws
  induction ws with
  | nil =>
    intro _ s n ws' om orr h hn
    cases s with
    | false => exact ⟨_, rfl⟩
    | true =>
      simp only [mstep, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, -⟩ := h
      simp only [res]; rw [ite_t (by rw [ite_t rfl] at hn; omega)]; exact ⟨_, rfl⟩
  | cons x V ih =>
    intro hg s n ws' om orr h hn
    have ihV := ih (good_tail x V hg)
    cases x with
    | o k =>
      cases s with
      | false => exact ⟨_, rfl⟩
      | true =>
        rw [ite_t rfl] at hn
        rw [mstep_o] at h
        cases e : mstep V (k % 2 == 1) with
        | none => rw [e] at h; cases h
        | some r =>
          obtain ⟨V', om', orr'⟩ := r
          rw [e] at h
          simp only [Option.bind_some] at h
          split at h
          · cases h
          · next hk =>
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨-, rfl, rfl⟩ := h
            have gap := mstep_gap V _ V' om' orr' e
            cases k with
            | zero =>
              rw [show ((0 : Nat) % 2 == 1) = false from rfl] at e
              obtain ⟨r0, e0⟩ := ihV false 3 V' om' orr' e (by rw [ite_f Bool.false_ne_true]; push_cast at hk; omega)
              obtain ⟨om0, orr0, m1, m2, m3⟩ := res_model V false 3 r0 e0
              obtain ⟨a0, M0, u0⟩ := r0
              rw [e] at m1
              simp only [Option.some.injEq, Prod.mk.injEq] at m1
              obtain ⟨h1, rfl, rfl⟩ := m1
              rw [ite_f Bool.false_ne_true] at m2
              simp only at m2 m3
              simp only [res, e0, rebR]
              rw [ite_t ⟨by push_cast at hk; omega, by push_cast at hk hn; omega⟩]
              exact ⟨_, rfl⟩
            | succ k =>
              have hb : ((k + 1) % 2 == 1) = (k % 2 == 0) := by
                rcases Nat.mod_two_eq_zero_or_one k with hk' | hk' <;> simp [hk', Nat.add_mod]
              rw [hb] at e
              obtain ⟨r0, e0⟩ := goX_complete V _ ihV k 2 V' om' orr' (by omega) e
                (by rcases Nat.mod_two_eq_zero_or_one k with hk' | hk' <;> simp only [hk'] <;>
                      push_cast at hk ⊢ <;> omega)
              obtain ⟨om0, orr0, m1, m2, m3⟩ := goX_model V _ (res_model V) k 2 r0 e0
              obtain ⟨a0, M0, u0⟩ := r0
              rw [e] at m1
              simp only [Option.some.injEq, Prod.mk.injEq] at m1
              obtain ⟨h1, rfl, rfl⟩ := m1
              simp only at m2 m3
              simp only [res, e0, rebR]
              rw [ite_t ⟨by rcases Nat.mod_two_eq_zero_or_one k with hk' | hk' <;> simp only [hk'] at m2 <;>
                    push_cast at hk m2 ⊢ <;> omega,
                  by rcases Nat.mod_two_eq_zero_or_one k with hk' | hk' <;> simp only [hk'] at m2 m3 <;>
                    push_cast at hk hn m2 m3 ⊢ <;> omega⟩]
              exact ⟨_, rfl⟩
    | c j =>
      cases j with
      | zero =>
        cases s with
        | false =>
          rw [mstep_c0, show ((0 : Nat) % 2 == 1) = false from rfl] at h
          cases e : mstep V false with
          | none => rw [e] at h; cases h
          | some r =>
            obtain ⟨V', om', orr'⟩ := r
            rw [e] at h
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨-, rfl, -⟩ := h
            rw [ite_f Bool.false_ne_true] at hn
            obtain ⟨r0, e0⟩ := ihV false (n + 2) V' om' orr' e (by rw [ite_f Bool.false_ne_true]; push_cast at hn ⊢; omega)
            exact ⟨r0, by simp only [res]; exact e0⟩
        | true =>
          simp only [mstep, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl, -⟩ := h
          rw [ite_t rfl] at hn
          simp only [res]
          rw [ite_t ⟨good_c0 V hg, by omega⟩]
          exact ⟨_, rfl⟩
      | succ j =>
        cases s with
        | false =>
          rw [mstep_c0] at h
          have hb : ((j + 1) % 2 == 1) = (j % 2 == 0) := by
            rcases Nat.mod_two_eq_zero_or_one j with hk' | hk' <;> simp [hk', Nat.add_mod]
          rw [hb] at h
          cases e : mstep V (j % 2 == 0) with
          | none => rw [e] at h; cases h
          | some r =>
            obtain ⟨V', om', orr'⟩ := r
            rw [e] at h
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨-, rfl, -⟩ := h
            rw [ite_f Bool.false_ne_true] at hn
            obtain ⟨r0, e0⟩ := goX_complete V _ ihV j (n + 1) V' om' orr' (by omega) e
              (by rcases Nat.mod_two_eq_zero_or_one j with hk' | hk' <;> simp only [hk'] <;>
                    push_cast at hn ⊢ <;> omega)
            exact ⟨r0, by simp only [res]; exact e0⟩
        | true =>
          rw [mstep_c1] at h
          rw [ite_t rfl] at hn
          cases j with
          | zero =>
            rw [show ((0 + 1 + 1) % 2 == 1) = false from rfl] at h
            cases e : mstep V false with
            | none => rw [e] at h; cases h
            | some r =>
              obtain ⟨V', om', orr'⟩ := r
              rw [e] at h
              simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨-, rfl, -⟩ := h
              obtain ⟨r0, e0⟩ := ihV false (n + 7) V' om' orr' e
                (by rw [ite_f Bool.false_ne_true]; push_cast at hn ⊢; omega)
              exact ⟨_, by simp only [res, e0]; rfl⟩
          | succ j =>
            have hb : ((j + 1 + 1 + 1) % 2 == 1) = (j % 2 == 0) := by
              rcases Nat.mod_two_eq_zero_or_one j with hk' | hk' <;> simp [hk', Nat.add_mod]
            rw [hb] at h
            cases e : mstep V (j % 2 == 0) with
            | none => rw [e] at h; cases h
            | some r =>
              obtain ⟨V', om', orr'⟩ := r
              rw [e] at h
              simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨-, rfl, -⟩ := h
              obtain ⟨r0, e0⟩ := goX_complete V _ ihV j (n + 6) V' om' orr' (by omega) e
                (by rcases Nat.mod_two_eq_zero_or_one j with hk' | hk' <;>
                      simp only [hk'] <;> push_cast at hn ⊢ <;> omega)
              exact ⟨_, by simp only [res, e0]; rfl⟩

/-- The block before the wall's answer: `3N/2 + 5` (N even) or `(3N + 9)/2` (N odd). -/
def base (N : Nat) : Nat := if N % 2 = 0 then 3 * N / 2 + 5 else (3 * N + 9) / 2

theorem mstepN_spec (ws ws' : List It) (N M : Nat) (h : mstepN ws N = some (ws', M)) :
    ∃ om orr, mstep ws (N % 2 == 1) = some (ws', om, orr) ∧ (M : Int) = (base N : Int) + om := by
  unfold mstepN at h
  cases e : mstep ws (N % 2 == 1) with
  | none => rw [e] at h; cases h
  | some r =>
    obtain ⟨V', om, orr⟩ := r
    rw [e] at h
    dsimp only at h
    by_cases hneg : ((if N % 2 = 0 then 3 * N / 2 + 5 else (3 * N + 9) / 2 : Nat) : Int) + om < 0
    · rw [ite_t hneg] at h; cases h
    · rw [ite_f hneg] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, hM⟩ := h
      refine ⟨om, orr, rfl, ?_⟩
      unfold base
      rw [← hM]
      omega

/-- **The whole step**: on a good wall with `N ≥ 5`, `stepRes` answers whenever `mstepN` answers with `N' ≥ 1`. -/
theorem stepRes_complete (ws ws' : List It) (N M : Nat) (hg : good ws = true) (hN : 5 ≤ N) (hM : 1 ≤ M)
    (h : mstepN ws N = some (ws', M)) : stepRes ws N = some (ws', M) := by
  obtain ⟨om, orr, e, hM'⟩ := mstepN_spec ws ws' N M h
  have hb : (N % 2 == 1) = ((N - 5) % 2 == 0) := by
    rcases Nat.mod_two_eq_zero_or_one N with hk | hk <;> simp [hk] <;> omega
  rw [hb] at e
  obtain ⟨r0, e0⟩ := goX_complete ws _ (res_complete ws hg) (N - 5) 12 ws' om orr (by omega) e (by
    unfold base at hM'
    rcases Nat.mod_two_eq_zero_or_one N with hk | hk
    · rw [ite_t hk] at hM'; rw [ite_f (by omega)]; push_cast at hM' ⊢; omega
    · rw [ite_f (by omega)] at hM'; rw [ite_t (by omega)]; push_cast at hM' ⊢; omega)
  have hs : stepRes ws N = some (r0.1, r0.2.1) := by
    unfold stepRes; rw [ite_t hN, e0]; rfl
  obtain ⟨om2, orr2, e2, hM2⟩ := mstepN_spec ws r0.1 N r0.2.1 (step_model ws r0.1 N r0.2.1 hs)
  rw [hb, e] at e2
  simp only [Option.some.injEq, Prod.mk.injEq] at e2
  obtain ⟨h1, rfl, rfl⟩ := e2
  rw [hs, ← h1]
  congr 2
  omega

/-! ## The orbit of the integer model -/

/-- The orbit of `mstepN` from the wall `K(2)` with `N = 48`. -/
def morbit : Nat → Option (List It × Nat)
  | 0 => some ([.o 2], 48)
  | i + 1 => (morbit i).bind fun p => mstepN p.1 p.2

theorem wl_start : wl [.o 2] = wall0 := rfl

/-- One step of the stack takes at least one step of the machine. -/
theorem step_ok1 (ws ws' : List It) (N M : Nat) (h : stepRes ws N = some (ws', M)) :
    ∃ n, 1 ≤ n ∧ steps n (S (wl ws) N) = some (S (wl ws') M) := by
  unfold stepRes at h
  split at h
  · next hN =>
    cases e : goX (res ws) (N - 5) 12 with
    | none => rw [e] at h; cases h
    | some r =>
      rw [e] at h; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨n, rfl⟩ : ∃ n, N = n + 5 := ⟨N - 5, by omega⟩
      have a := part1 (wtl ws) n
      rw [← wt_eq] at a
      rw [Nat.add_sub_cancel] at e
      obtain ⟨m, hm⟩ := goX_ok ws _ (res_ok ws) n 12 r e .top .top rfl
      refine ⟨5 * n + 695 + m, by omega, ?_⟩
      have h2 := steps_seq H3292.trans a hm
      rw [← wl_spec, ← wl_spec] at h2
      exact h2
  · cases h

/-- **Non-halting from the integer model.**  If along the orbit of `mstepN` from `(K(2), 48)` every step answers,
`N` stays at least 5, and no step makes a `K(0)` away from the pile, the machine does not halt from blank tape. -/
theorem not_halts_of_model
    (h : ∀ i, ∃ ws N, morbit i = some (ws, N) ∧ 5 ≤ N ∧ okO ws = true) : ¬ HaltsFromBlank := by
  have key : ∀ i ws N, morbit i = some (ws, N) → good ws = true ∧ ∃ n, i ≤ n ∧ steps n init = some (S (wl ws) N) := by
    intro i
    induction i with
    | zero =>
      intro ws N e
      simp only [morbit, Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      exact ⟨rfl, 10206, Nat.zero_le _, by rw [wl_start]; exact blank_to_start⟩
    | succ i ih =>
      intro ws' M e
      obtain ⟨ws, N, e0, hN, -⟩ := h i
      obtain ⟨ws1, N1, e1, hM, ho⟩ := h (i + 1)
      rw [e] at e1
      simp only [Option.some.injEq, Prod.mk.injEq] at e1
      obtain ⟨rfl, rfl⟩ := e1
      obtain ⟨hg, n, hn, hr⟩ := ih ws N e0
      simp only [morbit, e0, Option.bind_some] at e
      have hs := stepRes_complete ws ws' N M hg hN (by omega) e
      obtain ⟨om, orr, hm, -⟩ := mstepN_spec ws ws' N M e
      refine ⟨mstep_good ws _ ws' om orr hg hm ho, ?_⟩
      obtain ⟨m, hm1, hm2⟩ := step_ok1 ws ws' N M hs
      exact ⟨n + m, by omega, steps_seq H3292.trans hr hm2⟩
  rintro ⟨n, c', h1, h2⟩
  obtain ⟨ws, N, e, -, -⟩ := h (n + 1)
  obtain ⟨-, m, hm, h3⟩ := key (n + 1) ws N e
  have e2 : m = n + ((m - n - 1) + 1) := by omega
  rw [e2] at h3
  have h4 : (some _ : Option Config) = none := h3.symm.trans (steps_halt H3292.trans h1 h2 (m - n - 1))
  cases h4

end H3292

/-! ## The first steps of the orbit, by the kernel -/

namespace H3292

/-- Runs `t` steps of the model from `(ws, N)`, checking `N ≥ 5` and `okO` on the way. -/
def mcheck : Nat → List It → Nat → Bool
  | 0, ws, N => 5 ≤ N && okO ws
  | t + 1, ws, N => 5 ≤ N && okO ws &&
    match mstepN ws N with
    | some (ws', M) => mcheck t ws' M
    | none => false

theorem mcheck_ok : ∀ (t i : Nat) (ws : List It) (N : Nat), morbit i = some (ws, N) → mcheck t ws N = true →
    ∀ j ≤ t, ∃ ws' N', morbit (i + j) = some (ws', N') ∧ 5 ≤ N' ∧ okO ws' = true
  | 0, i, ws, N, e, h, j, hj => by
    obtain rfl : j = 0 := by omega
    simp only [mcheck, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨ws, N, e, h.1, h.2⟩
  | t + 1, i, ws, N, e, h, j, hj => by
    simp only [mcheck, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hN, ho⟩, hr⟩ := h
    cases j with
    | zero => exact ⟨ws, N, e, hN, ho⟩
    | succ j =>
      cases e2 : mstepN ws N with
      | none => rw [e2] at hr; cases hr
      | some p =>
        obtain ⟨ws', M⟩ := p
        rw [e2] at hr
        have e3 : morbit (i + 1) = some (ws', M) := by simp only [morbit, e, Option.bind_some, e2]
        have := mcheck_ok t (i + 1) ws' M e3 hr j (by omega)
        rwa [show i + 1 + j = i + (j + 1) by omega] at this

theorem model_first : ∀ j ≤ 50000, ∃ ws N, morbit j = some (ws, N) ∧ 5 ≤ N ∧ okO ws = true := by
  intro j hj
  have := mcheck_ok 50000 0 [.o 2] 48 rfl (by decide +kernel) j hj
  simpa using this

end H3292

/-! ## "Each counter at least 5 times the one below" is not enough on its own

Along the orbit every open counter has been at least 5 times the open counter under it (3,000,000 steps,
`py/modelorbit.py`), and if that held forever no count could fail.  But the bound is not kept by the rules: the
wall `1 K(0) K(114520) K(596629)` (bottom first) satisfies it, yet 16 odd signals in a row make a count negative
(the bound breaks after the first).  So a proof has to use more than the bound: which walls are reachable. -/

namespace H3292

/-- Every item is at least 5 times the item below it (list top first). -/
def ratio5 : List It → Bool
  | x :: y :: ws => (5 * (match y with | .o k => k | .c k => k) ≤ (match x with | .o k => k | .c k => k)) && ratio5 (y :: ws)
  | _ => true

theorem ratio5_not_enough :
    ratio5 [.o 596629, .o 114520, .o 0] = true ∧
    (mrun [.o 596629, .o 114520, .o 0] (List.replicate 15 true)).isSome = true ∧
    mrun [.o 596629, .o 114520, .o 0] (List.replicate 16 true) = none := by
  decide +kernel

end H3292
