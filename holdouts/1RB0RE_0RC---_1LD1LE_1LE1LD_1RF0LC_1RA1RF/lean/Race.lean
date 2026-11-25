import End

/-!
# Odd runs stop the sweep

`astep` fails in only two ways (`End.lean`).  The second, an even bounce blocked by the far part, cannot happen when
the far part is clean (`far_even`).  The first is a crossing bounce whose right sweep from F reads the whole of
`(sx true N).reverse ++ true :: s` without stopping and ends in F, while the tape ends in blank (`r = false`).

A sweep from F stops at the first `0` it reads in E, so it gets through a word without stopping and ends in F only if
the word is in `(0 | 11)*`.  `rswL_witness`: a word with a `0` followed by an odd run of 1s that is followed by a `0`
or by the end of the word is never read that way.  Call such a run a *witness*.  `astep_T2_witness`: a crossing turn
with a clean far part and a witness in the frozen word `s` always has a next turn.

In the run (`py/race.py`) every crossing turn with blank end has a witness in `s` except the first one or two after
each time E reads the last 1 during a crossing, when `s` is `0` or empty.
-/

namespace H75625

open TM

theorem rswL_trues (k : Nat) (W xs : List Bool) :
    ∃ W', rswL false W (List.replicate (2 * k) true ++ xs) = rswL false W' xs := by
  induction k generalizing W with
  | zero => exact ⟨W, rfl⟩
  | succ k ih =>
    obtain ⟨W', h⟩ := ih (false :: true :: W)
    have e : List.replicate (2 * (k + 1)) true ++ xs = true :: true :: (List.replicate (2 * k) true ++ xs) := by
      rw [show 2 * (k + 1) = 2 * k + 2 by omega]; rfl
    exact ⟨W', by rw [e]; exact h⟩

theorem rswL_witness (k : Nat) (v : List Bool) (hv : v.head? ≠ some true) (u : List Bool) :
    ∀ (e : Bool) (W : List Bool),
      (rswL e W (u ++ false :: (List.replicate (2 * k + 1) true ++ v))).2 ≠ (false, none) := by
  induction u with
  | nil =>
    intro e W
    cases e with
    | true => simp [rswL]
    | false =>
      have e : List.replicate (2 * k + 1) true ++ v = List.replicate (2 * k) true ++ true :: v := by
        rw [List.replicate_succ', List.append_assoc, List.singleton_append]
      obtain ⟨W', h⟩ := rswL_trues k (false :: W) (true :: v)
      have h2 : rswL false W ([] ++ false :: (List.replicate (2 * k + 1) true ++ v)) = rswL false W' (true :: v) := by
        rw [e, ← h]; rfl
      rw [h2]
      cases v with
      | nil => simp [rswL]
      | cons x v =>
        cases x with
        | true => exact absurd rfl hv
        | false => simp [rswL]
  | cons x u ih =>
    intro e W
    simp only [List.cons_append, rswL]
    split
    · simp
    · exact ih _ _

theorem astep_T2_witness (N ws : List Bool) (p : Bool) (u : List Bool) (k : Nat) (v : List Bool)
    (hv : v.head? ≠ some true) (r : Bool) :
    (astep (.T2 N (dbl (true :: ws)) p (u ++ false :: (List.replicate (2 * k + 1) true ++ v)) r)).isSome := by
  have hw := rswL_witness k v hv ((sx true N).reverse ++ true :: u) false []
  simp only [List.append_assoc, List.cons_append] at hw
  have hf := far_even ws
  simp only [astep, dbl, two, List.cons_append, List.nil_append, coreO]
  simp only [dbl, two, List.cons_append, List.nil_append] at hf
  split
  · revert hw
    generalize rswL false [] _ = x
    obtain ⟨W, e, o⟩ := x
    intro hw
    cases o <;> cases e <;> cases r <;> simp_all [fromSweep, endS]
  · rw [hf]
    simp only
    revert hw
    generalize rswL false [] _ = x
    obtain ⟨W, e, o⟩ := x
    intro hw
    cases o <;> cases e <;> cases r <;> simp_all [fromSweep, endS]

/-! ## Clean near parts

In the run almost every near part of a crossing turn with blank end is clean: `dbl (true :: ws) ++ [false]`, that is
`10 (00 | 10)* 0` (`py/race.py`).  Its bounce is odd exactly when `par false ws` is true.

* `near_odd`: an odd bounce stops inside the near part, so the frozen word gets `0 (00 | 11)* 1` put in front.  If the
  old frozen word is empty or starts with `0`, the new one has a witness (`near_odd_witness`).
* `near_even`: an even bounce against a frozen word that starts with `0` eats that `0` and leaves a clean near part
  `dbl (true :: false :: sx false ws)` (one more `0` comes from the far part).
-/

theorem sx_append (xs ys : List Bool) : ∀ q, sx q (xs ++ ys) = sx q xs ++ sx (par q xs) ys := by
  induction xs with
  | nil => intro q; rfl
  | cons x xs ih => intro q; simp [sx, par, ih]

theorem par_dbl (ws : List Bool) : ∀ q, par q (dbl ws) = par q ws := by
  induction ws with
  | nil => intro q; rfl
  | cons x ws ih => intro q; cases x <;> cases q <;> simp [dbl, two, par, ih]

/-- `j` pairs `t f` put in front of `W`. -/
def tf : Nat → List Bool → List Bool
  | 0, W => W
  | j + 1, W => tf j (true :: false :: W)

theorem rswL_true_dd (v t : List Bool) (j : Nat) : ∀ W : List Bool,
    rswL true W (dd (List.replicate j true ++ false :: v) ++ t) = (tf j W, true, some (false :: dd v ++ t)) := by
  induction j with
  | zero => intro W; rfl
  | succ j ih =>
    intro W
    rw [List.replicate_succ, List.cons_append]
    exact ih (true :: false :: W)

theorem rswL_dd_app (l t : List Bool) : ∀ W : List Bool,
    rswL false W (dd l ++ t) = rswL false ((l.reverse.flatMap fun z => [false, z]) ++ W) t := by
  induction l with
  | nil => intro W; rfl
  | cons z l ih =>
    intro W
    have h2 : rswL false W (dd (z :: l) ++ t) = rswL false (false :: z :: W) (dd l ++ t) := by
      cases z <;> rfl
    rw [h2, ih]
    simp [List.flatMap_append, List.append_assoc]

theorem split_false (m : List Bool) :
    ∃ j v, m ++ [false] = List.replicate j true ++ false :: v ∧ (v = [] ∨ ∃ v', v = v' ++ [false]) := by
  induction m with
  | nil => exact ⟨0, [], rfl, Or.inl rfl⟩
  | cons x m ih =>
    cases x with
    | true =>
      obtain ⟨j, v, h, hv⟩ := ih
      exact ⟨j + 1, v, by rw [List.cons_append, h]; rfl, hv⟩
    | false => exact ⟨0, m ++ [false], rfl, Or.inr ⟨m, rfl⟩⟩

theorem near_rev (ws : List Bool) :
    (sx true (dbl (true :: ws) ++ [false])).reverse =
      par false ws :: dd ((sx false ws).reverse ++ [false]) := by
  rw [sx_append, sx_dbl, par_dbl]
  simp only [sx, par, Bool.bne_false, bne_self_eq_false, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.singleton_append, dd_reverse]

theorem near_odd (ws t : List Bool) (h : par false ws = true) :
    ∃ j v, rswL false [] ((sx true (dbl (true :: ws) ++ [false])).reverse ++ t) =
        (tf j [true], true, some (false :: dd v ++ t)) ∧ (v = [] ∨ ∃ v', v = v' ++ [false]) := by
  obtain ⟨j, v, hs, hv⟩ := split_false (sx false ws).reverse
  refine ⟨j, v, ?_, hv⟩
  rw [near_rev, h, hs, List.cons_append]
  exact rswL_true_dd v t j [true]

theorem near_odd_witness (v s : List Bool) (hv : v = [] ∨ ∃ v', v = v' ++ [false]) :
    ∃ u, false :: dd v ++ true :: s = u ++ false :: (List.replicate (2 * 0 + 1) true ++ s) := by
  rcases hv with rfl | ⟨v', rfl⟩
  · exact ⟨[], rfl⟩
  · refine ⟨false :: dd v' ++ [false], ?_⟩
    rw [dd_append]
    simp [dd]

theorem near_even (ws s : List Bool) (h : par false ws = false) :
    rswL false [] ((sx true (dbl (true :: ws) ++ [false])).reverse ++ true :: false :: s) =
      (dbl (true :: false :: sx false ws), true, some s) := by
  rw [near_rev, h, List.cons_append]
  show rswL false [false] (dd ((sx false ws).reverse ++ [false]) ++ true :: false :: s) = _
  rw [rswL_dd_app]
  have e : ((sx false ws).reverse ++ [false]).reverse.flatMap (fun z => [false, z]) ++ [false]
      = false :: dbl (false :: sx false ws) := by
    rw [flatMap_dbl]; simp
  show (true :: (((sx false ws).reverse ++ [false]).reverse.flatMap (fun z => [false, z]) ++ [false]), true, some s) = _
  rw [e]
  rfl

end H75625
