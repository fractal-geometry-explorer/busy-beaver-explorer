import Model

/-!
# What a closed set of walls has to contain

The wall changes only through the parity of `N`, so one way to prove non-halting without any number theory would
be a set of walls that contains `1`, is closed under `mstep` for **both** signals, and never makes a count fail
(`Model.lean`'s hypothesis would then hold whatever the orbit of `N` does). `ratio5_not_enough` (`Model.lean`)
shows that the set "every counter at least 5 times the one below" is not closed. Here: every closed set contains
whole arithmetic families of walls, so a closed set cannot be cut out by inequalities between neighbouring counts.

Walls are listed top first. `P n` is the pile `K'(0)^n`.

* `mrun_pile`: the signals `1 (01)^n` build the wall `1 K'(0)^n K(0)` (bottom first).
* `odd_on_pile`: an odd signal on it dissolves the pile into the count: `K(2n + 2)`.
* `family`: from the wall `1`, the signals `1 (01)^(2i) 1 1 1` lead to `1 K(0) K(9i + 7)`, for every `i`.
* `closed_family`: so every set of walls that contains `1` and is closed under both signals contains
  `1 K(0) K(9i + 7)` for every `i`, and with it the whole run of odd signals from each of them.

Whether that run ever makes a count negative depends on `9i + 7` modulo a large power of 2: the top count `k`
stays odd for `t` steps exactly when it agrees with one 2-adic number `rho(0, 0)` in its last `t` binary digits
(`py/pairs.py`), and it fails only after about `k` steps. So the closed set needs `rho(0, 0)` to have a 1 among its
digits `p .. 2^p` for every `p`: a statement about the digits of a number made by a 3/2 recursion.
-/

namespace H3292

/-- The pile of `n` closed empty counters. -/
def P (n : Nat) : List It := List.replicate n (.c 0)

/-- The signals `(01)^n`. -/
def zo (n : Nat) : List Bool := (List.replicate n [false, true]).flatten

theorem mrun_append (w : List It) (a b : List Bool) :
    mrun w (a ++ b) = (mrun w a).bind fun v => mrun v b := by
  induction a generalizing w with
  | nil => simp [mrun]
  | cons s a ih =>
    simp only [List.cons_append, mrun]
    cases mstep w s with
    | none => rfl
    | some r => simp [ih]

theorem mrun_zo (n : Nat) : mrun (It.o 0 :: P 0) (zo n) = some (It.o 0 :: P n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have : zo (n + 1) = zo n ++ [false, true] := by
      simp [zo, List.replicate_succ']
    rw [this, mrun_append, ih]
    simp [mrun, mstep, P, List.replicate_succ]

/-- `1 (01)^n` builds `1 K'(0)^n K(0)`. -/
theorem mrun_pile (n : Nat) : mrun [] (true :: zo n) = some (It.o 0 :: P n) := by
  simp only [mrun, mstep, Option.bind_some]
  exact mrun_zo n

/-- An even signal on the pile dissolves it, each `K'(0)` adding 2 (and the empty wall adds 2). -/
theorem mstep_pile_even (n : Nat) : mstep (P n) false = some ([], (2 * n + 2 : Int), (2 * n + 2 : Int)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [P, List.replicate_succ] at ih ⊢
    rw [mstep.eq_def]
    have e : ((0 + if false = true then 1 else 0) % 2 == 1) = false := rfl
    simp only [e, ih]
    simp only [Nat.zero_div, Nat.zero_mod, Nat.mul_zero, Option.some.injEq, Prod.mk.injEq]
    simp only [Bool.false_eq_true, ite_false]
    constructor <;> push_cast <;> omega

/-- An odd signal on a single open counter with an even count: the count becomes `3k/2 + 2`. -/
theorem single_even (k : Nat) (hk : k % 2 = 0) : ∃ om orr, mstep [It.o k] true = some ([It.o (3 * k / 2 + 2)], om, orr) := by
  have : (k % 2 == 1) = false := by simp [hk]
  simp only [mstep, this]
  split
  · omega
  simp
  omega

/-- With an odd count a new `K(0)` is made under it. -/
theorem single_odd (k : Nat) (hk : k % 2 = 1) : ∃ om orr, mstep [It.o k] true = some ([It.o (3 * k / 2), It.o 0], om, orr) := by
  have : (k % 2 == 1) = true := by simp [hk]
  simp only [mstep, this]
  split
  · omega
  simp
  omega

/-- An odd signal on `1 K'(0)^n K(0)` dissolves the pile into the count: `1 K(2n + 2)`. -/
theorem odd_on_pile (n : Nat) : mstep (It.o 0 :: P n) true = some ([It.o (2 * n + 2)], 0, 0) := by
  have : ((0:Nat) % 2 == 1) = false := rfl
  rw [mstep.eq_def]
  simp only [this, mstep_pile_even]
  simp
  omega

/-- **From the wall `1`, the signals `1 (01)^(2i) 1 1 1` lead to `1 K(0) K(9i + 7)`.** -/
theorem family (i : Nat) :
    mrun [] ((true :: zo (2 * i)) ++ [true, true, true]) = some [It.o (9 * i + 7), It.o 0] := by
  rw [mrun_append, mrun_pile, Option.bind_some]
  obtain ⟨om1, orr1, h1⟩ := single_even (2 * (2 * i) + 2) (by omega)
  obtain ⟨om2, orr2, h2⟩ := single_odd (3 * (2 * (2 * i) + 2) / 2 + 2) (by omega)
  have e : 3 * (3 * (2 * (2 * i) + 2) / 2 + 2) / 2 = 9 * i + 7 := by omega
  simp only [mrun, odd_on_pile, Option.bind_some, h1, h2, e]

/-- Closed under both signals (as long as the model answers). -/
def Closed (S : List It → Prop) : Prop :=
  ∀ w s w' om orr, S w → mstep w s = some (w', om, orr) → S w'

theorem closed_mrun (S : List It → Prop) (hS : Closed S) :
    ∀ (w : List It) (ss : List Bool) (w' : List It), S w → mrun w ss = some w' → S w'
  | w, [], w', h, e => by simp only [mrun, Option.some.injEq] at e; rw [← e]; exact h
  | w, s :: ss, w', h, e => by
    simp only [mrun] at e
    cases e1 : mstep w s with
    | none => rw [e1] at e; cases e
    | some r =>
      obtain ⟨v, om, orr⟩ := r
      rw [e1, Option.bind_some] at e
      exact closed_mrun S hS v ss w' (hS w s v om orr h e1) e

/-- **Every closed set of walls containing `1` contains `1 K(0) K(9i + 7)` for every `i`**, and every wall of the
run of odd signals from it, as long as the run lasts. -/
theorem closed_family (S : List It → Prop) (hS : Closed S) (h0 : S []) (i t : Nat) (w : List It)
    (hw : mrun [It.o (9 * i + 7), It.o 0] (List.replicate t true) = some w) : S [It.o (9 * i + 7), It.o 0] ∧ S w := by
  have h1 := closed_mrun S hS [] _ _ h0 (family i)
  exact ⟨h1, closed_mrun S hS _ _ _ h1 hw⟩

/-- The member `i = 3` (count 34), by evaluation. -/
example : mrun [] ((true :: zo 6) ++ [true, true, true]) = some [.o 34, .o 0] := by decide +kernel

end H3292
