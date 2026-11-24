/-!
# The walk's δ is short: δ < 2^((7j − 1)/2)

The closed rebuild map of `py/map.py` sends the macro state (h, n, N) to (b, n + c, 2^(n+c) + (N >> j) − δ), where
(j, b, δ) come from a walk over the pairs of digits of N from the bottom.  This file restates that walk (`walk`,
pairs given lowest first as (lower digit, upper digit)) and proves, for every input, that the walk's δ is shorter
than 7/2 of the number of digits read (`walk_delta_lt`): if the walk stops after i pairs (j = 2i + 1 digits), then
δ < 2^(7i + 3).

A halt needs δ = (N >> j) + 1, and N >> j ≥ 2^(L − 1 − j) for a counter of L digits, so a rebuild cannot halt
unless 7i + 3 > L − 1 − j, that is unless the walk reads more than (2L − 1)/9 of the counter's digits
(`no_halt_if_short`).  The walk itself (that it is the rebuild) is checked against the exact rebuild in
`py/map.py`, not proved here; what is proved is the bound for the map as written.
-/

namespace H49767Delta

inductive Mode | O | Q
  deriving DecidableEq

/-- the value of a pair (lower digit, upper digit), 0 .. 3 -/
def pv (x : Bool × Bool) : Nat := (if x.1 then 1 else 0) + (if x.2 then 2 else 0)

/-- a pending borrow: a pair 00 counts as 11 and keeps it, any other pair is lowered by one -/
def lower (borrow : Bool) (v : Nat) : Nat := if borrow then (if v = 0 then 3 else v - 1) else v

def termO (k : Nat) : Nat := (3 * 2 ^ (2 * k + 2) - 1) * 2 ^ (5 * k + 5)

def termQ (flag : Bool) (k v : Nat) : Nat :=
  let A := if flag then 2 ^ (7 * k + 10) - 2 ^ (5 * k + 7) else 2 ^ (7 * k + 9) - 3 * 2 ^ (5 * k + 6)
  let B := if flag then 2 ^ (7 * k + 11) - 2 ^ (5 * k + 7) - 2 else 2 ^ (7 * k + 10) - 3 * 2 ^ (5 * k + 6) - 2
  if v = 0 then A else if v = 2 then A + 10 else B

def termStop (k : Nat) (b : Bool) : Nat := (if b then 0 else 1) + 2 ^ (5 * k + 5) * (3 * 2 ^ (2 * k + 3) - 1)

/-- The walk of `py/map.py`.  `k` pairs 11 skipped since the last term, `p` pairs read up to the last term, `d` the
sum of the terms so far (each later pair shifts it by 5 places).  Result: (pairs read i, next digit b, δ). -/
def walkAux : List (Bool × Bool) → Mode → Bool → Bool → Nat → Nat → Nat → Option (Nat × Bool × Nat)
  | [], _, _, _, _, _, _ => none
  | x :: rest, S, flag, borrow, k, p, d =>
    let v := lower borrow (pv x)
    if v = 3 then walkAux rest S flag (borrow && pv x == 0) (k + 1) p d
    else match S with
      | .O =>
        if v = 1 then
          match rest with
          | [] => none
          | y :: _ => some (p + k + 1, y.1, d * 2 ^ (5 * (k + 1)) + termStop k y.1)
        else walkAux rest (if v = 0 then .O else .Q) (if v = 0 then flag else false) (v == 0) 0 (p + k + 1)
          (d * 2 ^ (5 * (k + 1)) + termO k)
      | .Q =>
        walkAux rest (if v = 0 then .Q else .O) (if v = 0 then true else flag) true 0 (p + k + 1)
          (d * 2 ^ (5 * (k + 1)) + termQ flag k v)

/-- header 0110101 starts in mode O, 0110111 in mode Q -/
def walk (h : Bool) (pairs : List (Bool × Bool)) : Option (Nat × Bool × Nat) :=
  walkAux pairs (if h then .Q else .O) false false 0 0 0

/-! ## Bounds on the terms -/

theorem pow_split (a b : Nat) : 2 ^ (a + b) = 2 ^ a * 2 ^ b := Nat.pow_add 2 a b

theorem pow_pos' (a : Nat) : 0 < 2 ^ a := Nat.two_pow_pos a

theorem termO_lt (k : Nat) : termO k < 2 ^ (7 * (k + 1) + 4) := by
  unfold termO
  have h1 : (3 * 2 ^ (2 * k + 2) - 1) * 2 ^ (5 * k + 5) ≤ 3 * 2 ^ (2 * k + 2) * 2 ^ (5 * k + 5) :=
    Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have h2 : 3 * 2 ^ (2 * k + 2) * 2 ^ (5 * k + 5) = 3 * 2 ^ (7 * k + 7) := by
    rw [Nat.mul_assoc, ← Nat.pow_add]; congr 2; all_goals omega
  have h3 : 2 ^ (7 * (k + 1) + 4) = 2 ^ (7 * k + 7) * 2 ^ 4 := by rw [← Nat.pow_add]; congr 1; all_goals omega
  have := pow_pos' (7 * k + 7)
  rw [h3]; simp only [Nat.reducePow]; omega

theorem termQ_lt (flag : Bool) (k v : Nat) : termQ flag k v < 2 ^ (7 * (k + 1) + 4) := by
  have e10 : 2 ^ (7 * k + 10) = 2 ^ (7 * k + 9) * 2 := by rw [← Nat.pow_succ]
  have e11 : 2 ^ (7 * k + 11) = 2 ^ (7 * k + 9) * 4 := by
    rw [show 7 * k + 11 = (7 * k + 9) + 2 by omega, Nat.pow_add]
  have e : 2 ^ (7 * (k + 1) + 4) = 2 ^ (7 * k + 9) * 4 := by
    rw [show 7 * (k + 1) + 4 = (7 * k + 9) + 2 by omega, Nat.pow_add]
  have h512 : 512 ≤ 2 ^ (7 * k + 9) := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 9 ≤ 7 * k + 9 by omega)
    simpa using this
  have := Nat.two_pow_pos (5 * k + 7)
  have := Nat.two_pow_pos (5 * k + 6)
  unfold termQ
  rw [e]
  cases flag <;> simp only [Bool.false_eq_true, ite_true, ite_false] <;>
    split <;> (try split) <;> omega

theorem termStop_lt (k : Nat) (b : Bool) : termStop k b < 3 * 2 ^ (7 * (k + 1) + 1) := by
  unfold termStop
  have h1 : 2 ^ (5 * k + 5) * (3 * 2 ^ (2 * k + 3) - 1) = 3 * 2 ^ (7 * (k + 1) + 1) - 2 ^ (5 * k + 5) := by
    rw [Nat.mul_sub_one, Nat.mul_left_comm, ← Nat.pow_add]; congr 3; all_goals omega
  have h2 : 2 ≤ 2 ^ (5 * k + 5) := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 1 ≤ 5 * k + 5 by omega)
    simpa using this
  have h3 : 2 ^ (5 * k + 5) ≤ 2 ^ (7 * (k + 1) + 1) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  rw [h1]; cases b <;> simp <;> omega

/-! ## The invariant: after p pairs the sum is below 2^(7p + 4) (and 0 for p = 0) -/

theorem step_lt (d T k p : Nat) (hd : d < 2 ^ (7 * p + 4)) (h0 : p = 0 → d = 0)
    (hT : T < 2 ^ (7 * (k + 1) + 4)) : d * 2 ^ (5 * (k + 1)) + T < 2 ^ (7 * (p + k + 1) + 4) := by
  by_cases hp : p = 0
  · subst hp; rw [h0 rfl, Nat.zero_mul, Nat.zero_add]; rwa [show 7 * (0 + k + 1) + 4 = 7 * (k + 1) + 4 by omega]
  · have eA : 2 ^ (7 * (p + k + 1) + 4) = 2 ^ (7 * p + 4) * 2 ^ (5 * (k + 1)) * 2 ^ (2 * (k + 1)) := by
      rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; all_goals omega
    have eB : 2 ^ (7 * (p + k + 1) + 4) = 2 ^ (7 * (k + 1) + 4) * 2 ^ (7 * p) := by
      rw [← Nat.pow_add]; congr 1; all_goals omega
    have f1 : 4 ≤ 2 ^ (2 * (k + 1)) := by
      have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 2 ≤ 2 * (k + 1) by omega)
      simpa using this
    have f2 : 128 ≤ 2 ^ (7 * p) := by
      have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 7 ≤ 7 * p by omega)
      simpa using this
    have g1 : (d + 1) * 2 ^ (5 * (k + 1)) ≤ 2 ^ (7 * p + 4) * 2 ^ (5 * (k + 1)) := Nat.mul_le_mul_right _ hd
    rw [Nat.succ_mul] at g1
    have g2 := Nat.mul_le_mul_left (2 ^ (7 * p + 4) * 2 ^ (5 * (k + 1))) f1
    have g3 := Nat.mul_le_mul_left (2 ^ (7 * (k + 1) + 4)) f2
    have := pow_pos' (5 * (k + 1))
    omega

theorem stop_lt (d T k p : Nat) (hd : d < 2 ^ (7 * p + 4)) (h0 : p = 0 → d = 0)
    (hT : T < 3 * 2 ^ (7 * (k + 1) + 1)) : d * 2 ^ (5 * (k + 1)) + T < 2 ^ (7 * (p + k + 1) + 3) := by
  have eZ : 2 ^ (7 * (p + k + 1) + 3) = 2 ^ (7 * (k + 1) + 1) * 2 ^ (7 * p + 2) := by
    rw [← Nat.pow_add]; congr 1; all_goals omega
  have f0 : 4 ≤ 2 ^ (7 * p + 2) := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 2 ≤ 7 * p + 2 by omega)
    simpa using this
  by_cases hp : p = 0
  · subst hp; rw [h0 rfl, Nat.zero_mul, Nat.zero_add, eZ]
    have := Nat.mul_le_mul_left (2 ^ (7 * (k + 1) + 1)) f0
    omega
  · have eA : 2 ^ (7 * (p + k + 1) + 3) = 2 ^ (7 * p + 4) * 2 ^ (5 * (k + 1)) * 2 ^ (2 * k + 1) := by
      rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; all_goals omega
    have f1 : 2 ≤ 2 ^ (2 * k + 1) := by
      have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 1 ≤ 2 * k + 1 by omega)
      simpa using this
    have f2 : 512 ≤ 2 ^ (7 * p + 2) := by
      have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 9 ≤ 7 * p + 2 by omega)
      simpa using this
    have g1 : (d + 1) * 2 ^ (5 * (k + 1)) ≤ 2 ^ (7 * p + 4) * 2 ^ (5 * (k + 1)) := Nat.mul_le_mul_right _ hd
    rw [Nat.succ_mul] at g1
    have g2 := Nat.mul_le_mul_left (2 ^ (7 * p + 4) * 2 ^ (5 * (k + 1))) f1
    have g3 := Nat.mul_le_mul_left (2 ^ (7 * (k + 1) + 1)) f2
    have := pow_pos' (5 * (k + 1))
    omega

theorem walkAux_lt : ∀ (l : List (Bool × Bool)) (S : Mode) (flag borrow : Bool) (k p d i : Nat) (b : Bool) (δ : Nat),
    walkAux l S flag borrow k p d = some (i, b, δ) → d < 2 ^ (7 * p + 4) → (p = 0 → d = 0) →
    δ < 2 ^ (7 * i + 3)
  | [], _, _, _, _, _, _, _, _, _, h, _, _ => by simp [walkAux] at h
  | x :: rest, S, flag, borrow, k, p, d, i, b, δ, h, hd, h0 => by
    unfold walkAux at h
    simp only at h
    split at h
    · exact walkAux_lt rest _ _ _ _ _ _ _ _ _ h hd h0
    · cases S with
      | O =>
        simp only at h
        split at h
        · split at h
          · simp at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, -, rfl⟩ := h
            exact stop_lt _ _ _ _ hd h0 (termStop_lt _ _)
        · exact walkAux_lt rest _ _ _ _ _ _ _ _ _ h (step_lt _ _ _ _ hd h0 (termO_lt _)) (by omega)
      | Q =>
        simp only at h
        exact walkAux_lt rest _ _ _ _ _ _ _ _ _ h (step_lt _ _ _ _ hd h0 (termQ_lt _ _ _)) (by omega)

/-- **The bound.**  If the walk stops after i pairs (j = 2i + 1 digits), then δ < 2^(7i + 3) = 2^((7j − 1)/2). -/
theorem walk_delta_lt (h : Bool) (pairs : List (Bool × Bool)) (i : Nat) (b : Bool) (δ : Nat)
    (hw : walk h pairs = some (i, b, δ)) : δ < 2 ^ (7 * i + 3) :=
  walkAux_lt _ _ _ _ _ _ _ _ _ _ hw (pow_pos' _) (fun _ => rfl)

/-- **No halt from a short walk.**  A halt needs δ = (N >> j) + 1.  If the counter has L digits, N >> j ≥ 2^(L−1−j);
so when 9j ≤ 2L − 1 (j = 2i + 1 digits read) δ is smaller than N >> j and the rebuild does not halt. -/
theorem no_halt_if_short (h : Bool) (pairs : List (Bool × Bool)) (i : Nat) (b : Bool) (δ R L : Nat)
    (hw : walk h pairs = some (i, b, δ)) (hR : 2 ^ (L - 1 - (2 * i + 1)) ≤ R)
    (hs : 9 * (2 * i + 1) ≤ 2 * L - 1) : δ < R ∧ δ ≠ R + 1 := by
  have h1 := walk_delta_lt h pairs i b δ hw
  have h2 : 2 ^ (7 * i + 3) ≤ 2 ^ (L - 1 - (2 * i + 1)) := Nat.pow_le_pow_right (by decide) (by omega)
  omega

end H49767Delta
