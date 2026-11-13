import TM

/-!
# Tools for chaining rules (shared by the G01 second-pass machines; a copy sits in each machine's `lean/`)

* `cross_r2`, `cross_l2`: crossing a repeated word with words carried on both sides of the head
  (generalizes `TM.cross_r` / `TM.cross_l`, where nothing sits between the head and the repeat);
* `iter`: `k` rounds of a rule `P (x+1) i → P x (i+1)` whose round costs `f x i` steps, with `iterT_lin` the
  closed form of the total when the cost is linear;
* `bridge`, `bridge_l`, `bridge_r`: chaining two runs whose meeting configurations are equal but written
  differently (the equation is proved by `simp +arith`).
-/

namespace TM

variable {Q : Type} (δ : Q → Bool → Option (Bool × Dir × Q))

/-- `L u q> x w^k R` becomes `L v^k u q> x R` when one copy does (left words nearest first). -/
theorem cross_r2 {s : Nat} {q : Q} {u x w v : List Bool}
    (h : ∀ L R : Tape, steps δ s ⟨app u L, app x (app w R), q⟩ = some ⟨app u (app v L), app x R, q⟩) (k : Nat) :
    ∀ L R : Tape, steps δ (k * s) ⟨app u L, app x (rep k w R), q⟩ = some ⟨app u (rep k v L), app x R, q⟩ := by
  induction k with
  | zero => intro L R; simp
  | succ k ih =>
    intro L R
    have e : (k + 1) * s = s + k * s := by rw [Nat.succ_mul, Nat.add_comm]
    rw [e]
    have h₂ := ih (app v L) R
    rw [rep_app_comm] at h₂
    exact steps_seq δ (h L (rep k w R)) h₂

/-- `L x w^k q> u R` becomes `L x q> u v^k R` when one copy does (left words nearest first). -/
theorem cross_l2 {s : Nat} {q : Q} {u x w v : List Bool}
    (h : ∀ L R : Tape, steps δ s ⟨app x (app w L), app u R, q⟩ = some ⟨app x L, app u (app v R), q⟩) (k : Nat) :
    ∀ L R : Tape, steps δ (k * s) ⟨app x (rep k w L), app u R, q⟩ = some ⟨app x L, app u (rep k v R), q⟩ := by
  induction k with
  | zero => intro L R; simp
  | succ k ih =>
    intro L R
    have e : (k + 1) * s = s + k * s := by rw [Nat.succ_mul, Nat.add_comm]
    rw [e]
    have h₂ := ih L (app v R)
    rw [rep_app_comm] at h₂
    exact steps_seq δ (h (rep k w L) R) h₂

/-- The steps of `k` rounds from `P (x + k) i`, round `j` (from 0) costing `f (x + k - 1 - j) (i + j)`. -/
def iterT (f : Nat → Nat → Nat) : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | k + 1, x, i => f (x + k) i + iterT f k x (i + 1)

/-- Iterating a rule `P (x+1) i → P x (i+1)`: `k` rounds. -/
theorem iter {P : Nat → Nat → Cfg Q} {f : Nat → Nat → Nat}
    (h : ∀ x i, steps δ (f x i) (P (x + 1) i) = some (P x (i + 1))) :
    ∀ k x i, steps δ (iterT f k x i) (P (x + k) i) = some (P x (i + k)) := by
  intro k
  induction k with
  | zero => intro x i; rfl
  | succ k ih =>
    intro x i
    have h₂ := ih x (i + 1)
    rw [show i + 1 + k = i + (k + 1) by omega] at h₂
    exact steps_seq δ (h (x + k) i) h₂

/-- Twice `k (k-1) / 2` is `k (k-1)`. -/
theorem tri2 (k : Nat) : 2 * (k * (k - 1) / 2) = k * (k - 1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    cases k with
    | zero => rfl
    | succ k =>
      have e : (k + 2) * (k + 1) = k * (k + 1) + 2 * (k + 1) := by
        simp only [Nat.add_mul]
      rw [show k + 1 + 1 - 1 = k + 1 by omega, show k + 1 + 1 = k + 2 by omega, e]
      rw [show k + 1 - 1 = k by omega] at ih
      have e2 : (k + 1) * k = k * (k + 1) := Nat.mul_comm _ _
      rw [e2] at ih
      omega

theorem tri_succ (k : Nat) : (k + 1) * (k + 1 - 1) / 2 = k * (k - 1) / 2 + k := by
  have t1 := tri2 k
  have t2 := tri2 (k + 1)
  have e : (k + 1) * (k + 1 - 1) = k * (k - 1) + 2 * k := by
    cases k with
    | zero => rfl
    | succ k => simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one, Nat.add_sub_cancel]; omega
  omega

/-- A round cost `a + b x + c i` summed in closed form. -/
theorem iterT_lin (a b c : Nat) : ∀ k x i, iterT (fun x i => a + b * x + c * i) k x i =
    k * a + b * (k * x + k * (k - 1) / 2) + c * (k * i + k * (k - 1) / 2) := by
  intro k
  induction k with
  | zero => intro x i; simp [iterT]
  | succ k ih =>
    intro x i
    simp only [iterT, ih, tri_succ]
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one, Nat.add_assoc]
    omega

/-- Chaining two runs that meet at configurations proved equal. -/
theorem bridge {a b : Nat} {c d d' e : Cfg Q} (h₁ : steps δ a c = some d) (hd : d = d')
    (h₂ : steps δ b d' = some e) : steps δ (a + b) c = some e := by
  subst hd; exact steps_seq δ h₁ h₂

/-- A run restated with an equal start and end. -/
theorem bridge_lr {a : Nat} {c c' d d' : Cfg Q} (hc : c' = c) (h : steps δ a c = some d) (hd : d = d') :
    steps δ a c' = some d' := by
  subst hc; subst hd; exact h

/-- Merging two repeats of one word. -/
theorem rep_merge (a b c : Nat) (w : List Bool) (X : Tape) (h : a + b = c) : rep a w (rep b w X) = rep c w X := by
  rw [← h, rep_add]

/-- A repeat of a word of 0s on blank tape is blank tape. -/
theorem rep_zeros_blank (n : Nat) (w : List Bool) (h : app w blank = blank) : rep n w blank = blank := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rep_succ, ih, h]

/-- A word repeated `k` times. -/
def pw : Nat → List Bool → List Bool
  | 0, _ => []
  | k + 1, u => u ++ pw k u

theorem app_pw (k : Nat) (u : List Bool) (Y : Tape) : app (pw k u) Y = rep k u Y := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [pw, rep_succ]; rw [← app_app, ih]

/-- Regrouping a repeat of a repeated word: `(u^k)^n = u^(kn)`. -/
theorem rep_pw (n k m : Nat) (u : List Bool) (X : Tape) (h : k * n = m) : rep n (pw k u) X = rep m u X := by
  subst h
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [rep_succ, ih, app_pw, Nat.mul_succ, Nat.add_comm, rep_add]

end TM
