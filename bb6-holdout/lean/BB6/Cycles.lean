import BB6.Basic

/-!
# The three cycle lemmas

Each one says that a short cycle of the machine crosses a repeated word without ever reading the tape beyond it,
for every number of repetitions.  They are the only induction the mark rules need (`symtm.py`, `prove_cycles`).

* `pass`:  `E> (01)^k R` becomes `(01)^k E> R` in 2k steps (cycle E0 F1).
* `shift`: `A> (01)^k R` becomes `(10)^k A> R` in 2k steps (cycle A0 B1).
* `carry`: `(10)^k A> 1 1 R` becomes `A> 1 1 (10)^k R` in 4k steps (cycle A1 E1 B0 C0).

On the left stream (nearest cell first) a written word is reversed, so written `(01)^k` on the left is
`rep k [true, false]` and written `(10)^k` on the left is `rep k [false, true]`.
-/

namespace BB6

/-- A repeat absorbs a copy of its word written out in front of its tail. -/
theorem rep_cons2 (k : Nat) (x y : Bool) (s : Tape) :
    rep k [x, y] (cons x (cons y s)) = rep (k + 1) [x, y] s :=
  rep_app_comm k [x, y] s

/-- Re-bracketing: `x (y x)^n s = (x y)^n x s`. -/
theorem rep_shift' (x y : Bool) (n : Nat) (s : Tape) :
    cons x (rep n [y, x] s) = rep n [x, y] (cons x s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    show cons x (cons y (cons x (rep n [y, x] s))) = cons x (cons y (rep n [x, y] (cons x s)))
    rw [ih]

theorem pass (k : Nat) : ∀ (L R : Tape),
    steps (2 * k) ⟨L, rep k [false, true] R, .E⟩ = some ⟨rep k [true, false] L, R, .E⟩ := by
  induction k with
  | zero => intro L R; rfl
  | succ k ih =>
    intro L R
    have e : 2 * (k + 1) = 2 + 2 * k := by omega
    rw [e]
    have h₁ : steps 2 ⟨L, rep (k + 1) [false, true] R, .E⟩
        = some ⟨cons true (cons false L), rep k [false, true] R, .E⟩ := rfl
    have h₂ := ih (cons true (cons false L)) R
    rw [rep_cons2] at h₂
    exact steps_seq h₁ h₂

theorem shift (k : Nat) : ∀ (L R : Tape),
    steps (2 * k) ⟨L, rep k [false, true] R, .A⟩ = some ⟨rep k [false, true] L, R, .A⟩ := by
  induction k with
  | zero => intro L R; rfl
  | succ k ih =>
    intro L R
    have e : 2 * (k + 1) = 2 + 2 * k := by omega
    rw [e]
    have h₁ : steps 2 ⟨L, rep (k + 1) [false, true] R, .A⟩
        = some ⟨cons false (cons true L), rep k [false, true] R, .A⟩ := rfl
    have h₂ := ih (cons false (cons true L)) R
    rw [rep_cons2] at h₂
    exact steps_seq h₁ h₂

theorem carry (k : Nat) : ∀ (L R : Tape),
    steps (4 * k) ⟨rep k [false, true] L, cons true (cons true R), .A⟩
      = some ⟨L, cons true (cons true (rep k [true, false] R)), .A⟩ := by
  induction k with
  | zero => intro L R; rfl
  | succ k ih =>
    intro L R
    have e : 4 * (k + 1) = 4 + 4 * k := by omega
    rw [e]
    have h₁ : steps 4 ⟨rep (k + 1) [false, true] L, cons true (cons true R), .A⟩
        = some ⟨rep k [false, true] L, cons true (cons true (cons true (cons false R))), .A⟩ := rfl
    have h₂ := ih L (cons true (cons false R))
    rw [rep_cons2] at h₂
    exact steps_seq h₁ h₂

end BB6
