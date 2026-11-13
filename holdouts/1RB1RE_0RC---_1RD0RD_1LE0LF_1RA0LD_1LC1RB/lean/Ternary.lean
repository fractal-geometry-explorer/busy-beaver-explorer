import Machine

/-! # The ternary step of 1RB1RE_0RC---_1RD0RD_1LE0LF_1RA0LD_1LC1RB

At the left end of the tape, with blank tape to the left, a block of n pairs `01` followed by pairs `10`
triples: `E> (01)^n (10)^(y + 2n - 1) 1` becomes `E> (01)^(3n) (10)^y 1` (`ternary`, for every n ≥ 2).

The four pieces `t_intro`, `t_init`, `t_round`, `t_fin` are written by `bbtools.symtm.prove`; the induction over
the rounds (`rounds`) and the assembly are by hand.  E first turns the n pairs into 2n ones (`t_intro`); each
round then eats two of those 1s and two pairs `10` and writes three pairs `01` (`t_init` for the first, which
eats four, `t_round` for the others); at the end `t_fin` turns the leftover `1 1` into two more pairs. -/

namespace H8002

open TM

/-- At the left end, E turns the pairs `01` into a block of 1s. -/
theorem t_intro (n : Nat) (R : Tape) :
    steps (2 * n) ⟨blank, rep (n) [false, true] (R), .E⟩ = some ⟨rep (n) [true, true] (blank), R, .E⟩ := by
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [false, true] R, .E⟩ = some ⟨app [] (app [true, true] L), R, .E⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 2) ⟨blank, rep (n) [false, true] (R), .E⟩ = some ⟨rep (n) [true, true] (blank), R, .E⟩ :=
    cross_r trans c0 (n) (blank) (R)
  exact steps_congr trans (a := (n) * 2) (by omega) (h0)


/-- The first round eats four 1s. -/
theorem t_init (y : Nat) (L R : Tape) :
    steps (38) ⟨cons true (cons true (cons true (cons true (L)))), rep (y + 3) [true, false] (cons true (R)), .E⟩ = some ⟨L, cons true (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (rep (y) [true, false] (cons true (R)))))))))))), .E⟩ := by
  have h0 : steps 38 ⟨cons true (cons true (cons true (cons true (L)))), rep (y + 3) [true, false] (cons true (R)), .E⟩ = some ⟨L, cons true (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (rep (y) [true, false] (cons true (R)))))))))))), .E⟩ := rfl
  exact steps_congr trans (a := 38) (by omega) (h0)


/-- One round: two 1s of the block and two pairs `10` become three pairs `01`. -/
theorem t_round (k y : Nat) (L R : Tape) :
    steps (6 * k + 42) ⟨cons true (cons true (L)), cons true (cons true (cons false (cons true (cons false (rep (k) [true, false] (cons true (cons false (cons true (rep (y + 2) [true, false] (cons true (R))))))))))), .E⟩ = some ⟨L, cons true (cons true (cons false (cons true (cons false (cons true (cons false (rep (k) [true, false] (cons true (cons false (cons true (cons false (cons true (cons false (cons true (rep (y) [true, false] (cons true (R))))))))))))))))), .E⟩ := by
  have h0 : steps 13 ⟨cons true (cons true (L)), cons true (cons true (cons false (cons true (cons false (rep (k) [true, false] (cons true (cons false (cons true (rep (y + 2) [true, false] (cons true (R))))))))))), .E⟩ = some ⟨cons true (cons false (cons true (cons false (cons true (cons false (cons true (L))))))), rep (k) [true, false] (cons true (cons false (cons true (rep (y + 2) [true, false] (cons true (R)))))), .D⟩ := rfl
  have c1 : ∀ L R : Tape, steps 4 ⟨app [true] L, app [true, false] R, .D⟩ = some ⟨app [true] (app [false, true] L), R, .D⟩ := fun _ _ => rfl
  have h1 : steps ((k) * 4) ⟨cons true (cons false (cons true (cons false (cons true (cons false (cons true (L))))))), rep (k) [true, false] (cons true (cons false (cons true (rep (y + 2) [true, false] (cons true (R)))))), .D⟩ = some ⟨cons true (rep (k) [false, true] (cons false (cons true (cons false (cons true (cons false (cons true (L)))))))), cons true (cons false (cons true (rep (y + 2) [true, false] (cons true (R))))), .D⟩ :=
    cross_r trans c1 (k) (cons false (cons true (cons false (cons true (cons false (cons true (L))))))) (cons true (cons false (cons true (rep (y + 2) [true, false] (cons true (R))))))
  have h2 : steps 23 ⟨cons true (rep (k) [false, true] (cons false (cons true (cons false (cons true (cons false (cons true (L)))))))), cons true (cons false (cons true (rep (y + 2) [true, false] (cons true (R))))), .D⟩ = some ⟨rep (k) [false, true] (cons false (cons true (cons false (cons true (cons false (cons true (L))))))), cons true (cons true (cons false (cons true (cons false (cons true (cons false (cons true (rep (y) [true, false] (cons true (R)))))))))), .E⟩ := rfl
  have c3 : ∀ L R : Tape, steps 2 ⟨app [false, true] L, app [true] R, .E⟩ = some ⟨L, app [true] (app [true, false] R), .E⟩ := fun _ _ => rfl
  have h3 : steps ((k) * 2) ⟨rep (k) [false, true] (cons false (cons true (cons false (cons true (cons false (cons true (L))))))), cons true (cons true (cons false (cons true (cons false (cons true (cons false (cons true (rep (y) [true, false] (cons true (R)))))))))), .E⟩ = some ⟨cons false (cons true (cons false (cons true (cons false (cons true (L)))))), cons true (rep (k) [true, false] (cons true (cons false (cons true (cons false (cons true (cons false (cons true (rep (y) [true, false] (cons true (R))))))))))), .E⟩ :=
    cross_l trans c3 (k) (cons false (cons true (cons false (cons true (cons false (cons true (L))))))) (cons true (cons false (cons true (cons false (cons true (cons false (cons true (rep (y) [true, false] (cons true (R))))))))))
  have h4 : steps 6 ⟨cons false (cons true (cons false (cons true (cons false (cons true (L)))))), cons true (rep (k) [true, false] (cons true (cons false (cons true (cons false (cons true (cons false (cons true (rep (y) [true, false] (cons true (R))))))))))), .E⟩ = some ⟨L, cons true (cons true (cons false (cons true (cons false (cons true (cons false (rep (k) [true, false] (cons true (cons false (cons true (cons false (cons true (cons false (cons true (rep (y) [true, false] (cons true (R))))))))))))))))), .E⟩ := rfl
  exact steps_congr trans (a := 13 + ((k) * 4 + (23 + ((k) * 2 + (6))))) (by omega) (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (h4)))))


/-- At the left end, `E> 1 1` becomes `E> 0 1 0 1`. -/
theorem t_fin (R : Tape) :
    steps (2) ⟨blank, cons true (cons true (R)), .E⟩ = some ⟨blank, cons false (cons true (cons false (cons true (R)))), .E⟩ := by
  have h0 : steps 2 ⟨blank, cons true (cons true (R)), .E⟩ = some ⟨blank, cons false (cons true (cons false (cons true (R)))), .E⟩ := rfl
  exact steps_congr trans (a := 2) (by omega) (h0)


/-- The right tape during the rounds: `1 1 0 1 0 (10)^k 1 0 1 (10)^y 1 R`, i.e. `1 1 (01)^(k+3) (10)^y 1 R`. -/
def W (k y : Nat) (R : Tape) : Tape :=
  cons true (cons true (cons false (cons true (cons false (rep k [true, false]
    (cons true (cons false (cons true (rep y [true, false] (cons true R))))))))))

/-- `t_round` with its end written as `W (k + 3) y R`. -/
theorem round_W (k y : Nat) (L R : Tape) :
    steps (6 * k + 42) ⟨cons true (cons true L), W k (y + 2) R, .E⟩ = some ⟨L, W (k + 3) y R, .E⟩ := by
  have h := t_round k y L R
  have e : rep k [true, false] (cons true (cons false (cons true (cons false (cons true (cons false
      (cons true (rep y [true, false] (cons true R)))))))))
      = rep (k + 2) [true, false] (cons true (cons false (cons true (rep y [true, false] (cons true R))))) := by
    rw [← rep_app_comm, ← rep_app_comm]; rfl
  rw [e] at h
  exact h

/-- m rounds: m pairs `1 1` on the left are spent, k grows by 3m, y shrinks by 2m. -/
theorem rounds (m : Nat) : ∀ (k y : Nat) (L R : Tape),
    ∃ t, steps t ⟨rep m [true, true] L, W k (y + 2 * m) R, .E⟩ = some ⟨L, W (k + 3 * m) y R, .E⟩ := by
  induction m with
  | zero => intro k y L R; exact ⟨0, by simp [TM.steps]⟩
  | succ m ih =>
    intro k y L R
    have h1 := round_W k (y + 2 * m) (rep m [true, true] L) R
    obtain ⟨t, h2⟩ := ih (k + 3) y L R
    have e1 : y + 2 * (m + 1) = y + 2 * m + 2 := by omega
    have e2 : k + 3 + 3 * m = k + 3 * (m + 1) := by omega
    rw [e2] at h2
    rw [e1]
    exact ⟨_, steps_seq trans h1 h2⟩

/-- `0 (10)^k 1 Z = (01)^(k+1) Z`. -/
theorem shift01 (k : Nat) (Z : Tape) :
    cons false (rep k [true, false] (cons true Z)) = rep (k + 1) [false, true] Z := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show cons false (cons true (cons false (rep k [true, false] (cons true Z)))) = _
    rw [ih]; rfl

/-- **The ternary step.** At the left end, `E> (01)^n (10)^(y + 2n - 1) 1 R` reaches `E> (01)^(3n) (10)^y 1 R`. -/
theorem ternary (n y : Nat) (R : Tape) (hn : 2 ≤ n) :
    ∃ t, steps t ⟨blank, rep n [false, true] (rep (y + 2 * n - 1) [true, false] (cons true R)), .E⟩ =
      some ⟨blank, rep (3 * n) [false, true] (rep y [true, false] (cons true R)), .E⟩ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have h1 := t_intro (m + 2) (rep (y + 2 * (m + 2) - 1) [true, false] (cons true R))
  have e1 : y + 2 * (m + 2) - 1 = (y + 2 * m) + 3 := by omega
  rw [e1] at h1
  have h2 := t_init (y + 2 * m) (rep m [true, true] blank) R
  obtain ⟨t3, h3⟩ := rounds m 1 y blank R
  have h4 := t_fin (cons false (cons true (cons false (rep (1 + 3 * m) [true, false]
    (cons true (cons false (cons true (rep y [true, false] (cons true R)))))))))
  have e4 : ∀ Z : Tape, cons false (cons true (cons false (cons true (cons false (cons true (cons false
      (rep (1 + 3 * m) [true, false] (cons true (cons false (cons true Z))))))))))
      = rep (3 * (m + 2)) [false, true] Z := by
    intro Z
    have aux : ∀ (k : Nat) (Z : Tape), rep k [false, true] (cons false (cons true Z)) = rep (k + 1) [false, true] Z :=
      fun k Z => rep_app_comm k [false, true] Z
    rw [shift01, aux]
    have : 3 * (m + 2) = (1 + 3 * m + 1 + 1) + 3 := by omega
    rw [this]; rfl
  rw [e4 (rep y [true, false] (cons true R))] at h4
  exact ⟨_, steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 h4))⟩

end H8002
