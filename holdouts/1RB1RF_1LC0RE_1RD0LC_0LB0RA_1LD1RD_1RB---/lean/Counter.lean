import Machine

/-! # The ternary counter of 1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RB---

Write `x = 1110` and `a = 10`.  Most of the time the tape is a *counter configuration*

    C> 0 10 x^n0 [1 a^d1 x^n1] [1 a^d2 x^n2] ... [1 a^dk x^nk] 1 0^∞      (blank tape to the left)

with digits `d_i ∈ {0,1,2}`.  One *bounce* (C sweeps right to the first group with a nonzero digit, then the head
zig-zags back to the left end) is a ternary decrement: the first nonzero digit drops by one, the zero digits below
it become 2, each group passed loses one `x`, and `n0` gains one `x` (`bounce`).

The six pieces are written by `bbtools.symtm.prove` (`py/counter.py`); the definitions and the inductions over the
groups passed are by hand. -/

namespace H40361

open TM

theorem p_start (n : Nat) (R : Tape) :
    steps (4 * n + 4) ⟨blank, cons false (cons true (cons false (rep (n) [true, true, true, false] (cons true (R))))), .C⟩ = some ⟨cons false (cons true (cons false (rep (n) [true, false, true, false] (cons true (blank))))), R, .E⟩ := by
  have hn : 1 + (0 + ((n) * 4 + (3))) = 4 * n + 4 := by omega
  have h0 : steps 1 ⟨blank, cons false (cons true (cons false (rep (n) [true, true, true, false] (cons true (R))))), .C⟩ = some ⟨cons true (blank), cons true (cons false (rep (n) [true, true, true, false] (cons true (R)))), .D⟩ := rfl
  have h1 : steps 0 ⟨cons true (blank), cons true (cons false (rep (n) [true, true, true, false] (cons true (R)))), .D⟩ = some ⟨cons true (blank), rep (n) [true, false, true, true] (cons true (cons false (cons true (R)))), .D⟩ := by
    simp only [steps_zero, show cons true (cons false (rep (n) [true, true, true, false] (cons true (R)))) = rep (n) [true, false, true, true] (cons true (cons false (cons true (R)))) from
      rep_rotate (n) [true, false] [true, true, true, false] [true, false, true, true] rfl (cons true (R))]
  have c2 : ∀ L R : Tape, steps 4 ⟨app [] L, app [true, false, true, true] R, .D⟩ = some ⟨app [] (app [true, false, true, false] L), R, .D⟩ := fun _ _ => rfl
  have h2 : steps ((n) * 4) ⟨cons true (blank), rep (n) [true, false, true, true] (cons true (cons false (cons true (R)))), .D⟩ = some ⟨rep (n) [true, false, true, false] (cons true (blank)), cons true (cons false (cons true (R))), .D⟩ :=
    cross_r trans c2 (n) (cons true (blank)) (cons true (cons false (cons true (R))))
  have h3 : steps 3 ⟨rep (n) [true, false, true, false] (cons true (blank)), cons true (cons false (cons true (R))), .D⟩ = some ⟨cons false (cons true (cons false (rep (n) [true, false, true, false] (cons true (blank))))), R, .E⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (h3))))

theorem p_pass (m : Nat) (L R : Tape) :
    steps (4 * m + 5) ⟨L, rep (m + 1) [true, true, true, false] (cons true (R)), .E⟩ = some ⟨cons false (rep (m) [true, false, true, false] (cons true (cons true (cons false (cons true (L)))))), R, .E⟩ := by
  have hn : 4 + ((m) * 4 + (1)) = 4 * m + 5 := by omega
  have h0 : steps 4 ⟨L, rep (m + 1) [true, true, true, false] (cons true (R)), .E⟩ = some ⟨cons true (cons true (cons false (cons true (L)))), rep (m) [true, true, true, false] (cons true (R)), .B⟩ := rfl
  have c1 : ∀ L R : Tape, steps 4 ⟨app [] L, app [true, true, true, false] R, .B⟩ = some ⟨app [] (app [true, false, true, false] L), R, .B⟩ := fun _ _ => rfl
  have h1 : steps ((m) * 4) ⟨cons true (cons true (cons false (cons true (L)))), rep (m) [true, true, true, false] (cons true (R)), .B⟩ = some ⟨rep (m) [true, false, true, false] (cons true (cons true (cons false (cons true (L))))), cons true (R), .B⟩ :=
    cross_r trans c1 (m) (cons true (cons true (cons false (cons true (L))))) (cons true (R))
  have h2 : steps 1 ⟨rep (m) [true, false, true, false] (cons true (cons true (cons false (cons true (L))))), cons true (R), .B⟩ = some ⟨cons false (rep (m) [true, false, true, false] (cons true (cons true (cons false (cons true (L)))))), R, .E⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (h2)))

theorem p_turn1 (L R : Tape) :
    steps (4) ⟨L, cons true (cons false (R)), .E⟩ = some ⟨L, cons false (cons true (R)), .D⟩ := by
  have hn : 4 = 4 := by omega
  have h0 : steps 4 ⟨L, cons true (cons false (R)), .E⟩ = some ⟨L, cons false (cons true (R)), .D⟩ := rfl
  exact steps_congr trans hn (h0)

theorem p_turn2 (L R : Tape) :
    steps (4) ⟨L, cons true (cons false (cons true (cons false (R)))), .E⟩ = some ⟨L, cons false (cons true (cons true (cons false (R)))), .D⟩ := by
  have hn : 4 = 4 := by omega
  have h0 : steps 4 ⟨L, cons true (cons false (cons true (cons false (R)))), .E⟩ = some ⟨L, cons false (cons true (cons true (cons false (R)))), .D⟩ := rfl
  exact steps_congr trans hn (h0)

theorem p_ret (m : Nat) (L R : Tape) :
    steps (10 * m + 11) ⟨cons false (rep (m) [true, false, true, false] (cons true (cons true (cons false (cons true (L)))))), cons false (cons true (R)), .D⟩ = some ⟨L, cons false (cons true (cons true (cons false (cons true (cons false (rep (m) [true, true, true, false] (cons true (R)))))))), .D⟩ := by
  have hn : 0 + ((m) * 10 + (11)) = 10 * m + 11 := by omega
  have h0 : steps 0 ⟨cons false (rep (m) [true, false, true, false] (cons true (cons true (cons false (cons true (L)))))), cons false (cons true (R)), .D⟩ = some ⟨rep (m) [false, true, false, true] (cons false (cons true (cons true (cons false (cons true (L)))))), cons false (cons true (R)), .D⟩ := by
    simp only [steps_zero, show cons false (rep (m) [true, false, true, false] (cons true (cons true (cons false (cons true (L)))))) = rep (m) [false, true, false, true] (cons false (cons true (cons true (cons false (cons true (L)))))) from
      rep_rotate (m) [false] [true, false, true, false] [false, true, false, true] rfl (cons true (cons true (cons false (cons true (L)))))]
  have c1 : ∀ L R : Tape, steps 10 ⟨app [false, true, false, true] L, app [false] R, .D⟩ = some ⟨L, app [false] (app [true, true, true, false] R), .D⟩ := fun _ _ => rfl
  have h1 : steps ((m) * 10) ⟨rep (m) [false, true, false, true] (cons false (cons true (cons true (cons false (cons true (L)))))), cons false (cons true (R)), .D⟩ = some ⟨cons false (cons true (cons true (cons false (cons true (L))))), cons false (rep (m) [true, true, true, false] (cons true (R))), .D⟩ :=
    cross_l trans c1 (m) (cons false (cons true (cons true (cons false (cons true (L)))))) (cons true (R))
  have h2 : steps 11 ⟨cons false (cons true (cons true (cons false (cons true (L))))), cons false (rep (m) [true, true, true, false] (cons true (R))), .D⟩ = some ⟨L, cons false (cons true (cons true (cons false (cons true (cons false (rep (m) [true, true, true, false] (cons true (R)))))))), .D⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (h2)))

theorem p_end (n : Nat) (R : Tape) :
    steps (10 * n + 12) ⟨cons false (cons true (cons false (rep (n) [true, false, true, false] (cons true (blank))))), cons false (cons true (R)), .D⟩ = some ⟨blank, cons false (cons true (cons false (cons true (cons true (cons true (cons false (rep (n) [true, true, true, false] (cons true (R))))))))), .C⟩ := by
  have hn : 0 + ((n) * 10 + (12)) = 10 * n + 12 := by omega
  have h0 : steps 0 ⟨cons false (cons true (cons false (rep (n) [true, false, true, false] (cons true (blank))))), cons false (cons true (R)), .D⟩ = some ⟨rep (n) [false, true, false, true] (cons false (cons true (cons false (cons true (blank))))), cons false (cons true (R)), .D⟩ := by
    simp only [steps_zero, show cons false (cons true (cons false (rep (n) [true, false, true, false] (cons true (blank))))) = rep (n) [false, true, false, true] (cons false (cons true (cons false (cons true (blank))))) from
      rep_rotate (n) [false, true, false] [true, false, true, false] [false, true, false, true] rfl (cons true (blank))]
  have c1 : ∀ L R : Tape, steps 10 ⟨app [false, true, false, true] L, app [false] R, .D⟩ = some ⟨L, app [false] (app [true, true, true, false] R), .D⟩ := fun _ _ => rfl
  have h1 : steps ((n) * 10) ⟨rep (n) [false, true, false, true] (cons false (cons true (cons false (cons true (blank))))), cons false (cons true (R)), .D⟩ = some ⟨cons false (cons true (cons false (cons true (blank)))), cons false (rep (n) [true, true, true, false] (cons true (R))), .D⟩ :=
    cross_l trans c1 (n) (cons false (cons true (cons false (cons true (blank))))) (cons true (R))
  have h2 : steps 12 ⟨cons false (cons true (cons false (cons true (blank)))), cons false (rep (n) [true, true, true, false] (cons true (R))), .D⟩ = some ⟨blank, cons false (cons true (cons false (cons true (cons true (cons true (cons false (rep (n) [true, true, true, false] (cons true (R))))))))), .C⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (h2)))


/-- `x = 1110`. -/
abbrev xw : List Bool := [true, true, true, false]
/-- `a = 10`. -/
abbrev aw : List Bool := [true, false]

/-- A group `1 a^d x^n` in front of `R`. -/
def grp (g : Nat × Nat) (R : Tape) : Tape := cons true (rep g.1 aw (rep g.2 xw R))

/-- A list of groups in front of `R`. -/
def grps : List (Nat × Nat) → Tape → Tape
  | [], R => R
  | g :: gs, R => grp g (grps gs R)

/-- The right half of a counter configuration: `0 10 x^n0 G R`. -/
def ctape (n0 : Nat) (G : List (Nat × Nat)) (R : Tape) : Tape :=
  cons false (cons true (cons false (rep n0 xw (grps G R))))

/-- A counter configuration: head in C at the left end, blank to the left, `0 10 x^n0 G 1 0^∞` to the right. -/
def ccfg (n0 : Nat) (G : List (Nat × Nat)) : Config := ⟨blank, ctape n0 G (cons true blank), .C⟩

/-- The groups passed by the borrow, before: `x^(m+1) 1` each (the `1` is the next group's separator). -/
def pathR : List Nat → Tape → Tape
  | [], R => R
  | m :: ms, R => rep (m + 1) xw (cons true (pathR ms R))

/-- The groups passed, after the return: `a^2 x^m 1` each. -/
def pathR2 : List Nat → Tape → Tape
  | [], R => R
  | m :: ms, R => rep 2 aw (rep m xw (cons true (pathR2 ms R)))

/-- The left tape left behind by `p_pass` over one group: `1011 (0101)^m 0` (written left to right). -/
def lp (m : Nat) (L : Tape) : Tape :=
  cons false (rep m [true, false, true, false] (cons true (cons true (cons false (cons true L)))))

/-- The left tape after passing the groups `ms` (the first group deepest). -/
def pathL : List Nat → Tape → Tape
  | [], L => L
  | m :: ms, L => pathL ms (lp m L)

/-- E passes any number of groups with digit 0. -/
theorem pass_all (ms : List Nat) : ∀ (L R : Tape),
    ∃ t, steps t ⟨L, pathR ms R, .E⟩ = some ⟨pathL ms L, R, .E⟩ := by
  induction ms with
  | nil => intro L R; exact ⟨0, rfl⟩
  | cons m ms ih =>
    intro L R
    obtain ⟨t, h⟩ := ih (lp m L) R
    exact ⟨_, steps_seq trans (p_pass m L (pathR ms R)) h⟩

/-- D returns over the groups passed, turning each `x^(m+1) 1` into `a^2 x^m 1`. -/
theorem ret_all (ms : List Nat) : ∀ (L R : Tape),
    ∃ t, steps t ⟨pathL ms L, cons false (cons true R), .D⟩ =
      some ⟨L, cons false (cons true (pathR2 ms R)), .D⟩ := by
  induction ms with
  | nil => intro L R; exact ⟨0, rfl⟩
  | cons m ms ih =>
    intro L R
    obtain ⟨t, h⟩ := ih (lp m L) R
    have h2 := p_ret m L (pathR2 ms R)
    exact ⟨_, steps_seq trans h h2⟩

/-- The groups the borrow passes, then the group whose digit it decrements. -/
theorem grps_path (ms : List Nat) (d n : Nat) (rest : List (Nat × Nat)) (R : Tape) :
    grps (ms.map (fun m => (0, m + 1)) ++ (d, n) :: rest) R =
      cons true (pathR ms (rep d aw (rep n xw (grps rest R)))) := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    show cons true (rep 0 aw (rep (m + 1) xw (grps (ms.map (fun m => (0, m + 1)) ++ (d, n) :: rest) R))) = _
    rw [ih]; rfl

/-- The same groups after the bounce: digit 2, one `x` fewer. -/
theorem grps_path2 (ms : List Nat) (d n : Nat) (rest : List (Nat × Nat)) (R : Tape) :
    grps (ms.map (fun m => (2, m)) ++ (d, n) :: rest) R =
      cons true (pathR2 ms (rep d aw (rep n xw (grps rest R)))) := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    show cons true (rep 2 aw (rep m xw (grps (ms.map (fun m => (2, m)) ++ (d, n) :: rest) R))) = _
    rw [ih]; rfl

/-- The turn at the decremented digit: `E> a^(e+1)` becomes `D> 0 1 a^e`, for e = 0, 1. -/
theorem turn (e : Nat) (he : e ≤ 1) (L Y : Tape) :
    steps 4 ⟨L, rep (e + 1) aw Y, .E⟩ = some ⟨L, cons false (cons true (rep e aw Y)), .D⟩ := by
  rcases (by omega : e = 0 ∨ e = 1) with rfl | rfl
  · exact p_turn1 L Y
  · exact p_turn2 L Y

/-- **One bounce is a ternary decrement.**  The borrow passes the groups `(0, m+1)` for `m ∈ ms` (each loses an
`x` and gets digit 2), the next digit `e + 1` drops to `e`, and `n0` gains an `x`.  Any tape `F` may follow the
groups. -/
theorem bounce_gen (n0 : Nat) (ms : List Nat) (e n : Nat) (he : e ≤ 1) (rest : List (Nat × Nat)) (F : Tape) :
    ∃ t, 0 < t ∧ steps t ⟨blank, ctape n0 (ms.map (fun m => (0, m + 1)) ++ (e + 1, n) :: rest) F, .C⟩ =
      some ⟨blank, ctape (n0 + 1) (ms.map (fun m => (2, m)) ++ (e, n) :: rest) F, .C⟩ := by
  let Y := rep n xw (grps rest F)
  have h1 := p_start n0 (pathR ms (rep (e + 1) aw Y))
  obtain ⟨t2, h2⟩ := pass_all ms (cons false (cons true (cons false (rep n0 [true, false, true, false]
    (cons true blank))))) (rep (e + 1) aw Y)
  have h3 := turn e he (pathL ms (cons false (cons true (cons false (rep n0 [true, false, true, false]
    (cons true blank)))))) Y
  obtain ⟨t4, h4⟩ := ret_all ms (cons false (cons true (cons false (rep n0 [true, false, true, false]
    (cons true blank))))) (rep e aw Y)
  have h5 := p_end n0 (pathR2 ms (rep e aw Y))
  have e1 : ctape n0 (ms.map (fun m => (0, m + 1)) ++ (e + 1, n) :: rest) F =
      cons false (cons true (cons false (rep n0 xw (cons true (pathR ms (rep (e + 1) aw Y)))))) := by
    unfold ctape; rw [grps_path]
  have e2 : ctape (n0 + 1) (ms.map (fun m => (2, m)) ++ (e, n) :: rest) F =
      cons false (cons true (cons false (cons true (cons true (cons true (cons false (rep n0 xw
        (cons true (pathR2 ms (rep e aw Y)))))))))) := by
    unfold ctape; rw [grps_path2]; rfl
  rw [e1, e2]
  exact ⟨4 * n0 + 4 + (t2 + (4 + (t4 + (10 * n0 + 12)))), by omega,
    steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (steps_seq trans h4 h5)))⟩

theorem p_t1 (L : Tape) :
    steps (4) ⟨L, cons true (blank), .E⟩ = some ⟨L, cons false (cons true (blank)), .D⟩ := by
  have hn : 4 = 4 := by omega
  have h0 : steps 4 ⟨L, cons true (blank), .E⟩ = some ⟨L, cons false (cons true (blank)), .D⟩ := rfl
  exact steps_congr trans hn (h0)

theorem p_t2 (L : Tape) :
    steps (12) ⟨L, cons true (cons true (blank)), .E⟩ = some ⟨L, cons false (cons true (cons true (cons true (blank)))), .D⟩ := by
  have hn : 12 = 12 := by omega
  have h0 : steps 12 ⟨L, cons true (cons true (blank)), .E⟩ = some ⟨L, cons false (cons true (cons true (cons true (blank)))), .D⟩ := rfl
  exact steps_congr trans hn (h0)

theorem p_t3 (L : Tape) :
    steps (14) ⟨L, cons true (cons true (cons true (blank))), .E⟩ = some ⟨L, cons false (cons true (cons true (cons false (cons true (blank))))), .D⟩ := by
  have hn : 14 = 14 := by omega
  have h0 : steps 14 ⟨L, cons true (cons true (cons true (blank))), .E⟩ = some ⟨L, cons false (cons true (cons true (cons false (cons true (blank))))), .D⟩ := rfl
  exact steps_congr trans hn (h0)


/-- E reading `1 1 1 1` halts: E, D and A move right over three 1s and F reads the fourth. -/
theorem p_halt (L R : Tape) :
    steps 3 ⟨L, cons true (cons true (cons true (cons true R))), .E⟩ =
      some ⟨cons true (cons false (cons true L)), cons true R, .F⟩ ∧
    step ⟨cons true (cons false (cons true L)), cons true R, .F⟩ = none := ⟨rfl, rfl⟩

theorem grps_append (A B : List (Nat × Nat)) (F : Tape) : grps (A ++ B) F = grps A (grps B F) := by
  induction A with
  | nil => rfl
  | cons g A ih => show grp g (grps (A ++ B) F) = grp g (grps A (grps B F)); rw [ih]

theorem pathR2_grps (ms : List Nat) (W : Tape) :
    cons true (pathR2 ms W) = grps (ms.map (fun m => (2, m))) (cons true W) := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    show cons true (rep 2 aw (rep m xw (cons true (pathR2 ms W)))) = _
    rw [ih]; rfl

/-- The common part of every bounce: the sweep right over `0 10 x^n0` and the groups `ms`. -/
theorem sweep (n0 : Nat) (ms : List Nat) (W : Tape) :
    ∃ t, 0 < t ∧ steps t ⟨blank, ctape n0 (ms.map (fun m => (0, m + 1))) (cons true W), .C⟩ =
      some ⟨pathL ms (cons false (cons true (cons false (rep n0 [true, false, true, false] (cons true blank))))),
        W, .E⟩ := by
  have e : ctape n0 (ms.map (fun m => (0, m + 1))) (cons true W) =
      cons false (cons true (cons false (rep n0 xw (cons true (pathR ms W))))) := by
    unfold ctape; congr 4
    induction ms with
    | nil => rfl
    | cons m ms ih =>
      show cons true (rep 0 aw (rep (m + 1) xw (grps (ms.map (fun m => (0, m + 1))) (cons true W)))) = _
      rw [ih]; rfl
  rw [e]
  obtain ⟨t2, h2⟩ := pass_all ms (cons false (cons true (cons false (rep n0 [true, false, true, false]
    (cons true blank))))) W
  exact ⟨4 * n0 + 4 + t2, by omega, steps_seq trans (p_start n0 (pathR ms W)) h2⟩

/-- The common part of the way back: from `D> 0 1 W` over the groups `ms` to the left end. -/
theorem sweep_back (n0 : Nat) (ms : List Nat) (W : Tape) :
    ∃ t, steps t ⟨pathL ms (cons false (cons true (cons false (rep n0 [true, false, true, false]
        (cons true blank))))), cons false (cons true W), .D⟩ =
      some ⟨blank, ctape (n0 + 1) (ms.map (fun m => (2, m))) (cons true W), .C⟩ := by
  obtain ⟨t4, h4⟩ := ret_all ms (cons false (cons true (cons false (rep n0 [true, false, true, false]
    (cons true blank))))) W
  have h5 := p_end n0 (pathR2 ms W)
  have e : ctape (n0 + 1) (ms.map (fun m => (2, m))) (cons true W) =
      cons false (cons true (cons false (cons true (cons true (cons true (cons false (rep n0 xw
        (cons true (pathR2 ms W))))))))) := by
    unfold ctape; rw [← pathR2_grps]; rfl
  rw [e]
  exact ⟨_, steps_seq trans h4 h5⟩

/-- **Trailing groups.**  When the borrow passes every group with a digit and reaches `t` empty groups `(0,0)`
at the end: one of them (`t = 1`) is removed, two (`t = 2`) stay, three (`t = 3`) become one group `(1,0)`. -/
theorem bounce_t1 (n0 : Nat) (ms : List Nat) :
    ∃ t, 0 < t ∧ steps t (ccfg n0 (ms.map (fun m => (0, m + 1)) ++ [(0, 0)])) =
      some (ccfg (n0 + 1) (ms.map (fun m => (2, m)))) := by
  obtain ⟨t1, ht1, h1⟩ := sweep n0 ms (cons true blank)
  obtain ⟨t3, h3⟩ := sweep_back n0 ms blank
  have e : ctape n0 (ms.map (fun m => (0, m + 1)) ++ [(0, 0)]) (cons true blank) =
      ctape n0 (ms.map (fun m => (0, m + 1))) (cons true (cons true blank)) := by
    unfold ctape; rw [grps_append]; rfl
  unfold ccfg; rw [e]
  exact ⟨_, by omega, steps_seq trans h1 (steps_seq trans (p_t1 _) h3)⟩

theorem bounce_t2 (n0 : Nat) (ms : List Nat) :
    ∃ t, 0 < t ∧ steps t (ccfg n0 (ms.map (fun m => (0, m + 1)) ++ [(0, 0), (0, 0)])) =
      some (ccfg (n0 + 1) (ms.map (fun m => (2, m)) ++ [(0, 0), (0, 0)])) := by
  obtain ⟨t1, ht1, h1⟩ := sweep n0 ms (cons true (cons true blank))
  obtain ⟨t3, h3⟩ := sweep_back n0 ms (cons true (cons true blank))
  have e : ∀ (k : Nat) (A : List (Nat × Nat)), ctape k (A ++ [(0, 0), (0, 0)]) (cons true blank) =
      ctape k A (cons true (cons true (cons true blank))) := by
    intro k A; unfold ctape; rw [grps_append]; rfl
  unfold ccfg; rw [e n0 (ms.map (fun m => (0, m + 1))), e (n0 + 1) (ms.map (fun m => (2, m)))]
  exact ⟨_, by omega, steps_seq trans h1 (steps_seq trans (p_t2 _) h3)⟩

theorem bounce_t3 (n0 : Nat) (ms : List Nat) :
    ∃ t, 0 < t ∧ steps t (ccfg n0 (ms.map (fun m => (0, m + 1)) ++ [(0, 0), (0, 0), (0, 0)])) =
      some (ccfg (n0 + 1) (ms.map (fun m => (2, m)) ++ [(1, 0)])) := by
  obtain ⟨t1, ht1, h1⟩ := sweep n0 ms (cons true (cons true (cons true blank)))
  obtain ⟨t3, h3⟩ := sweep_back n0 ms (cons true (cons false (cons true blank)))
  have e1 : ctape n0 (ms.map (fun m => (0, m + 1)) ++ [(0, 0), (0, 0), (0, 0)]) (cons true blank) =
      ctape n0 (ms.map (fun m => (0, m + 1))) (cons true (cons true (cons true (cons true blank)))) := by
    unfold ctape; rw [grps_append]; rfl
  have e2 : ctape (n0 + 1) (ms.map (fun m => (2, m)) ++ [(1, 0)]) (cons true blank) =
      ctape (n0 + 1) (ms.map (fun m => (2, m))) (cons true (cons true (cons false (cons true blank)))) := by
    unfold ctape; rw [grps_append]; rfl
  unfold ccfg; rw [e1, e2]
  exact ⟨_, by omega, steps_seq trans h1 (steps_seq trans (p_t3 _) h3)⟩

/-- **Halting.**  If the borrow passes the groups `ms` and then meets an empty group `(0,0)` (its separator is the
first `1` here) followed by a tape that starts with `1 1 1` (a group `(0, n+1)`, or two more groups, or four or more empty groups in all), the
machine halts. -/
theorem bounce_halt (n0 : Nat) (ms : List Nat) (R : Tape) :
    Halts trans ⟨blank, ctape n0 (ms.map (fun m => (0, m + 1)))
      (cons true (cons true (cons true (cons true (cons true R))))), .C⟩ := by
  obtain ⟨t1, ht1, h1⟩ := sweep n0 ms (cons true (cons true (cons true (cons true R))))
  exact ⟨_, _, steps_seq trans h1 (p_halt _ R).1, (p_halt _ R).2⟩


/-- **Merges** are equalities of tapes: an empty group followed by a group with digit 1 is one more `x`
(`1 · 1 10 = 1110`), so the two join the block of `x` before them. -/
theorem merge_mid (A B : List (Nat × Nat)) (d n n' : Nat) (F : Tape) :
    grps (A ++ (d, n) :: (0, 0) :: (1, n') :: B) F = grps (A ++ (d, n + 1 + n') :: B) F := by
  rw [grps_append, grps_append]; congr 1
  show cons true (rep d aw (rep n xw (cons true (cons true (cons true (cons false (rep n' xw (grps B F)))))))) =
    cons true (rep d aw (rep (n + 1 + n') xw (grps B F)))
  rw [rep_add, rep_add]; rfl

theorem merge_first (n0 n' : Nat) (B : List (Nat × Nat)) (F : Tape) :
    ctape n0 ((0, 0) :: (1, n') :: B) F = ctape (n0 + 1 + n') B F := by
  unfold ctape
  show cons false (cons true (cons false (rep n0 xw (cons true (cons true (cons true (cons false
    (rep n' xw (grps B F))))))))) = _
  rw [rep_add, rep_add]; rfl

theorem p_x1 (k : Nat) (L : Tape) :
    steps (10 * k + 9) ⟨cons false (rep (k) [true, false, true, false] (cons true (cons true (cons false (cons true (L)))))), blank, .E⟩ = some ⟨L, cons true (cons true (cons false (cons true (cons true (rep (k) [true, true, false, true] (cons true (blank))))))), .C⟩ := by
  have hn : 1 + ((k) * 10 + (8)) = 10 * k + 9 := by omega
  have h0 : steps 1 ⟨cons false (rep (k) [true, false, true, false] (cons true (cons true (cons false (cons true (L)))))), blank, .E⟩ = some ⟨rep (k) [true, false, true, false] (cons true (cons true (cons false (cons true (L))))), cons false (cons true (blank)), .D⟩ := rfl
  have c1 : ∀ L R : Tape, steps 10 ⟨app [true, false, true, false] L, app [false] R, .D⟩ = some ⟨L, app [false] (app [true, true, false, true] R), .D⟩ := fun _ _ => rfl
  have h1 : steps ((k) * 10) ⟨rep (k) [true, false, true, false] (cons true (cons true (cons false (cons true (L))))), cons false (cons true (blank)), .D⟩ = some ⟨cons true (cons true (cons false (cons true (L)))), cons false (rep (k) [true, true, false, true] (cons true (blank))), .D⟩ :=
    cross_l trans c1 (k) (cons true (cons true (cons false (cons true (L))))) (cons true (blank))
  have h2 : steps 8 ⟨cons true (cons true (cons false (cons true (L)))), cons false (rep (k) [true, true, false, true] (cons true (blank))), .D⟩ = some ⟨L, cons true (cons true (cons false (cons true (cons true (rep (k) [true, true, false, true] (cons true (blank))))))), .C⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (h2)))

theorem p_y (m : Nat) (L R : Tape) :
    steps (10 * m + 13) ⟨cons false (rep (m) [true, false, true, false] (cons true (cons true (cons false (cons true (L)))))), cons true (R), .C⟩ = some ⟨L, cons true (cons true (cons false (cons true (cons true (cons true (rep (m) [true, false, true, true] (R))))))), .C⟩ := by
  have hn : 0 + ((m) * 10 + (13)) = 10 * m + 13 := by omega
  have h0 : steps 0 ⟨cons false (rep (m) [true, false, true, false] (cons true (cons true (cons false (cons true (L)))))), cons true (R), .C⟩ = some ⟨rep (m) [false, true, false, true] (cons false (cons true (cons true (cons false (cons true (L)))))), cons true (R), .C⟩ := by
    simp only [steps_zero, show cons false (rep (m) [true, false, true, false] (cons true (cons true (cons false (cons true (L)))))) = rep (m) [false, true, false, true] (cons false (cons true (cons true (cons false (cons true (L)))))) from
      rep_rotate (m) [false] [true, false, true, false] [false, true, false, true] rfl (cons true (cons true (cons false (cons true (L)))))]
  have c1 : ∀ L R : Tape, steps 10 ⟨app [false, true, false, true] L, app [true] R, .C⟩ = some ⟨L, app [true] (app [true, false, true, true] R), .C⟩ := fun _ _ => rfl
  have h1 : steps ((m) * 10) ⟨rep (m) [false, true, false, true] (cons false (cons true (cons true (cons false (cons true (L)))))), cons true (R), .C⟩ = some ⟨cons false (cons true (cons true (cons false (cons true (L))))), cons true (rep (m) [true, false, true, true] (R)), .C⟩ :=
    cross_l trans c1 (m) (cons false (cons true (cons true (cons false (cons true (L)))))) (R)
  have h2 : steps 13 ⟨cons false (cons true (cons true (cons false (cons true (L))))), cons true (rep (m) [true, false, true, true] (R)), .C⟩ = some ⟨L, cons true (cons true (cons false (cons true (cons true (cons true (rep (m) [true, false, true, true] (R))))))), .C⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (h2)))

theorem p_z (n : Nat) (R : Tape) :
    steps (10 * n + 17) ⟨cons false (cons true (cons false (rep (n) [true, false, true, false] (cons true (blank))))), cons true (R), .C⟩ = some ⟨blank, cons false (cons true (cons false (cons true (cons true (cons false (cons true (cons true (rep (n) [true, false, true, true] (R))))))))), .C⟩ := by
  have hn : 0 + ((n) * 10 + (17)) = 10 * n + 17 := by omega
  have h0 : steps 0 ⟨cons false (cons true (cons false (rep (n) [true, false, true, false] (cons true (blank))))), cons true (R), .C⟩ = some ⟨rep (n) [false, true, false, true] (cons false (cons true (cons false (cons true (blank))))), cons true (R), .C⟩ := by
    simp only [steps_zero, show cons false (cons true (cons false (rep (n) [true, false, true, false] (cons true (blank))))) = rep (n) [false, true, false, true] (cons false (cons true (cons false (cons true (blank))))) from
      rep_rotate (n) [false, true, false] [true, false, true, false] [false, true, false, true] rfl (cons true (blank))]
  have c1 : ∀ L R : Tape, steps 10 ⟨app [false, true, false, true] L, app [true] R, .C⟩ = some ⟨L, app [true] (app [true, false, true, true] R), .C⟩ := fun _ _ => rfl
  have h1 : steps ((n) * 10) ⟨rep (n) [false, true, false, true] (cons false (cons true (cons false (cons true (blank))))), cons true (R), .C⟩ = some ⟨cons false (cons true (cons false (cons true (blank)))), cons true (rep (n) [true, false, true, true] (R)), .C⟩ :=
    cross_l trans c1 (n) (cons false (cons true (cons false (cons true (blank))))) (R)
  have h2 : steps 17 ⟨cons false (cons true (cons false (cons true (blank)))), cons true (rep (n) [true, false, true, true] (R)), .C⟩ = some ⟨blank, cons false (cons true (cons false (cons true (cons true (cons false (cons true (cons true (rep (n) [true, false, true, true] (R))))))))), .C⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (h2)))


/-- `(1011)^n 1 0 = 1 0 (1110)^n`. -/
theorem rot1 (n : Nat) (Z : Tape) :
    rep n [true, false, true, true] (cons true (cons false Z)) = cons true (cons false (rep n xw Z)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show cons true (cons false (cons true (cons true (rep n [true, false, true, true] (cons true (cons false Z)))))) = _
    rw [ih]; rfl

/-- `1 (1101)^k = (1110)^k 1`. -/
theorem rot2 (k : Nat) (Z : Tape) :
    cons true (rep k [true, true, false, true] Z) = rep k xw (cons true Z) := by
  induction k generalizing Z with
  | zero => rfl
  | succ k ih =>
    show cons true (cons true (cons true (cons false (cons true (rep k [true, true, false, true] Z))))) = _
    rw [ih]; rfl

/-- The tape `p_y` leaves for one group, `1 0 1 1 1 (1011)^m R`. -/
def wm (m : Nat) (R : Tape) : Tape :=
  cons true (cons false (cons true (cons true (cons true (rep m [true, false, true, true] R)))))

def wlist : List Nat → Tape → Tape
  | [], R => R
  | m :: ms, R => wm m (wlist ms R)

/-- C converts the passed groups back, from the right. -/
theorem conv_all (ms : List Nat) : ∀ (L R : Tape),
    ∃ t, steps t ⟨pathL ms L, cons true R, .C⟩ = some ⟨L, cons true (wlist ms R), .C⟩ := by
  induction ms with
  | nil => intro L R; exact ⟨0, rfl⟩
  | cons m ms ih =>
    intro L R
    obtain ⟨t, h⟩ := ih (lp m L) R
    exact ⟨_, steps_seq trans h (p_y m L (wlist ms R))⟩

theorem pathL_snoc (ms : List Nat) (k : Nat) : ∀ L, pathL (ms ++ [k]) L = lp k (pathL ms L) := by
  induction ms with
  | nil => intro L; rfl
  | cons m ms ih => intro L; exact ih (lp m L)

/-- `wlist` read as groups: each `wm m` followed by `1 0 ...` is the group `(0, m+1)`. -/
theorem wlist_grps (ms : List Nat) (k : Nat) :
    wlist ms (cons true (cons false (cons true (cons true (rep k [true, true, false, true] (cons true blank)))))) =
      cons true (cons false (grps (ms.map (fun m => (0, m + 1)) ++ [(0, k), (0, 0)]) (cons true blank))) := by
  induction ms with
  | nil =>
    show cons true (cons false (cons true (cons true (rep k [true, true, false, true] (cons true blank))))) = _
    rw [rot2]; rfl
  | cons m ms ih =>
    show wm m (wlist ms _) = _
    rw [ih]; unfold wm; rw [rot1]; rfl

/-- **Exhaustion.**  When every digit is 0 the borrow runs off the right end; the machine converts the tape back
and starts the next round with the counter `(0; (1, n0+1), (0, m1+1), ..., (0, m_(k-1)+1), (0, m_k), (0,0))`:
`n0` moves into the first group with digit 1, the last group loses an `x`, and an empty group is appended. -/
theorem exhaust (n0 : Nat) (ms : List Nat) (k : Nat) :
    ∃ t, 0 < t ∧ steps t (ccfg n0 ((ms ++ [k]).map (fun m => (0, m + 1)))) =
      some (ccfg 0 ((1, n0 + 1) :: ms.map (fun m => (0, m + 1)) ++ [(0, k), (0, 0)])) := by
  obtain ⟨t1, ht1, h1⟩ := sweep n0 (ms ++ [k]) blank
  rw [pathL_snoc] at h1
  have h2 := p_x1 k (pathL ms (cons false (cons true (cons false (rep n0 [true, false, true, false]
    (cons true blank))))))
  obtain ⟨t3, h3⟩ := conv_all ms (cons false (cons true (cons false (rep n0 [true, false, true, false]
    (cons true blank))))) (cons true (cons false (cons true (cons true (rep k [true, true, false, true]
    (cons true blank))))))
  have h4 := p_z n0 (wlist ms (cons true (cons false (cons true (cons true (rep k [true, true, false, true]
    (cons true blank)))))))
  have e : ccfg 0 ((1, n0 + 1) :: ms.map (fun m => (0, m + 1)) ++ [(0, k), (0, 0)]) =
      ⟨blank, cons false (cons true (cons false (cons true (cons true (cons false (cons true (cons true
        (rep n0 [true, false, true, true] (wlist ms (cons true (cons false (cons true (cons true
        (rep k [true, true, false, true] (cons true blank))))))))))))))), .C⟩ := by
    rw [wlist_grps, rot1]; rfl
  unfold ccfg at *
  rw [e]
  exact ⟨_, by omega, steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 h4))⟩

end H40361
