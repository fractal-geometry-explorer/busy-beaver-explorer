import Counter

/-! # The remaining cases of the counter of 1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RB---

`Counter.lean` proves the bounces that occur in the run.  This file proves what the machine does in the other
cases, so that the counter model (`Model.lean`) is defined on every counter configuration:

* `bounce_any`: the decrement works for every digit `e + 1` (not only 1 and 2);
* `exhaust0`: a round that ends with no group at all, `(n0; )  ->  (0; (1,n0), (0,0))`;
* `mid1`, `mid2`: the borrow meets one or two empty groups followed by a group with a digit `e + 2`: the machine
  turns round there as at the end of a round, `(n0; Z, (0,0), (e+2,n), rest) -> (0; (1,n0+1), Z, (0,0), (e,n), rest)`
  (`Z` the passed groups, unchanged), and the same with two empty groups.

The five pieces are written by `bbtools.symtm.prove`, like those of `Counter.lean`. -/

namespace H40361

open TM

theorem p_mx (k : Nat) (L R : Tape) :
    steps (10 * k + 23) ⟨cons false (rep (k) [true, false, true, false] (cons true (cons true (cons false (cons true (L)))))), cons true (cons true (cons false (cons true (cons false (R))))), .E⟩ = some ⟨L, cons true (cons true (cons false (cons true (cons true (cons true (cons true (cons false (cons true (rep (k) [true, true, false, true] (cons true (R))))))))))), .C⟩ := by
  have hn : 6 + (0 + ((k) * 10 + (17))) = 10 * k + 23 := by omega
  have h0 : steps 6 ⟨cons false (rep (k) [true, false, true, false] (cons true (cons true (cons false (cons true (L)))))), cons true (cons true (cons false (cons true (cons false (R))))), .E⟩ = some ⟨cons false (cons true (cons false (rep (k) [true, false, true, false] (cons true (cons true (cons false (cons true (L)))))))), cons true (cons false (cons true (R))), .B⟩ := rfl
  have h1 : steps 0 ⟨cons false (cons true (cons false (rep (k) [true, false, true, false] (cons true (cons true (cons false (cons true (L)))))))), cons true (cons false (cons true (R))), .B⟩ = some ⟨rep (k) [false, true, false, true] (cons false (cons true (cons false (cons true (cons true (cons false (cons true (L)))))))), cons true (cons false (cons true (R))), .B⟩ := by
    simp only [steps_zero, show cons false (cons true (cons false (rep (k) [true, false, true, false] (cons true (cons true (cons false (cons true (L)))))))) = rep (k) [false, true, false, true] (cons false (cons true (cons false (cons true (cons true (cons false (cons true (L)))))))) from
      rep_rotate (k) [false, true, false] [true, false, true, false] [false, true, false, true] rfl (cons true (cons true (cons false (cons true (L)))))]
  have c2 : ∀ L R : Tape, steps 10 ⟨app [false, true, false, true] L, app [true, false] R, .B⟩ = some ⟨L, app [true, false] (app [true, true, false, true] R), .B⟩ := fun _ _ => rfl
  have h2 : steps ((k) * 10) ⟨rep (k) [false, true, false, true] (cons false (cons true (cons false (cons true (cons true (cons false (cons true (L)))))))), cons true (cons false (cons true (R))), .B⟩ = some ⟨cons false (cons true (cons false (cons true (cons true (cons false (cons true (L))))))), cons true (cons false (rep (k) [true, true, false, true] (cons true (R)))), .B⟩ :=
    cross_l trans c2 (k) (cons false (cons true (cons false (cons true (cons true (cons false (cons true (L)))))))) (cons true (R))
  have h3 : steps 17 ⟨cons false (cons true (cons false (cons true (cons true (cons false (cons true (L))))))), cons true (cons false (rep (k) [true, true, false, true] (cons true (R)))), .B⟩ = some ⟨L, cons true (cons true (cons false (cons true (cons true (cons true (cons true (cons false (cons true (rep (k) [true, true, false, true] (cons true (R))))))))))), .C⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (h3))))

theorem p_mz (n : Nat) (R : Tape) :
    steps (10 * n + 27) ⟨cons false (cons true (cons false (rep (n) [true, false, true, false] (cons true (blank))))), cons true (cons true (cons false (cons true (cons false (R))))), .E⟩ = some ⟨blank, cons false (cons true (cons false (cons true (cons true (cons false (cons true (cons true (rep (n) [true, false, true, true] (cons true (cons false (cons true (cons true (R))))))))))))), .C⟩ := by
  have hn : 10 + (0 + ((n) * 10 + (17))) = 10 * n + 27 := by omega
  have h0 : steps 10 ⟨cons false (cons true (cons false (rep (n) [true, false, true, false] (cons true (blank))))), cons true (cons true (cons false (cons true (cons false (R))))), .E⟩ = some ⟨cons false (cons true (cons false (rep (n) [true, false, true, false] (cons true (blank))))), cons true (cons true (cons false (cons true (cons true (R))))), .C⟩ := rfl
  have h1 : steps 0 ⟨cons false (cons true (cons false (rep (n) [true, false, true, false] (cons true (blank))))), cons true (cons true (cons false (cons true (cons true (R))))), .C⟩ = some ⟨rep (n) [false, true, false, true] (cons false (cons true (cons false (cons true (blank))))), cons true (cons true (cons false (cons true (cons true (R))))), .C⟩ := by
    simp only [steps_zero, show cons false (cons true (cons false (rep (n) [true, false, true, false] (cons true (blank))))) = rep (n) [false, true, false, true] (cons false (cons true (cons false (cons true (blank))))) from
      rep_rotate (n) [false, true, false] [true, false, true, false] [false, true, false, true] rfl (cons true (blank))]
  have c2 : ∀ L R : Tape, steps 10 ⟨app [false, true, false, true] L, app [true] R, .C⟩ = some ⟨L, app [true] (app [true, false, true, true] R), .C⟩ := fun _ _ => rfl
  have h2 : steps ((n) * 10) ⟨rep (n) [false, true, false, true] (cons false (cons true (cons false (cons true (blank))))), cons true (cons true (cons false (cons true (cons true (R))))), .C⟩ = some ⟨cons false (cons true (cons false (cons true (blank)))), cons true (rep (n) [true, false, true, true] (cons true (cons false (cons true (cons true (R)))))), .C⟩ :=
    cross_l trans c2 (n) (cons false (cons true (cons false (cons true (blank))))) (cons true (cons false (cons true (cons true (R)))))
  have h3 : steps 17 ⟨cons false (cons true (cons false (cons true (blank)))), cons true (rep (n) [true, false, true, true] (cons true (cons false (cons true (cons true (R)))))), .C⟩ = some ⟨blank, cons false (cons true (cons false (cons true (cons true (cons false (cons true (cons true (rep (n) [true, false, true, true] (cons true (cons false (cons true (cons true (R))))))))))))), .C⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (h3))))

theorem p_mx2 (k : Nat) (L R : Tape) :
    steps (10 * k + 27) ⟨cons false (rep (k) [true, false, true, false] (cons true (cons true (cons false (cons true (L)))))), cons true (cons true (cons true (cons false (cons true (cons false (R)))))), .E⟩ = some ⟨L, cons true (cons true (cons false (cons true (cons true (cons true (cons true (cons false (cons true (rep (k) [true, true, false, true] (cons true (cons true (R)))))))))))), .C⟩ := by
  have hn : 10 + (0 + ((k) * 10 + (17))) = 10 * k + 27 := by omega
  have h0 : steps 10 ⟨cons false (rep (k) [true, false, true, false] (cons true (cons true (cons false (cons true (L)))))), cons true (cons true (cons true (cons false (cons true (cons false (R)))))), .E⟩ = some ⟨cons false (cons true (cons false (rep (k) [true, false, true, false] (cons true (cons true (cons false (cons true (L)))))))), cons true (cons false (cons true (cons true (R)))), .B⟩ := rfl
  have h1 : steps 0 ⟨cons false (cons true (cons false (rep (k) [true, false, true, false] (cons true (cons true (cons false (cons true (L)))))))), cons true (cons false (cons true (cons true (R)))), .B⟩ = some ⟨rep (k) [false, true, false, true] (cons false (cons true (cons false (cons true (cons true (cons false (cons true (L)))))))), cons true (cons false (cons true (cons true (R)))), .B⟩ := by
    simp only [steps_zero, show cons false (cons true (cons false (rep (k) [true, false, true, false] (cons true (cons true (cons false (cons true (L)))))))) = rep (k) [false, true, false, true] (cons false (cons true (cons false (cons true (cons true (cons false (cons true (L)))))))) from
      rep_rotate (k) [false, true, false] [true, false, true, false] [false, true, false, true] rfl (cons true (cons true (cons false (cons true (L)))))]
  have c2 : ∀ L R : Tape, steps 10 ⟨app [false, true, false, true] L, app [true, false] R, .B⟩ = some ⟨L, app [true, false] (app [true, true, false, true] R), .B⟩ := fun _ _ => rfl
  have h2 : steps ((k) * 10) ⟨rep (k) [false, true, false, true] (cons false (cons true (cons false (cons true (cons true (cons false (cons true (L)))))))), cons true (cons false (cons true (cons true (R)))), .B⟩ = some ⟨cons false (cons true (cons false (cons true (cons true (cons false (cons true (L))))))), cons true (cons false (rep (k) [true, true, false, true] (cons true (cons true (R))))), .B⟩ :=
    cross_l trans c2 (k) (cons false (cons true (cons false (cons true (cons true (cons false (cons true (L)))))))) (cons true (cons true (R)))
  have h3 : steps 17 ⟨cons false (cons true (cons false (cons true (cons true (cons false (cons true (L))))))), cons true (cons false (rep (k) [true, true, false, true] (cons true (cons true (R))))), .B⟩ = some ⟨L, cons true (cons true (cons false (cons true (cons true (cons true (cons true (cons false (cons true (rep (k) [true, true, false, true] (cons true (cons true (R)))))))))))), .C⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (h3))))

theorem p_mz2 (n : Nat) (R : Tape) :
    steps (10 * n + 31) ⟨cons false (cons true (cons false (rep (n) [true, false, true, false] (cons true (blank))))), cons true (cons true (cons true (cons false (cons true (cons false (R)))))), .E⟩ = some ⟨blank, cons false (cons true (cons false (cons true (cons true (cons false (cons true (cons true (rep (n) [true, false, true, true] (cons true (cons false (cons true (cons true (cons true (R)))))))))))))), .C⟩ := by
  have hn : 14 + (0 + ((n) * 10 + (17))) = 10 * n + 31 := by omega
  have h0 : steps 14 ⟨cons false (cons true (cons false (rep (n) [true, false, true, false] (cons true (blank))))), cons true (cons true (cons true (cons false (cons true (cons false (R)))))), .E⟩ = some ⟨cons false (cons true (cons false (rep (n) [true, false, true, false] (cons true (blank))))), cons true (cons true (cons false (cons true (cons true (cons true (R)))))), .C⟩ := rfl
  have h1 : steps 0 ⟨cons false (cons true (cons false (rep (n) [true, false, true, false] (cons true (blank))))), cons true (cons true (cons false (cons true (cons true (cons true (R)))))), .C⟩ = some ⟨rep (n) [false, true, false, true] (cons false (cons true (cons false (cons true (blank))))), cons true (cons true (cons false (cons true (cons true (cons true (R)))))), .C⟩ := by
    simp only [steps_zero, show cons false (cons true (cons false (rep (n) [true, false, true, false] (cons true (blank))))) = rep (n) [false, true, false, true] (cons false (cons true (cons false (cons true (blank))))) from
      rep_rotate (n) [false, true, false] [true, false, true, false] [false, true, false, true] rfl (cons true (blank))]
  have c2 : ∀ L R : Tape, steps 10 ⟨app [false, true, false, true] L, app [true] R, .C⟩ = some ⟨L, app [true] (app [true, false, true, true] R), .C⟩ := fun _ _ => rfl
  have h2 : steps ((n) * 10) ⟨rep (n) [false, true, false, true] (cons false (cons true (cons false (cons true (blank))))), cons true (cons true (cons false (cons true (cons true (cons true (R)))))), .C⟩ = some ⟨cons false (cons true (cons false (cons true (blank)))), cons true (rep (n) [true, false, true, true] (cons true (cons false (cons true (cons true (cons true (R))))))), .C⟩ :=
    cross_l trans c2 (n) (cons false (cons true (cons false (cons true (blank))))) (cons true (cons false (cons true (cons true (cons true (R))))))
  have h3 : steps 17 ⟨cons false (cons true (cons false (cons true (blank)))), cons true (rep (n) [true, false, true, true] (cons true (cons false (cons true (cons true (cons true (R))))))), .C⟩ = some ⟨blank, cons false (cons true (cons false (cons true (cons true (cons false (cons true (cons true (rep (n) [true, false, true, true] (cons true (cons false (cons true (cons true (cons true (R)))))))))))))), .C⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (h3))))

theorem p_e0 (n : Nat) :
    steps (10 * n + 13) ⟨cons false (cons true (cons false (rep (n) [true, false, true, false] (cons true (blank))))), blank, .E⟩ = some ⟨blank, cons false (cons true (cons false (cons true (cons true (cons false (cons true (rep (n) [true, true, false, true] (cons true (blank))))))))), .C⟩ := by
  have hn : 1 + (0 + ((n) * 10 + (12))) = 10 * n + 13 := by omega
  have h0 : steps 1 ⟨cons false (cons true (cons false (rep (n) [true, false, true, false] (cons true (blank))))), blank, .E⟩ = some ⟨cons true (cons false (rep (n) [true, false, true, false] (cons true (blank)))), cons false (cons true (blank)), .D⟩ := rfl
  have h1 : steps 0 ⟨cons true (cons false (rep (n) [true, false, true, false] (cons true (blank)))), cons false (cons true (blank)), .D⟩ = some ⟨rep (n) [true, false, true, false] (cons true (cons false (cons true (blank)))), cons false (cons true (blank)), .D⟩ := by
    simp only [steps_zero, show cons true (cons false (rep (n) [true, false, true, false] (cons true (blank)))) = rep (n) [true, false, true, false] (cons true (cons false (cons true (blank)))) from
      rep_rotate (n) [true, false] [true, false, true, false] [true, false, true, false] rfl (cons true (blank))]
  have c2 : ∀ L R : Tape, steps 10 ⟨app [true, false, true, false] L, app [false] R, .D⟩ = some ⟨L, app [false] (app [true, true, false, true] R), .D⟩ := fun _ _ => rfl
  have h2 : steps ((n) * 10) ⟨rep (n) [true, false, true, false] (cons true (cons false (cons true (blank)))), cons false (cons true (blank)), .D⟩ = some ⟨cons true (cons false (cons true (blank))), cons false (rep (n) [true, true, false, true] (cons true (blank))), .D⟩ :=
    cross_l trans c2 (n) (cons true (cons false (cons true (blank)))) (cons true (blank))
  have h3 : steps 12 ⟨cons true (cons false (cons true (blank))), cons false (rep (n) [true, true, false, true] (cons true (blank))), .D⟩ = some ⟨blank, cons false (cons true (cons false (cons true (cons true (cons false (cons true (rep (n) [true, true, false, true] (cons true (blank))))))))), .C⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (h3))))


/-- The decrement for every digit. -/
theorem bounce_any (n0 : Nat) (ms : List Nat) (e n : Nat) (rest : List (Nat × Nat)) (F : Tape) :
    ∃ t, 0 < t ∧ steps t ⟨blank, ctape n0 (ms.map (fun m => (0, m + 1)) ++ (e + 1, n) :: rest) F, .C⟩ =
      some ⟨blank, ctape (n0 + 1) (ms.map (fun m => (2, m)) ++ (e, n) :: rest) F, .C⟩ := by
  let Y := rep n xw (grps rest F)
  have h1 := p_start n0 (pathR ms (rep (e + 1) aw Y))
  obtain ⟨t2, h2⟩ := pass_all ms (cons false (cons true (cons false (rep n0 [true, false, true, false]
    (cons true blank))))) (rep (e + 1) aw Y)
  have h3 := p_turn1 (pathL ms (cons false (cons true (cons false (rep n0 [true, false, true, false]
    (cons true blank)))))) (rep e aw Y)
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

/-- **A round with no group.**  `(n0; )` becomes `(0; (1, n0), (0,0))`. -/
theorem exhaust0 (n0 : Nat) :
    ∃ t, 0 < t ∧ steps t (ccfg n0 []) = some (ccfg 0 [(1, n0), (0, 0)]) := by
  have h1 := p_start n0 blank
  have h2 := p_e0 n0
  have e : ccfg 0 [(1, n0), (0, 0)] = ⟨blank, cons false (cons true (cons false (cons true (cons true (cons false
      (cons true (rep n0 [true, true, false, true] (cons true blank)))))))), .C⟩ := by
    rw [rot2]; rfl
  rw [e]
  exact ⟨_, by omega, steps_seq trans h1 h2⟩

/-- `(1011)^k 1011 = 101 (1101)^k 1`. -/
theorem rot3 (k : Nat) (Z : Tape) :
    rep k [true, false, true, true] (cons true (cons false (cons true (cons true Z)))) =
      cons true (cons false (cons true (rep k [true, true, false, true] (cons true Z)))) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show cons true (cons false (cons true (cons true (rep k [true, false, true, true] _)))) = _
    rw [ih]; rfl

theorem wlist_snoc (ms : List Nat) (k : Nat) (R : Tape) : wlist (ms ++ [k]) R = wlist ms (wm k R) := by
  induction ms with
  | nil => rfl
  | cons m ms ih => show wm m (wlist (ms ++ [k]) R) = wm m (wlist ms (wm k R)); rw [ih]

/-- `wlist` read as groups, in front of `1 0 1 1 W`. -/
theorem wlist_grps2 (ms : List Nat) (W : Tape) :
    wlist ms (cons true (cons false (cons true (cons true W)))) =
      cons true (cons false (grps (ms.map (fun m => (0, m + 1))) (cons true (cons true W)))) := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    show wm m (wlist ms _) = _
    rw [ih]; unfold wm; rw [rot1]; rfl

/-- The turn in the middle of the list, from the two facts about the tape `W` that the head meets after the
separator of an empty group: over the last passed group (`hx`) and with no passed group (`hz`). -/
theorem mid_core (W W' : Tape)
    (hx : ∀ k L, ∃ t, steps t ⟨lp k L, W, .E⟩ =
      some ⟨L, cons true (wm k (cons true (cons false (cons true (cons true W'))))), .C⟩)
    (hz : ∀ n, ∃ t, steps t ⟨cons false (cons true (cons false (rep n [true, false, true, false]
        (cons true blank)))), W, .E⟩ =
      some ⟨blank, cons false (cons true (cons false (cons true (cons true (cons false (cons true (cons true
        (rep n [true, false, true, true] (cons true (cons false (cons true (cons true W')))))))))))), .C⟩)
    (n0 : Nat) (ms : List Nat) :
    ∃ t, 0 < t ∧ steps t ⟨blank, ctape n0 (ms.map (fun m => (0, m + 1))) (cons true W), .C⟩ =
      some ⟨blank, ctape 0 ((1, n0 + 1) :: ms.map (fun m => (0, m + 1))) (cons true (cons true W')), .C⟩ := by
  obtain ⟨t1, ht1, h1⟩ := sweep n0 ms W
  have e : ctape 0 ((1, n0 + 1) :: ms.map (fun m => (0, m + 1))) (cons true (cons true W')) =
      cons false (cons true (cons false (cons true (cons true (cons false (cons true (cons true
        (rep n0 [true, false, true, true] (wlist ms (cons true (cons false (cons true (cons true W'))))))))))))) := by
    rw [wlist_grps2, rot1]; rfl
  rw [e]
  rcases List.eq_nil_or_concat ms with rfl | ⟨init, k, rfl⟩
  · obtain ⟨t2, h2⟩ := hz n0
    exact ⟨_, by omega, steps_seq trans h1 h2⟩
  · rw [List.concat_eq_append] at h1 ⊢
    rw [pathL_snoc] at h1
    obtain ⟨t2, h2⟩ := hx k (pathL init (cons false (cons true (cons false (rep n0 [true, false, true, false]
      (cons true blank))))))
    obtain ⟨t3, h3⟩ := conv_all init (cons false (cons true (cons false (rep n0 [true, false, true, false]
      (cons true blank))))) (wm k (cons true (cons false (cons true (cons true W')))))
    have h4 := p_z n0 (wlist init (wm k (cons true (cons false (cons true (cons true W'))))))
    rw [wlist_snoc]
    exact ⟨_, by omega, steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 h4))⟩

/-- **A turn at one empty group.**  The borrow passes the groups `ms`, meets an empty group `(0,0)` and then a
group with digit `e + 2`: the machine turns round as at the end of a round.  `n0` moves into a new first group
with digit 1, the passed groups are restored, and the digit drops by two. -/
theorem mid1 (n0 : Nat) (ms : List Nat) (e n : Nat) (rest : List (Nat × Nat)) (F : Tape) :
    ∃ t, 0 < t ∧ steps t ⟨blank, ctape n0 (ms.map (fun m => (0, m + 1)) ++ (0, 0) :: (e + 2, n) :: rest) F, .C⟩ =
      some ⟨blank, ctape 0 ((1, n0 + 1) :: ms.map (fun m => (0, m + 1)) ++ (0, 0) :: (e, n) :: rest) F, .C⟩ := by
  have h := mid_core (cons true (cons true (cons false (cons true (cons false (rep e aw (rep n xw (grps rest F))))))))
    (rep e aw (rep n xw (grps rest F)))
    (fun k L => ⟨_, (by have := p_mx k L (rep e aw (rep n xw (grps rest F))); rw [← rot3] at this; exact this)⟩)
    (fun k => ⟨_, p_mz k _⟩) n0 ms
  have e1 : ctape n0 (ms.map (fun m => (0, m + 1)) ++ (0, 0) :: (e + 2, n) :: rest) F =
      ctape n0 (ms.map (fun m => (0, m + 1))) (cons true (cons true (cons true (cons false (cons true (cons false
        (rep e aw (rep n xw (grps rest F))))))))) := by
    unfold ctape; rw [grps_append]; rfl
  have e2 : ctape 0 ((1, n0 + 1) :: ms.map (fun m => (0, m + 1)) ++ (0, 0) :: (e, n) :: rest) F =
      ctape 0 ((1, n0 + 1) :: ms.map (fun m => (0, m + 1))) (cons true (cons true
        (rep e aw (rep n xw (grps rest F))))) := by
    unfold ctape; rw [grps_append]; rfl
  rw [e1, e2]; exact h

/-- **A turn at two empty groups**: the same with `(0,0), (0,0), (e+2, n)`. -/
theorem mid2 (n0 : Nat) (ms : List Nat) (e n : Nat) (rest : List (Nat × Nat)) (F : Tape) :
    ∃ t, 0 < t ∧ steps t ⟨blank, ctape n0 (ms.map (fun m => (0, m + 1)) ++ (0, 0) :: (0, 0) :: (e + 2, n) :: rest) F, .C⟩ =
      some ⟨blank, ctape 0 ((1, n0 + 1) :: ms.map (fun m => (0, m + 1)) ++ (0, 0) :: (0, 0) :: (e, n) :: rest) F, .C⟩ := by
  have h := mid_core (cons true (cons true (cons true (cons false (cons true (cons false (rep e aw (rep n xw (grps rest F)))))))))
    (cons true (rep e aw (rep n xw (grps rest F))))
    (fun k L => ⟨_, (by have := p_mx2 k L (rep e aw (rep n xw (grps rest F))); rw [← rot3] at this; exact this)⟩)
    (fun k => ⟨_, p_mz2 k _⟩) n0 ms
  have e1 : ctape n0 (ms.map (fun m => (0, m + 1)) ++ (0, 0) :: (0, 0) :: (e + 2, n) :: rest) F =
      ctape n0 (ms.map (fun m => (0, m + 1))) (cons true (cons true (cons true (cons true (cons false (cons true (cons false
        (rep e aw (rep n xw (grps rest F)))))))))) := by
    unfold ctape; rw [grps_append]; rfl
  have e2 : ctape 0 ((1, n0 + 1) :: ms.map (fun m => (0, m + 1)) ++ (0, 0) :: (0, 0) :: (e, n) :: rest) F =
      ctape 0 ((1, n0 + 1) :: ms.map (fun m => (0, m + 1))) (cons true (cons true (cons true
        (rep e aw (rep n xw (grps rest F)))))) := by
    unfold ctape; rw [grps_append]; rfl
  rw [e1, e2]; exact h

end H40361
