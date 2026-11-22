import Machine

/-! # 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1LF: busycoq PR 93's macro rules on this machine

Exchange the names E and F and replace the detour D0 = 1LE, E0 = 0RA, A1 = 1RA by one step 1RA (it ends in the same
configuration unless the cell left of D is 1, where the machine halts): the table becomes
1RB1RA_1LC0RD_1LD1LB_1RA0LE_0LB1LE, which is the table T3 of DeepMind's proof in busycoq PR 93
(1RB1RA_1LC0RD_1LD1LB_1RA0LE_0LB0LF_0LB---) except E1 (T3: 0LF then F0 = 0LB; here 1LE).  PR 93's engine works with
CfgR l r = l A> 0100 r, CfgL l r = l <B 1 r and CfgJ l r = l <C 100 r, the digit words D n = 1 (11)^n 00 and
S n = 1 (01)^(n+1) (written on the left, so read backwards there).  The rules below are stated for this machine, with
its detours, for every count and every tape L, R around them.  A rule that ends in CfgL or CfgJ (head on the last cell
of L) is stated one step before, when the head is still on the first cell of the rule's own tape:
CfgL L r is one step after `L C> 1 r` and CfgJ L r is one step after `L B> 0 0 0 r`.

Rules that change: the four rules of PR 93 that end in CfgJ (collision, collide, defect0, finishP) still end in CfgJ,
but where T3 writes the digit D (k+1) first, this machine writes D k 1 0.

Written by the folder's `py/engine_rules.py` with `tools/py/bbtools/symtm.py`; do not edit by hand. -/

namespace H99431

open TM

/-- PR 93 `rule_left`: CfgL (L · S n) R reaches CfgL L (D n · R). Same as T3. -/
theorem pr93_left (n : Nat) (L R : Tape) :
    steps (2 * n + 4) ⟨rep (n + 1) [false, true] (L), cons true (cons true (R)), .B⟩ = some ⟨L, cons true (cons true (rep (n) [true, true] (cons false (cons false (R))))), .C⟩ := by
  have hn : 3 + (0 + ((n) * 2 + (1))) = 2 * n + 4 := by omega
  have h0 : steps 3 ⟨rep (n + 1) [false, true] (L), cons true (cons true (R)), .B⟩ = some ⟨cons true (rep (n) [false, true] (L)), cons false (cons false (cons false (R))), .B⟩ := rfl
  have h1 : steps 0 ⟨cons true (rep (n) [false, true] (L)), cons false (cons false (cons false (R))), .B⟩ = some ⟨rep (n) [true, false] (cons true (L)), cons false (cons false (cons false (R))), .B⟩ := by
    simp only [steps_zero, show cons true (rep (n) [false, true] (L)) = rep (n) [true, false] (cons true (L)) from
      rep_rotate (n) [true] [false, true] [true, false] rfl (L)]
  have c2 : ∀ L R : Tape, steps 2 ⟨app [true, false] L, app [false] R, .B⟩ = some ⟨L, app [false] (app [true, true] R), .B⟩ := fun _ _ => rfl
  have h2 : steps ((n) * 2) ⟨rep (n) [true, false] (cons true (L)), cons false (cons false (cons false (R))), .B⟩ = some ⟨cons true (L), cons false (rep (n) [true, true] (cons false (cons false (R)))), .B⟩ :=
    cross_l trans c2 (n) (cons true (L)) (cons false (cons false (R)))
  have h3 : steps 1 ⟨cons true (L), cons false (rep (n) [true, true] (cons false (cons false (R)))), .B⟩ = some ⟨L, cons true (cons true (rep (n) [true, true] (cons false (cons false (R))))), .C⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (h3))))

/-- PR 93 `rule_even`: CfgR L ((11)^(n+1) 00 R) reaches CfgL L (D (n+1) · 10 · R). Same as T3. -/
theorem pr93_even (n : Nat) (L R : Tape) :
    steps (10 * n + 22) ⟨L, cons false (cons true (cons false (cons false (rep (n + 1) [true, true] (cons false (cons false (R))))))), .A⟩ = some ⟨L, cons true (cons true (cons true (cons true (rep (n) [true, true] (cons false (cons false (cons true (cons false (R))))))))), .C⟩ := by
  have hn : 6 + ((n + 1) * 8 + (5 + ((n) * 2 + (3)))) = 10 * n + 22 := by omega
  have h0 : steps 6 ⟨L, cons false (cons true (cons false (cons false (rep (n + 1) [true, true] (cons false (cons false (R))))))), .A⟩ = some ⟨cons true (cons true (cons false (cons true (L)))), rep (n + 1) [true, true] (cons false (cons false (R))), .B⟩ := rfl
  have c1 : ∀ L R : Tape, steps 8 ⟨app [true] L, app [true, true] R, .B⟩ = some ⟨app [true] (app [true, false] L), R, .B⟩ := fun _ _ => rfl
  have h1 : steps ((n + 1) * 8) ⟨cons true (cons true (cons false (cons true (L)))), rep (n + 1) [true, true] (cons false (cons false (R))), .B⟩ = some ⟨cons true (rep (n + 1) [true, false] (cons true (cons false (cons true (L))))), cons false (cons false (R)), .B⟩ :=
    cross_r trans c1 (n + 1) (cons true (cons false (cons true (L)))) (cons false (cons false (R)))
  have h2 : steps 5 ⟨cons true (rep (n + 1) [true, false] (cons true (cons false (cons true (L))))), cons false (cons false (R)), .B⟩ = some ⟨rep (n) [true, false] (cons true (cons false (cons true (L)))), cons false (cons false (cons false (cons true (cons false (R))))), .B⟩ := rfl
  have c3 : ∀ L R : Tape, steps 2 ⟨app [true, false] L, app [false] R, .B⟩ = some ⟨L, app [false] (app [true, true] R), .B⟩ := fun _ _ => rfl
  have h3 : steps ((n) * 2) ⟨rep (n) [true, false] (cons true (cons false (cons true (L)))), cons false (cons false (cons false (cons true (cons false (R))))), .B⟩ = some ⟨cons true (cons false (cons true (L))), cons false (rep (n) [true, true] (cons false (cons false (cons true (cons false (R)))))), .B⟩ :=
    cross_l trans c3 (n) (cons true (cons false (cons true (L)))) (cons false (cons false (cons true (cons false (R)))))
  have h4 : steps 3 ⟨cons true (cons false (cons true (L))), cons false (rep (n) [true, true] (cons false (cons false (cons true (cons false (R)))))), .B⟩ = some ⟨L, cons true (cons true (cons true (cons true (rep (n) [true, true] (cons false (cons false (cons true (cons false (R))))))))), .C⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (h4)))))

/-- PR 93 `rule_leftJ`: CfgJ (L · S n) R reaches CfgL L (D (n+1) · R). Same as T3. -/
theorem pr93_leftJ (n : Nat) (L R : Tape) :
    steps (2 * n + 2) ⟨rep (n + 1) [false, true] (L), cons true (cons true (cons false (cons false (R)))), .C⟩ = some ⟨L, cons true (rep (n + 1) [true, true] (cons true (cons false (cons false (R))))), .C⟩ := by
  have hn : (n + 1) * 2 = 2 * n + 2 := by omega
  have c0 : ∀ L R : Tape, steps 2 ⟨app [false, true] L, app [true] R, .C⟩ = some ⟨L, app [true] (app [true, true] R), .C⟩ := fun _ _ => rfl
  have h0 : steps ((n + 1) * 2) ⟨rep (n + 1) [false, true] (L), cons true (cons true (cons false (cons false (R)))), .C⟩ = some ⟨L, cons true (rep (n + 1) [true, true] (cons true (cons false (cons false (R))))), .C⟩ :=
    cross_l trans c0 (n + 1) (L) (cons true (cons false (cons false (R))))
  exact steps_congr trans hn (h0)

/-- PR 93 `rule_turnJ` (b+1 for its b): CfgJ (L · 111 · (10)^(b+1)) R reaches CfgR (L · (10)^(b+2)) R. Same as T3. -/
theorem pr93_turnJ (b : Nat) (L R : Tape) :
    steps (10 * b + 18) ⟨cons false (rep (b) [true, false] (cons true (cons true (cons true (L))))), cons true (cons true (cons false (cons false (R)))), .C⟩ = some ⟨cons true (cons false (rep (b) [true, false] (cons true (cons false (L))))), cons false (cons true (cons false (cons false (R)))), .A⟩ := by
  have hn : 0 + ((b) * 2 + (12 + (0 + ((b) * 8 + (6))))) = 10 * b + 18 := by omega
  have h0 : steps 0 ⟨cons false (rep (b) [true, false] (cons true (cons true (cons true (L))))), cons true (cons true (cons false (cons false (R)))), .C⟩ = some ⟨rep (b) [false, true] (cons false (cons true (cons true (cons true (L))))), cons true (cons true (cons false (cons false (R)))), .C⟩ := by
    simp only [steps_zero, show cons false (rep (b) [true, false] (cons true (cons true (cons true (L))))) = rep (b) [false, true] (cons false (cons true (cons true (cons true (L))))) from
      rep_rotate (b) [false] [true, false] [false, true] rfl (cons true (cons true (cons true (L))))]
  have c1 : ∀ L R : Tape, steps 2 ⟨app [false, true] L, app [true] R, .C⟩ = some ⟨L, app [true] (app [true, true] R), .C⟩ := fun _ _ => rfl
  have h1 : steps ((b) * 2) ⟨rep (b) [false, true] (cons false (cons true (cons true (cons true (L))))), cons true (cons true (cons false (cons false (R)))), .C⟩ = some ⟨cons false (cons true (cons true (cons true (L)))), cons true (rep (b) [true, true] (cons true (cons false (cons false (R))))), .C⟩ :=
    cross_l trans c1 (b) (cons false (cons true (cons true (cons true (L))))) (cons true (cons false (cons false (R))))
  have h2 : steps 12 ⟨cons false (cons true (cons true (cons true (L)))), cons true (rep (b) [true, true] (cons true (cons false (cons false (R))))), .C⟩ = some ⟨cons false (cons true (cons true (cons false (L)))), cons true (rep (b) [true, true] (cons true (cons false (cons false (R))))), .D⟩ := rfl
  have h3 : steps 0 ⟨cons false (cons true (cons true (cons false (L)))), cons true (rep (b) [true, true] (cons true (cons false (cons false (R))))), .D⟩ = some ⟨cons false (cons true (cons true (cons false (L)))), rep (b) [true, true] (cons true (cons true (cons false (cons false (R))))), .D⟩ := by
    simp only [steps_zero, show cons true (rep (b) [true, true] (cons true (cons false (cons false (R))))) = rep (b) [true, true] (cons true (cons true (cons false (cons false (R))))) from
      rep_rotate (b) [true] [true, true] [true, true] rfl (cons true (cons false (cons false (R))))]
  have c4 : ∀ L R : Tape, steps 8 ⟨app [false, true] L, app [true, true] R, .D⟩ = some ⟨app [false, true] (app [true, false] L), R, .D⟩ := fun _ _ => rfl
  have h4 : steps ((b) * 8) ⟨cons false (cons true (cons true (cons false (L)))), rep (b) [true, true] (cons true (cons true (cons false (cons false (R))))), .D⟩ = some ⟨cons false (cons true (rep (b) [true, false] (cons true (cons false (L))))), cons true (cons true (cons false (cons false (R)))), .D⟩ :=
    cross_r trans c4 (b) (cons true (cons false (L))) (cons true (cons true (cons false (cons false (R)))))
  have h5 : steps 6 ⟨cons false (cons true (rep (b) [true, false] (cons true (cons false (L))))), cons true (cons true (cons false (cons false (R)))), .D⟩ = some ⟨cons true (cons false (rep (b) [true, false] (cons true (cons false (L))))), cons false (cons true (cons false (cons false (R)))), .A⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (steps_seq trans h4 (h5))))))

/-- PR 93 `rule_defect1`: CfgR L (10 · D 1 · 1 (11)^m 0 · R) reaches CfgL L (D 0 · D 0 · D (m+1) · 1 · R). Same as T3. -/
theorem pr93_defect1 (m : Nat) (L R : Tape) :
    steps (10 * m + 50) ⟨L, cons false (cons true (cons false (cons false (cons true (cons false (cons true (rep (1) [true, true] (cons false (cons false (cons true (rep (m) [true, true] (cons false (R))))))))))))), .A⟩ = some ⟨L, cons true (cons true (cons false (cons false (cons true (cons false (cons false (cons true (cons true (cons true (rep (m) [true, true] (cons false (cons false (cons true (R)))))))))))))), .C⟩ := by
  have hn : 10 + (0 + ((1) * 2 + (13 + (0 + ((m) * 8 + (12 + ((m) * 2 + (13)))))))) = 10 * m + 50 := by omega
  have h0 : steps 10 ⟨L, cons false (cons true (cons false (cons false (cons true (cons false (cons true (rep (1) [true, true] (cons false (cons false (cons true (rep (m) [true, true] (cons false (R))))))))))))), .A⟩ = some ⟨cons true (cons false (cons true (cons true (cons false (cons true (L)))))), cons true (rep (1) [true, true] (cons false (cons false (cons true (rep (m) [true, true] (cons false (R))))))), .A⟩ := rfl
  have h1 : steps 0 ⟨cons true (cons false (cons true (cons true (cons false (cons true (L)))))), cons true (rep (1) [true, true] (cons false (cons false (cons true (rep (m) [true, true] (cons false (R))))))), .A⟩ = some ⟨cons true (cons false (cons true (cons true (cons false (cons true (L)))))), rep (1) [true, true] (cons true (cons false (cons false (cons true (rep (m) [true, true] (cons false (R))))))), .A⟩ := by
    simp only [steps_zero, show cons true (rep (1) [true, true] (cons false (cons false (cons true (rep (m) [true, true] (cons false (R))))))) = rep (1) [true, true] (cons true (cons false (cons false (cons true (rep (m) [true, true] (cons false (R))))))) from
      rep_rotate (1) [true] [true, true] [true, true] rfl (cons false (cons false (cons true (rep (m) [true, true] (cons false (R))))))]
  have c2 : ∀ L R : Tape, steps 2 ⟨app [] L, app [true, true] R, .A⟩ = some ⟨app [] (app [true, true] L), R, .A⟩ := fun _ _ => rfl
  have h2 : steps ((1) * 2) ⟨cons true (cons false (cons true (cons true (cons false (cons true (L)))))), rep (1) [true, true] (cons true (cons false (cons false (cons true (rep (m) [true, true] (cons false (R))))))), .A⟩ = some ⟨rep (1) [true, true] (cons true (cons false (cons true (cons true (cons false (cons true (L))))))), cons true (cons false (cons false (cons true (rep (m) [true, true] (cons false (R)))))), .A⟩ :=
    cross_r trans c2 (1) (cons true (cons false (cons true (cons true (cons false (cons true (L))))))) (cons true (cons false (cons false (cons true (rep (m) [true, true] (cons false (R)))))))
  have h3 : steps 13 ⟨rep (1) [true, true] (cons true (cons false (cons true (cons true (cons false (cons true (L))))))), cons true (cons false (cons false (cons true (rep (m) [true, true] (cons false (R)))))), .A⟩ = some ⟨cons false (cons true (cons true (cons false (cons true (cons true (cons false (cons true (cons true (cons false (cons true (L))))))))))), cons true (rep (m) [true, true] (cons false (R))), .D⟩ := rfl
  have h4 : steps 0 ⟨cons false (cons true (cons true (cons false (cons true (cons true (cons false (cons true (cons true (cons false (cons true (L))))))))))), cons true (rep (m) [true, true] (cons false (R))), .D⟩ = some ⟨cons false (cons true (cons true (cons false (cons true (cons true (cons false (cons true (cons true (cons false (cons true (L))))))))))), rep (m) [true, true] (cons true (cons false (R))), .D⟩ := by
    simp only [steps_zero, show cons true (rep (m) [true, true] (cons false (R))) = rep (m) [true, true] (cons true (cons false (R))) from
      rep_rotate (m) [true] [true, true] [true, true] rfl (cons false (R))]
  have c5 : ∀ L R : Tape, steps 8 ⟨app [false, true] L, app [true, true] R, .D⟩ = some ⟨app [false, true] (app [true, false] L), R, .D⟩ := fun _ _ => rfl
  have h5 : steps ((m) * 8) ⟨cons false (cons true (cons true (cons false (cons true (cons true (cons false (cons true (cons true (cons false (cons true (L))))))))))), rep (m) [true, true] (cons true (cons false (R))), .D⟩ = some ⟨cons false (cons true (rep (m) [true, false] (cons true (cons false (cons true (cons true (cons false (cons true (cons true (cons false (cons true (L)))))))))))), cons true (cons false (R)), .D⟩ :=
    cross_r trans c5 (m) (cons true (cons false (cons true (cons true (cons false (cons true (cons true (cons false (cons true (L)))))))))) (cons true (cons false (R)))
  have h6 : steps 12 ⟨cons false (cons true (rep (m) [true, false] (cons true (cons false (cons true (cons true (cons false (cons true (cons true (cons false (cons true (L)))))))))))), cons true (cons false (R)), .D⟩ = some ⟨rep (m) [true, false] (cons true (cons false (cons true (cons true (cons false (cons true (cons true (cons false (cons true (L)))))))))), cons false (cons false (cons false (cons true (R)))), .B⟩ := rfl
  have c7 : ∀ L R : Tape, steps 2 ⟨app [true, false] L, app [false] R, .B⟩ = some ⟨L, app [false] (app [true, true] R), .B⟩ := fun _ _ => rfl
  have h7 : steps ((m) * 2) ⟨rep (m) [true, false] (cons true (cons false (cons true (cons true (cons false (cons true (cons true (cons false (cons true (L)))))))))), cons false (cons false (cons false (cons true (R)))), .B⟩ = some ⟨cons true (cons false (cons true (cons true (cons false (cons true (cons true (cons false (cons true (L))))))))), cons false (rep (m) [true, true] (cons false (cons false (cons true (R))))), .B⟩ :=
    cross_l trans c7 (m) (cons true (cons false (cons true (cons true (cons false (cons true (cons true (cons false (cons true (L)))))))))) (cons false (cons false (cons true (R))))
  have h8 : steps 13 ⟨cons true (cons false (cons true (cons true (cons false (cons true (cons true (cons false (cons true (L))))))))), cons false (rep (m) [true, true] (cons false (cons false (cons true (R))))), .B⟩ = some ⟨L, cons true (cons true (cons false (cons false (cons true (cons false (cons false (cons true (cons true (cons true (rep (m) [true, true] (cons false (cons false (cons true (R)))))))))))))), .C⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (steps_seq trans h4 (steps_seq trans h5 (steps_seq trans h6 (steps_seq trans h7 (h8)))))))))

/-- PR 93 `rule_defect_blank0`: CfgR L (10 · D 0 · 00 · R) reaches CfgR (L · S 0 · 1001) R. Same as T3. -/
theorem pr93_dblank0 (L R : Tape) :
    steps (21) ⟨L, cons false (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons false (cons false (cons false (R))))))))))), .A⟩ = some ⟨cons true (cons false (cons false (cons true (cons true (cons false (cons true (L))))))), cons false (cons true (cons false (cons false (R)))), .A⟩ := by
  have hn : 21 = 21 := by omega
  have h0 : steps 21 ⟨L, cons false (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons false (cons false (cons false (R))))))))))), .A⟩ = some ⟨cons true (cons false (cons false (cons true (cons true (cons false (cons true (L))))))), cons false (cons true (cons false (cons false (R)))), .A⟩ := rfl
  exact steps_congr trans hn (h0)

/-- Changed. PR 93 `rule_collisionD`: CfgL (L · 001101) (D n · R) reaches CfgJ L (D (n+2) · R) for T3; here CfgJ L (D (n+1) · 10 · R). -/
theorem pr93_collisionD (n : Nat) (L R : Tape) :
    steps (10 * n + 39) ⟨cons false (cons true (cons true (cons false (cons true (L))))), cons false (cons true (cons true (rep (n) [true, true] (cons false (cons false (R)))))), .B⟩ = some ⟨L, cons false (cons false (cons false (cons true (cons true (cons true (rep (n) [true, true] (cons false (cons false (cons true (cons false (R))))))))))), .B⟩ := by
  have hn : 20 + (0 + ((n) * 8 + (12 + ((n) * 2 + (7))))) = 10 * n + 39 := by omega
  have h0 : steps 20 ⟨cons false (cons true (cons true (cons false (cons true (L))))), cons false (cons true (cons true (rep (n) [true, true] (cons false (cons false (R)))))), .B⟩ = some ⟨cons false (cons true (cons true (cons false (cons true (cons true (cons false (L))))))), cons true (rep (n) [true, true] (cons false (cons false (R)))), .D⟩ := rfl
  have h1 : steps 0 ⟨cons false (cons true (cons true (cons false (cons true (cons true (cons false (L))))))), cons true (rep (n) [true, true] (cons false (cons false (R)))), .D⟩ = some ⟨cons false (cons true (cons true (cons false (cons true (cons true (cons false (L))))))), rep (n) [true, true] (cons true (cons false (cons false (R)))), .D⟩ := by
    simp only [steps_zero, show cons true (rep (n) [true, true] (cons false (cons false (R)))) = rep (n) [true, true] (cons true (cons false (cons false (R)))) from
      rep_rotate (n) [true] [true, true] [true, true] rfl (cons false (cons false (R)))]
  have c2 : ∀ L R : Tape, steps 8 ⟨app [false, true] L, app [true, true] R, .D⟩ = some ⟨app [false, true] (app [true, false] L), R, .D⟩ := fun _ _ => rfl
  have h2 : steps ((n) * 8) ⟨cons false (cons true (cons true (cons false (cons true (cons true (cons false (L))))))), rep (n) [true, true] (cons true (cons false (cons false (R)))), .D⟩ = some ⟨cons false (cons true (rep (n) [true, false] (cons true (cons false (cons true (cons true (cons false (L)))))))), cons true (cons false (cons false (R))), .D⟩ :=
    cross_r trans c2 (n) (cons true (cons false (cons true (cons true (cons false (L)))))) (cons true (cons false (cons false (R))))
  have h3 : steps 12 ⟨cons false (cons true (rep (n) [true, false] (cons true (cons false (cons true (cons true (cons false (L)))))))), cons true (cons false (cons false (R))), .D⟩ = some ⟨rep (n) [true, false] (cons true (cons false (cons true (cons true (cons false (L)))))), cons false (cons false (cons false (cons true (cons false (R))))), .B⟩ := rfl
  have c4 : ∀ L R : Tape, steps 2 ⟨app [true, false] L, app [false] R, .B⟩ = some ⟨L, app [false] (app [true, true] R), .B⟩ := fun _ _ => rfl
  have h4 : steps ((n) * 2) ⟨rep (n) [true, false] (cons true (cons false (cons true (cons true (cons false (L)))))), cons false (cons false (cons false (cons true (cons false (R))))), .B⟩ = some ⟨cons true (cons false (cons true (cons true (cons false (L))))), cons false (rep (n) [true, true] (cons false (cons false (cons true (cons false (R)))))), .B⟩ :=
    cross_l trans c4 (n) (cons true (cons false (cons true (cons true (cons false (L)))))) (cons false (cons false (cons true (cons false (R)))))
  have h5 : steps 7 ⟨cons true (cons false (cons true (cons true (cons false (L))))), cons false (rep (n) [true, true] (cons false (cons false (cons true (cons false (R)))))), .B⟩ = some ⟨L, cons false (cons false (cons false (cons true (cons true (cons true (rep (n) [true, true] (cons false (cons false (cons true (cons false (R))))))))))), .B⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (steps_seq trans h4 (h5))))))

/-- Changed. PR 93 `rule_collide`: CfgR L (10 · D 0 · D 0 · R) reaches CfgJ L (D 2 · 10 · R) for T3; here CfgJ L (D 1 · 10 · 10 · R). -/
theorem pr93_collide (L R : Tape) :
    steps (76) ⟨L, cons false (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons false (cons true (cons false (cons false (R)))))))))))), .A⟩ = some ⟨L, cons false (cons false (cons false (cons true (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (R)))))))))))), .B⟩ := by
  have hn : 40 + (36) = 76 := by omega
  have h0 : steps 40 ⟨L, cons false (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons false (cons true (cons false (cons false (R)))))))))))), .A⟩ = some ⟨cons false (cons true (L)), cons true (cons false (cons true (cons true (cons true (cons true (cons false (cons false (cons true (cons false (R)))))))))), .F⟩ := rfl
  have h1 : steps 36 ⟨cons false (cons true (L)), cons true (cons false (cons true (cons true (cons true (cons true (cons false (cons false (cons true (cons false (R)))))))))), .F⟩ = some ⟨L, cons false (cons false (cons false (cons true (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (R)))))))))))), .B⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (h1))

/-- Changed. PR 93 `rule_defect0D`: CfgR L (10 · D 0 · D m · R) reaches CfgJ L (D (m+2) · 10 · R) for T3; here CfgJ L (D (m+1) · 10 · 10 · R). -/
theorem pr93_defect0D (m : Nat) (L R : Tape) :
    steps (20 * m + 76) ⟨L, cons false (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons false (cons true (rep (m) [true, true] (cons false (cons false (R))))))))))))), .A⟩ = some ⟨L, cons false (cons false (cons false (cons true (cons true (cons true (rep (m) [true, true] (cons false (cons false (cons true (cons false (cons true (cons false (R))))))))))))), .B⟩ := by
  have hn : 23 + (0 + ((m) * 8 + (12 + ((m) * 2 + (22 + (0 + ((m) * 8 + (12 + ((m) * 2 + (7)))))))))) = 20 * m + 76 := by omega
  have h0 : steps 23 ⟨L, cons false (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons false (cons true (rep (m) [true, true] (cons false (cons false (R))))))))))))), .A⟩ = some ⟨cons false (cons true (cons true (cons false (cons false (cons true (cons true (cons false (cons true (L))))))))), cons true (rep (m) [true, true] (cons false (cons false (R)))), .D⟩ := rfl
  have h1 : steps 0 ⟨cons false (cons true (cons true (cons false (cons false (cons true (cons true (cons false (cons true (L))))))))), cons true (rep (m) [true, true] (cons false (cons false (R)))), .D⟩ = some ⟨cons false (cons true (cons true (cons false (cons false (cons true (cons true (cons false (cons true (L))))))))), rep (m) [true, true] (cons true (cons false (cons false (R)))), .D⟩ := by
    simp only [steps_zero, show cons true (rep (m) [true, true] (cons false (cons false (R)))) = rep (m) [true, true] (cons true (cons false (cons false (R)))) from
      rep_rotate (m) [true] [true, true] [true, true] rfl (cons false (cons false (R)))]
  have c2 : ∀ L R : Tape, steps 8 ⟨app [false, true] L, app [true, true] R, .D⟩ = some ⟨app [false, true] (app [true, false] L), R, .D⟩ := fun _ _ => rfl
  have h2 : steps ((m) * 8) ⟨cons false (cons true (cons true (cons false (cons false (cons true (cons true (cons false (cons true (L))))))))), rep (m) [true, true] (cons true (cons false (cons false (R)))), .D⟩ = some ⟨cons false (cons true (rep (m) [true, false] (cons true (cons false (cons false (cons true (cons true (cons false (cons true (L)))))))))), cons true (cons false (cons false (R))), .D⟩ :=
    cross_r trans c2 (m) (cons true (cons false (cons false (cons true (cons true (cons false (cons true (L)))))))) (cons true (cons false (cons false (R))))
  have h3 : steps 12 ⟨cons false (cons true (rep (m) [true, false] (cons true (cons false (cons false (cons true (cons true (cons false (cons true (L)))))))))), cons true (cons false (cons false (R))), .D⟩ = some ⟨rep (m) [true, false] (cons true (cons false (cons false (cons true (cons true (cons false (cons true (L)))))))), cons false (cons false (cons false (cons true (cons false (R))))), .B⟩ := rfl
  have c4 : ∀ L R : Tape, steps 2 ⟨app [true, false] L, app [false] R, .B⟩ = some ⟨L, app [false] (app [true, true] R), .B⟩ := fun _ _ => rfl
  have h4 : steps ((m) * 2) ⟨rep (m) [true, false] (cons true (cons false (cons false (cons true (cons true (cons false (cons true (L)))))))), cons false (cons false (cons false (cons true (cons false (R))))), .B⟩ = some ⟨cons true (cons false (cons false (cons true (cons true (cons false (cons true (L))))))), cons false (rep (m) [true, true] (cons false (cons false (cons true (cons false (R)))))), .B⟩ :=
    cross_l trans c4 (m) (cons true (cons false (cons false (cons true (cons true (cons false (cons true (L)))))))) (cons false (cons false (cons true (cons false (R)))))
  have h5 : steps 22 ⟨cons true (cons false (cons false (cons true (cons true (cons false (cons true (L))))))), cons false (rep (m) [true, true] (cons false (cons false (cons true (cons false (R)))))), .B⟩ = some ⟨cons false (cons true (cons true (cons false (cons true (cons true (cons false (L))))))), cons true (rep (m) [true, true] (cons false (cons false (cons true (cons false (R)))))), .D⟩ := rfl
  have h6 : steps 0 ⟨cons false (cons true (cons true (cons false (cons true (cons true (cons false (L))))))), cons true (rep (m) [true, true] (cons false (cons false (cons true (cons false (R)))))), .D⟩ = some ⟨cons false (cons true (cons true (cons false (cons true (cons true (cons false (L))))))), rep (m) [true, true] (cons true (cons false (cons false (cons true (cons false (R)))))), .D⟩ := by
    simp only [steps_zero, show cons true (rep (m) [true, true] (cons false (cons false (cons true (cons false (R)))))) = rep (m) [true, true] (cons true (cons false (cons false (cons true (cons false (R)))))) from
      rep_rotate (m) [true] [true, true] [true, true] rfl (cons false (cons false (cons true (cons false (R)))))]
  have c7 : ∀ L R : Tape, steps 8 ⟨app [false, true] L, app [true, true] R, .D⟩ = some ⟨app [false, true] (app [true, false] L), R, .D⟩ := fun _ _ => rfl
  have h7 : steps ((m) * 8) ⟨cons false (cons true (cons true (cons false (cons true (cons true (cons false (L))))))), rep (m) [true, true] (cons true (cons false (cons false (cons true (cons false (R)))))), .D⟩ = some ⟨cons false (cons true (rep (m) [true, false] (cons true (cons false (cons true (cons true (cons false (L)))))))), cons true (cons false (cons false (cons true (cons false (R))))), .D⟩ :=
    cross_r trans c7 (m) (cons true (cons false (cons true (cons true (cons false (L)))))) (cons true (cons false (cons false (cons true (cons false (R))))))
  have h8 : steps 12 ⟨cons false (cons true (rep (m) [true, false] (cons true (cons false (cons true (cons true (cons false (L)))))))), cons true (cons false (cons false (cons true (cons false (R))))), .D⟩ = some ⟨rep (m) [true, false] (cons true (cons false (cons true (cons true (cons false (L)))))), cons false (cons false (cons false (cons true (cons false (cons true (cons false (R))))))), .B⟩ := rfl
  have c9 : ∀ L R : Tape, steps 2 ⟨app [true, false] L, app [false] R, .B⟩ = some ⟨L, app [false] (app [true, true] R), .B⟩ := fun _ _ => rfl
  have h9 : steps ((m) * 2) ⟨rep (m) [true, false] (cons true (cons false (cons true (cons true (cons false (L)))))), cons false (cons false (cons false (cons true (cons false (cons true (cons false (R))))))), .B⟩ = some ⟨cons true (cons false (cons true (cons true (cons false (L))))), cons false (rep (m) [true, true] (cons false (cons false (cons true (cons false (cons true (cons false (R)))))))), .B⟩ :=
    cross_l trans c9 (m) (cons true (cons false (cons true (cons true (cons false (L)))))) (cons false (cons false (cons true (cons false (cons true (cons false (R)))))))
  have h10 : steps 7 ⟨cons true (cons false (cons true (cons true (cons false (L))))), cons false (rep (m) [true, true] (cons false (cons false (cons true (cons false (cons true (cons false (R)))))))), .B⟩ = some ⟨L, cons false (cons false (cons false (cons true (cons true (cons true (rep (m) [true, true] (cons false (cons false (cons true (cons false (cons true (cons false (R))))))))))))), .B⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (steps_seq trans h4 (steps_seq trans h5 (steps_seq trans h6 (steps_seq trans h7 (steps_seq trans h8 (steps_seq trans h9 (h10)))))))))))

/-- Changed. PR 93 `rule_defect0`: CfgR L (10 · D 0 · 1 (11)^m 0 · R) reaches CfgJ L (1111 · D m · 1 · R) = CfgJ L (D (m+2) · 1 · R) for T3; here CfgJ L (D (m+1) · 101 · R). -/
theorem pr93_defect0 (m : Nat) (L R : Tape) :
    steps (20 * m + 76) ⟨L, cons false (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons false (cons true (rep (m) [true, true] (cons false (R)))))))))))), .A⟩ = some ⟨L, cons false (cons false (cons false (cons true (cons true (cons true (rep (m) [true, true] (cons false (cons false (cons true (cons false (cons true (R)))))))))))), .B⟩ := by
  have hn : 23 + (0 + ((m) * 8 + (12 + ((m) * 2 + (22 + (0 + ((m) * 8 + (12 + ((m) * 2 + (7)))))))))) = 20 * m + 76 := by omega
  have h0 : steps 23 ⟨L, cons false (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons false (cons true (rep (m) [true, true] (cons false (R)))))))))))), .A⟩ = some ⟨cons false (cons true (cons true (cons false (cons false (cons true (cons true (cons false (cons true (L))))))))), cons true (rep (m) [true, true] (cons false (R))), .D⟩ := rfl
  have h1 : steps 0 ⟨cons false (cons true (cons true (cons false (cons false (cons true (cons true (cons false (cons true (L))))))))), cons true (rep (m) [true, true] (cons false (R))), .D⟩ = some ⟨cons false (cons true (cons true (cons false (cons false (cons true (cons true (cons false (cons true (L))))))))), rep (m) [true, true] (cons true (cons false (R))), .D⟩ := by
    simp only [steps_zero, show cons true (rep (m) [true, true] (cons false (R))) = rep (m) [true, true] (cons true (cons false (R))) from
      rep_rotate (m) [true] [true, true] [true, true] rfl (cons false (R))]
  have c2 : ∀ L R : Tape, steps 8 ⟨app [false, true] L, app [true, true] R, .D⟩ = some ⟨app [false, true] (app [true, false] L), R, .D⟩ := fun _ _ => rfl
  have h2 : steps ((m) * 8) ⟨cons false (cons true (cons true (cons false (cons false (cons true (cons true (cons false (cons true (L))))))))), rep (m) [true, true] (cons true (cons false (R))), .D⟩ = some ⟨cons false (cons true (rep (m) [true, false] (cons true (cons false (cons false (cons true (cons true (cons false (cons true (L)))))))))), cons true (cons false (R)), .D⟩ :=
    cross_r trans c2 (m) (cons true (cons false (cons false (cons true (cons true (cons false (cons true (L)))))))) (cons true (cons false (R)))
  have h3 : steps 12 ⟨cons false (cons true (rep (m) [true, false] (cons true (cons false (cons false (cons true (cons true (cons false (cons true (L)))))))))), cons true (cons false (R)), .D⟩ = some ⟨rep (m) [true, false] (cons true (cons false (cons false (cons true (cons true (cons false (cons true (L)))))))), cons false (cons false (cons false (cons true (R)))), .B⟩ := rfl
  have c4 : ∀ L R : Tape, steps 2 ⟨app [true, false] L, app [false] R, .B⟩ = some ⟨L, app [false] (app [true, true] R), .B⟩ := fun _ _ => rfl
  have h4 : steps ((m) * 2) ⟨rep (m) [true, false] (cons true (cons false (cons false (cons true (cons true (cons false (cons true (L)))))))), cons false (cons false (cons false (cons true (R)))), .B⟩ = some ⟨cons true (cons false (cons false (cons true (cons true (cons false (cons true (L))))))), cons false (rep (m) [true, true] (cons false (cons false (cons true (R))))), .B⟩ :=
    cross_l trans c4 (m) (cons true (cons false (cons false (cons true (cons true (cons false (cons true (L)))))))) (cons false (cons false (cons true (R))))
  have h5 : steps 22 ⟨cons true (cons false (cons false (cons true (cons true (cons false (cons true (L))))))), cons false (rep (m) [true, true] (cons false (cons false (cons true (R))))), .B⟩ = some ⟨cons false (cons true (cons true (cons false (cons true (cons true (cons false (L))))))), cons true (rep (m) [true, true] (cons false (cons false (cons true (R))))), .D⟩ := rfl
  have h6 : steps 0 ⟨cons false (cons true (cons true (cons false (cons true (cons true (cons false (L))))))), cons true (rep (m) [true, true] (cons false (cons false (cons true (R))))), .D⟩ = some ⟨cons false (cons true (cons true (cons false (cons true (cons true (cons false (L))))))), rep (m) [true, true] (cons true (cons false (cons false (cons true (R))))), .D⟩ := by
    simp only [steps_zero, show cons true (rep (m) [true, true] (cons false (cons false (cons true (R))))) = rep (m) [true, true] (cons true (cons false (cons false (cons true (R))))) from
      rep_rotate (m) [true] [true, true] [true, true] rfl (cons false (cons false (cons true (R))))]
  have c7 : ∀ L R : Tape, steps 8 ⟨app [false, true] L, app [true, true] R, .D⟩ = some ⟨app [false, true] (app [true, false] L), R, .D⟩ := fun _ _ => rfl
  have h7 : steps ((m) * 8) ⟨cons false (cons true (cons true (cons false (cons true (cons true (cons false (L))))))), rep (m) [true, true] (cons true (cons false (cons false (cons true (R))))), .D⟩ = some ⟨cons false (cons true (rep (m) [true, false] (cons true (cons false (cons true (cons true (cons false (L)))))))), cons true (cons false (cons false (cons true (R)))), .D⟩ :=
    cross_r trans c7 (m) (cons true (cons false (cons true (cons true (cons false (L)))))) (cons true (cons false (cons false (cons true (R)))))
  have h8 : steps 12 ⟨cons false (cons true (rep (m) [true, false] (cons true (cons false (cons true (cons true (cons false (L)))))))), cons true (cons false (cons false (cons true (R)))), .D⟩ = some ⟨rep (m) [true, false] (cons true (cons false (cons true (cons true (cons false (L)))))), cons false (cons false (cons false (cons true (cons false (cons true (R)))))), .B⟩ := rfl
  have c9 : ∀ L R : Tape, steps 2 ⟨app [true, false] L, app [false] R, .B⟩ = some ⟨L, app [false] (app [true, true] R), .B⟩ := fun _ _ => rfl
  have h9 : steps ((m) * 2) ⟨rep (m) [true, false] (cons true (cons false (cons true (cons true (cons false (L)))))), cons false (cons false (cons false (cons true (cons false (cons true (R)))))), .B⟩ = some ⟨cons true (cons false (cons true (cons true (cons false (L))))), cons false (rep (m) [true, true] (cons false (cons false (cons true (cons false (cons true (R))))))), .B⟩ :=
    cross_l trans c9 (m) (cons true (cons false (cons true (cons true (cons false (L)))))) (cons false (cons false (cons true (cons false (cons true (R))))))
  have h10 : steps 7 ⟨cons true (cons false (cons true (cons true (cons false (L))))), cons false (rep (m) [true, true] (cons false (cons false (cons true (cons false (cons true (R))))))), .B⟩ = some ⟨L, cons false (cons false (cons false (cons true (cons true (cons true (rep (m) [true, true] (cons false (cons false (cons true (cons false (cons true (R)))))))))))), .B⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (steps_seq trans h4 (steps_seq trans h5 (steps_seq trans h6 (steps_seq trans h7 (steps_seq trans h8 (steps_seq trans h9 (h10)))))))))))

/-- Changed. PR 93 `rule_finishP`: CfgL (L · S 0 · 01 · (10)^(b+1)) R reaches CfgJ L (D (b+1) · R) for T3; here CfgJ L (D b · 10 · R). -/
theorem pr93_finishP (b : Nat) (L R : Tape) :
    steps (12 * b + 32) ⟨cons false (rep (b) [true, false] (cons false (cons true (cons true (cons false (cons true (L))))))), cons true (cons true (R)), .B⟩ = some ⟨L, cons false (cons false (cons false (cons true (rep (b) [true, true] (cons false (cons false (cons true (cons false (R))))))))), .B⟩ := by
  have hn : 3 + ((b) * 2 + (12 + (0 + ((b) * 8 + (12 + ((b) * 2 + (5))))))) = 12 * b + 32 := by omega
  have h0 : steps 3 ⟨cons false (rep (b) [true, false] (cons false (cons true (cons true (cons false (cons true (L))))))), cons true (cons true (R)), .B⟩ = some ⟨rep (b) [true, false] (cons false (cons true (cons true (cons false (cons true (L)))))), cons false (cons false (cons false (R))), .B⟩ := rfl
  have c1 : ∀ L R : Tape, steps 2 ⟨app [true, false] L, app [false] R, .B⟩ = some ⟨L, app [false] (app [true, true] R), .B⟩ := fun _ _ => rfl
  have h1 : steps ((b) * 2) ⟨rep (b) [true, false] (cons false (cons true (cons true (cons false (cons true (L)))))), cons false (cons false (cons false (R))), .B⟩ = some ⟨cons false (cons true (cons true (cons false (cons true (L))))), cons false (rep (b) [true, true] (cons false (cons false (R)))), .B⟩ :=
    cross_l trans c1 (b) (cons false (cons true (cons true (cons false (cons true (L)))))) (cons false (cons false (R)))
  have h2 : steps 12 ⟨cons false (cons true (cons true (cons false (cons true (L))))), cons false (rep (b) [true, true] (cons false (cons false (R)))), .B⟩ = some ⟨cons false (cons true (cons true (cons true (cons false (L))))), cons true (rep (b) [true, true] (cons false (cons false (R)))), .D⟩ := rfl
  have h3 : steps 0 ⟨cons false (cons true (cons true (cons true (cons false (L))))), cons true (rep (b) [true, true] (cons false (cons false (R)))), .D⟩ = some ⟨cons false (cons true (cons true (cons true (cons false (L))))), rep (b) [true, true] (cons true (cons false (cons false (R)))), .D⟩ := by
    simp only [steps_zero, show cons true (rep (b) [true, true] (cons false (cons false (R)))) = rep (b) [true, true] (cons true (cons false (cons false (R)))) from
      rep_rotate (b) [true] [true, true] [true, true] rfl (cons false (cons false (R)))]
  have c4 : ∀ L R : Tape, steps 8 ⟨app [false, true] L, app [true, true] R, .D⟩ = some ⟨app [false, true] (app [true, false] L), R, .D⟩ := fun _ _ => rfl
  have h4 : steps ((b) * 8) ⟨cons false (cons true (cons true (cons true (cons false (L))))), rep (b) [true, true] (cons true (cons false (cons false (R)))), .D⟩ = some ⟨cons false (cons true (rep (b) [true, false] (cons true (cons true (cons false (L)))))), cons true (cons false (cons false (R))), .D⟩ :=
    cross_r trans c4 (b) (cons true (cons true (cons false (L)))) (cons true (cons false (cons false (R))))
  have h5 : steps 12 ⟨cons false (cons true (rep (b) [true, false] (cons true (cons true (cons false (L)))))), cons true (cons false (cons false (R))), .D⟩ = some ⟨rep (b) [true, false] (cons true (cons true (cons false (L)))), cons false (cons false (cons false (cons true (cons false (R))))), .B⟩ := rfl
  have c6 : ∀ L R : Tape, steps 2 ⟨app [true, false] L, app [false] R, .B⟩ = some ⟨L, app [false] (app [true, true] R), .B⟩ := fun _ _ => rfl
  have h6 : steps ((b) * 2) ⟨rep (b) [true, false] (cons true (cons true (cons false (L)))), cons false (cons false (cons false (cons true (cons false (R))))), .B⟩ = some ⟨cons true (cons true (cons false (L))), cons false (rep (b) [true, true] (cons false (cons false (cons true (cons false (R)))))), .B⟩ :=
    cross_l trans c6 (b) (cons true (cons true (cons false (L)))) (cons false (cons false (cons true (cons false (R)))))
  have h7 : steps 5 ⟨cons true (cons true (cons false (L))), cons false (rep (b) [true, true] (cons false (cons false (cons true (cons false (R)))))), .B⟩ = some ⟨L, cons false (cons false (cons false (cons true (rep (b) [true, true] (cons false (cons false (cons true (cons false (R))))))))), .B⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (steps_seq trans h4 (steps_seq trans h5 (steps_seq trans h6 (h7))))))))

end H99431
