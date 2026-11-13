import Machine

/-! # The gap counter of 1RB0RF_1LC1RF_1RA0LD_0LC0RE_1LD---_0RC0RD

Write the tape as *gap words* `0^g 1`.  At the sample points the configuration is

    0^∞ 1 1 1 C> 0 0 1 [0^g1 1] [0^g2 1] ... [0^gk 1] 0^∞          (`cfg [g1, ..., gk]`)

so a state is just the list of gaps.  Most gaps are 3 (blocks `(0001)^m`).  One *bounce* (C sweeps right, turns at
the first gap that is not 3 or 5, and the head comes back to the left end) rewrites the list:

* the sweep passes gaps 3 and 5, the pairs (0, 1) and (2, 3) and the run (0, 0, 3, 3) (`Tok`, `c_*`);
* it stops at the first other pattern (`stopM`, `s_*`) and turns back in the *normal* state `1 1 1 D> 0` or the
  *special* state `1 1 1 C> 1 0 1`;
* going back, a 5 becomes 1 1 1 and the passed (0, 1) and (0, 0, 3, 3) are rewritten, the state switching between
  normal and special (`retStep`, `n_*`, `p_*`);
* at the left end a normal return puts a 3 in front of the list, a special one 1 1 1 (`n_end`, `p_end`).

Two stops halt the machine: the gaps (0, 0, 0) and (4, 0) (`h_000`, `h_40`).

The pieces are written by `bbtools.symtm.prove` (`py/counter.py`); the definitions and the inductions are by hand. -/

namespace H58767

open TM

theorem c_blk (m : Nat) (L R : Tape) :
    steps (4 * m) ⟨L, cons false (cons false (cons true (rep (m) [false, false, false, true] (R)))), .C⟩ = some ⟨rep (m) [false, true, true, true] (L), cons false (cons false (cons true (R))), .C⟩ := by
  have hn : 0 + ((m) * 4) = 4 * m := by omega
  have h0 : steps 0 ⟨L, cons false (cons false (cons true (rep (m) [false, false, false, true] (R)))), .C⟩ = some ⟨L, rep (m) [false, false, true, false] (cons false (cons false (cons true (R)))), .C⟩ := by
    simp only [steps_zero, show cons false (cons false (cons true (rep (m) [false, false, false, true] (R)))) = rep (m) [false, false, true, false] (cons false (cons false (cons true (R)))) from
      rep_rotate (m) [false, false, true] [false, false, false, true] [false, false, true, false] rfl (R)]
  have c1 : ∀ L R : Tape, steps 4 ⟨app [] L, app [false, false, true, false] R, .C⟩ = some ⟨app [] (app [false, true, true, true] L), R, .C⟩ := fun _ _ => rfl
  have h1 : steps ((m) * 4) ⟨L, rep (m) [false, false, true, false] (cons false (cons false (cons true (R)))), .C⟩ = some ⟨rep (m) [false, true, true, true] (L), cons false (cons false (cons true (R))), .C⟩ :=
    cross_r trans c1 (m) (L) (cons false (cons false (cons true (R))))
  exact steps_congr trans hn (steps_seq trans h0 (h1))

theorem c_five (L R : Tape) :
    steps (16) ⟨L, cons false (cons false (cons true (cons false (cons false (cons false (cons false (cons false (cons true (R))))))))), .C⟩ = some ⟨cons true (cons true (cons true (cons true (cons true (cons true (L)))))), cons false (cons false (cons true (R))), .C⟩ := by
  have hn : 16 = 16 := by omega
  have h0 : steps 16 ⟨L, cons false (cons false (cons true (cons false (cons false (cons false (cons false (cons false (cons true (R))))))))), .C⟩ = some ⟨cons true (cons true (cons true (cons true (cons true (cons true (L)))))), cons false (cons false (cons true (R))), .C⟩ := rfl
  exact steps_congr trans hn (h0)

theorem c_merge (L R : Tape) :
    steps (5) ⟨L, cons false (cons false (cons true (cons true (cons false (cons true (R)))))), .C⟩ = some ⟨cons true (cons true (cons true (L))), cons false (cons false (cons true (R))), .C⟩ := by
  have hn : 5 = 5 := by omega
  have h0 : steps 5 ⟨L, cons false (cons false (cons true (cons true (cons false (cons true (R)))))), .C⟩ = some ⟨cons true (cons true (cons true (L))), cons false (cons false (cons true (R))), .C⟩ := rfl
  exact steps_congr trans hn (h0)

theorem c_zz (L R : Tape) :
    steps (14) ⟨L, cons false (cons false (cons true (cons true (cons true (cons false (cons false (cons false (cons true (cons false (cons false (cons false (cons true (R))))))))))))), .C⟩ = some ⟨cons false (cons false (cons true (cons false (cons true (cons true (cons true (cons true (cons true (cons true (L)))))))))), cons false (cons false (cons true (R))), .C⟩ := by
  have hn : 14 = 14 := by omega
  have h0 : steps 14 ⟨L, cons false (cons false (cons true (cons true (cons true (cons false (cons false (cons false (cons true (cons false (cons false (cons false (cons true (R))))))))))))), .C⟩ = some ⟨cons false (cons false (cons true (cons false (cons true (cons true (cons true (cons true (cons true (cons true (L)))))))))), cons false (cons false (cons true (R))), .C⟩ := rfl
  exact steps_congr trans hn (h0)

theorem c_23 (L R : Tape) :
    steps (7) ⟨L, cons false (cons false (cons true (cons false (cons false (cons true (cons false (cons false (cons false (cons true (R)))))))))), .C⟩ = some ⟨cons false (cons false (cons true (cons false (cons true (cons true (cons true (L))))))), cons false (cons false (cons true (R))), .C⟩ := by
  have hn : 7 = 7 := by omega
  have h0 : steps 7 ⟨L, cons false (cons false (cons true (cons false (cons false (cons true (cons false (cons false (cons false (cons true (R)))))))))), .C⟩ = some ⟨cons false (cons false (cons true (cons false (cons true (cons true (cons true (L))))))), cons false (cons false (cons true (R))), .C⟩ := rfl
  exact steps_congr trans hn (h0)

theorem s_1 (L R : Tape) :
    steps (5) ⟨L, cons false (cons false (cons true (cons false (cons true (R))))), .C⟩ = some ⟨cons true (cons true (cons true (L))), cons false (cons false (R)), .D⟩ := by
  have hn : 5 = 5 := by omega
  have h0 : steps 5 ⟨L, cons false (cons false (cons true (cons false (cons true (R))))), .C⟩ = some ⟨cons true (cons true (cons true (L))), cons false (cons false (R)), .D⟩ := rfl
  exact steps_congr trans hn (h0)

theorem s_21 (L R : Tape) :
    steps (17) ⟨L, cons false (cons false (cons true (cons false (cons false (cons true (cons false (cons true (R)))))))), .C⟩ = some ⟨cons true (cons true (cons true (L))), cons false (cons false (cons false (cons true (cons true (R))))), .D⟩ := by
  have hn : 17 = 17 := by omega
  have h0 : steps 17 ⟨L, cons false (cons false (cons true (cons false (cons false (cons true (cons false (cons true (R)))))))), .C⟩ = some ⟨cons true (cons true (cons true (L))), cons false (cons false (cons false (cons true (cons true (R))))), .D⟩ := rfl
  exact steps_congr trans hn (h0)

theorem s_2e (L : Tape) :
    steps (33) ⟨L, cons false (cons false (cons true (cons false (cons false (cons true (blank)))))), .C⟩ = some ⟨cons true (cons true (cons true (L))), cons false (cons false (cons false (cons false (cons false (cons true (cons false (cons true (cons true (blank))))))))), .D⟩ := by
  have hn : 33 = 33 := by omega
  have h0 : steps 33 ⟨L, cons false (cons false (cons true (cons false (cons false (cons true (blank)))))), .C⟩ = some ⟨cons true (cons true (cons true (L))), cons false (cons false (cons false (cons false (cons false (cons true (cons false (cons true (cons true (blank))))))))), .D⟩ := rfl
  exact steps_congr trans hn (h0)

theorem s_0x (L R : Tape) :
    steps (11) ⟨L, cons false (cons false (cons true (cons true (cons false (cons false (R)))))), .C⟩ = some ⟨cons true (cons true (cons true (L))), cons false (cons true (cons true (R))), .D⟩ := by
  have hn : 11 = 11 := by omega
  have h0 : steps 11 ⟨L, cons false (cons false (cons true (cons true (cons false (cons false (R)))))), .C⟩ = some ⟨cons true (cons true (cons true (L))), cons false (cons true (cons true (R))), .D⟩ := rfl
  exact steps_congr trans hn (h0)

theorem s_0e (L : Tape) :
    steps (11) ⟨L, cons false (cons false (cons true (cons true (blank)))), .C⟩ = some ⟨cons true (cons true (cons true (L))), cons false (cons true (cons true (blank))), .D⟩ := by
  have hn : 11 = 11 := by omega
  have h0 : steps 11 ⟨L, cons false (cons false (cons true (cons true (blank)))), .C⟩ = some ⟨cons true (cons true (cons true (L))), cons false (cons true (cons true (blank))), .D⟩ := rfl
  exact steps_congr trans hn (h0)

theorem s_41x (L R : Tape) :
    steps (41) ⟨L, cons false (cons false (cons true (cons false (cons false (cons false (cons false (cons true (cons false (cons true (cons false (cons false (R)))))))))))), .C⟩ = some ⟨cons true (cons true (cons true (L))), cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons true (R))))))))), .D⟩ := by
  have hn : 41 = 41 := by omega
  have h0 : steps 41 ⟨L, cons false (cons false (cons true (cons false (cons false (cons false (cons false (cons true (cons false (cons true (cons false (cons false (R)))))))))))), .C⟩ = some ⟨cons true (cons true (cons true (L))), cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons true (R))))))))), .D⟩ := rfl
  exact steps_congr trans hn (h0)

theorem s_7x (L R : Tape) :
    steps (27) ⟨L, cons false (cons false (cons true (cons false (cons false (cons false (cons false (cons false (cons false (cons false (R)))))))))), .C⟩ = some ⟨cons true (cons true (cons true (L))), cons true (cons false (cons true (cons false (cons true (cons true (cons false (R))))))), .C⟩ := by
  have hn : 27 = 27 := by omega
  have h0 : steps 27 ⟨L, cons false (cons false (cons true (cons false (cons false (cons false (cons false (cons false (cons false (cons false (R)))))))))), .C⟩ = some ⟨cons true (cons true (cons true (L))), cons true (cons false (cons true (cons false (cons true (cons true (cons false (R))))))), .C⟩ := rfl
  exact steps_congr trans hn (h0)

theorem s_4e (L : Tape) :
    steps (57) ⟨L, cons false (cons false (cons true (cons false (cons false (cons false (cons false (cons true (blank)))))))), .C⟩ = some ⟨cons true (cons true (cons true (L))), cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons true (blank)))))))))))), .C⟩ := by
  have hn : 57 = 57 := by omega
  have h0 : steps 57 ⟨L, cons false (cons false (cons true (cons false (cons false (cons false (cons false (cons true (blank)))))))), .C⟩ = some ⟨cons true (cons true (cons true (L))), cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons true (blank)))))))))))), .C⟩ := rfl
  exact steps_congr trans hn (h0)

theorem s_6e (L : Tape) :
    steps (27) ⟨L, cons false (cons false (cons true (cons false (cons false (cons false (cons false (cons false (cons false (cons true (blank)))))))))), .C⟩ = some ⟨cons true (cons true (cons true (L))), cons true (cons false (cons true (cons false (cons true (cons true (cons true (blank))))))), .C⟩ := by
  have hn : 27 = 27 := by omega
  have h0 : steps 27 ⟨L, cons false (cons false (cons true (cons false (cons false (cons false (cons false (cons false (cons false (cons true (blank)))))))))), .C⟩ = some ⟨cons true (cons true (cons true (L))), cons true (cons false (cons true (cons false (cons true (cons true (cons true (blank))))))), .C⟩ := rfl
  exact steps_congr trans hn (h0)

theorem s_20e (L : Tape) :
    steps (45) ⟨L, cons false (cons false (cons true (cons false (cons false (cons true (cons true (blank))))))), .C⟩ = some ⟨cons true (cons true (cons true (L))), cons true (cons false (cons true (cons false (cons false (cons false (cons true (cons true (blank)))))))), .C⟩ := by
  have hn : 45 = 45 := by omega
  have h0 : steps 45 ⟨L, cons false (cons false (cons true (cons false (cons false (cons true (cons true (blank))))))), .C⟩ = some ⟨cons true (cons true (cons true (L))), cons true (cons false (cons true (cons false (cons false (cons false (cons true (cons true (blank)))))))), .C⟩ := rfl
  exact steps_congr trans hn (h0)

theorem n_blk (m : Nat) (L R : Tape) :
    steps (6 * m) ⟨cons true (cons true (cons true (rep (m) [false, true, true, true] (L)))), cons false (R), .D⟩ = some ⟨cons true (cons true (cons true (L))), cons false (rep (m) [false, false, true, false] (R)), .D⟩ := by
  have hn : 0 + ((m) * 6) = 6 * m := by omega
  have h0 : steps 0 ⟨cons true (cons true (cons true (rep (m) [false, true, true, true] (L)))), cons false (R), .D⟩ = some ⟨rep (m) [true, true, true, false] (cons true (cons true (cons true (L)))), cons false (R), .D⟩ := by
    simp only [steps_zero, show cons true (cons true (cons true (rep (m) [false, true, true, true] (L)))) = rep (m) [true, true, true, false] (cons true (cons true (cons true (L)))) from
      rep_rotate (m) [true, true, true] [false, true, true, true] [true, true, true, false] rfl (L)]
  have c1 : ∀ L R : Tape, steps 6 ⟨app [true, true, true, false] L, app [false] R, .D⟩ = some ⟨L, app [false] (app [false, false, true, false] R), .D⟩ := fun _ _ => rfl
  have h1 : steps ((m) * 6) ⟨rep (m) [true, true, true, false] (cons true (cons true (cons true (L)))), cons false (R), .D⟩ = some ⟨cons true (cons true (cons true (L))), cons false (rep (m) [false, false, true, false] (R)), .D⟩ :=
    cross_l trans c1 (m) (cons true (cons true (cons true (L)))) (R)
  exact steps_congr trans hn (steps_seq trans h0 (h1))

theorem n_five (L R : Tape) :
    steps (12) ⟨cons true (cons true (cons true (cons true (cons true (cons true (cons true (cons true (cons true (L))))))))), cons false (R), .D⟩ = some ⟨cons true (cons true (cons true (L))), cons false (cons true (cons false (cons true (cons false (cons true (cons false (R))))))), .D⟩ := by
  have hn : 12 = 12 := by omega
  have h0 : steps 12 ⟨cons true (cons true (cons true (cons true (cons true (cons true (cons true (cons true (cons true (L))))))))), cons false (R), .D⟩ = some ⟨cons true (cons true (cons true (L))), cons false (cons true (cons false (cons true (cons false (cons true (cons false (R))))))), .D⟩ := rfl
  exact steps_congr trans hn (h0)

theorem n_merge (L R : Tape) :
    steps (5) ⟨cons true (cons true (cons true (cons true (cons true (cons true (L)))))), cons false (R), .D⟩ = some ⟨cons true (cons true (cons true (L))), cons true (cons false (cons true (cons false (R)))), .C⟩ := by
  have hn : 5 = 5 := by omega
  have h0 : steps 5 ⟨cons true (cons true (cons true (cons true (cons true (cons true (L)))))), cons false (R), .D⟩ = some ⟨cons true (cons true (cons true (L))), cons true (cons false (cons true (cons false (R)))), .C⟩ := rfl
  exact steps_congr trans hn (h0)

theorem n_zz (L R : Tape) :
    steps (20) ⟨cons true (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons true (cons true (cons true (cons true (cons true (L))))))))))))), cons false (R), .D⟩ = some ⟨cons true (cons true (cons true (L))), cons true (cons false (cons true (cons false (cons false (cons false (cons true (cons true (cons false (cons true (cons false (R))))))))))), .C⟩ := by
  have hn : 20 = 20 := by omega
  have h0 : steps 20 ⟨cons true (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons true (cons true (cons true (cons true (cons true (L))))))))))))), cons false (R), .D⟩ = some ⟨cons true (cons true (cons true (L))), cons true (cons false (cons true (cons false (cons false (cons false (cons true (cons true (cons false (cons true (cons false (R))))))))))), .C⟩ := rfl
  exact steps_congr trans hn (h0)

theorem n_23 (L R : Tape) :
    steps (15) ⟨cons true (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons true (cons true (L)))))))))), cons false (R), .D⟩ = some ⟨cons true (cons true (cons true (L))), cons false (cons false (cons false (cons true (cons true (cons false (cons true (cons false (R)))))))), .D⟩ := by
  have hn : 15 = 15 := by omega
  have h0 : steps 15 ⟨cons true (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons true (cons true (L)))))))))), cons false (R), .D⟩ = some ⟨cons true (cons true (cons true (L))), cons false (cons false (cons false (cons true (cons true (cons false (cons true (cons false (R)))))))), .D⟩ := rfl
  exact steps_congr trans hn (h0)

theorem n_end (R : Tape) :
    steps (37) ⟨cons true (cons true (cons true (cons true (cons true (cons true (blank)))))), cons false (R), .D⟩ = some ⟨cons true (cons true (cons true (blank))), cons false (cons false (cons true (cons false (cons false (cons false (cons true (cons false (R)))))))), .C⟩ := by
  have hn : 37 = 37 := by omega
  have h0 : steps 37 ⟨cons true (cons true (cons true (cons true (cons true (cons true (blank)))))), cons false (R), .D⟩ = some ⟨cons true (cons true (cons true (blank))), cons false (cons false (cons true (cons false (cons false (cons false (cons true (cons false (R)))))))), .C⟩ := rfl
  exact steps_congr trans hn (h0)

theorem p_blk (L R : Tape) :
    steps (18) ⟨cons true (cons true (cons true (cons false (cons true (cons true (cons true (L))))))), cons true (cons false (cons true (R))), .C⟩ = some ⟨cons true (cons true (cons true (L))), cons true (cons false (cons true (cons false (cons false (cons false (cons true (R))))))), .C⟩ := by
  have hn : 18 = 18 := by omega
  have h0 : steps 18 ⟨cons true (cons true (cons true (cons false (cons true (cons true (cons true (L))))))), cons true (cons false (cons true (R))), .C⟩ = some ⟨cons true (cons true (cons true (L))), cons true (cons false (cons true (cons false (cons false (cons false (cons true (R))))))), .C⟩ := rfl
  exact steps_congr trans hn (h0)

theorem p_five (L R : Tape) :
    steps (12) ⟨cons true (cons true (cons true (cons true (cons true (cons true (cons true (cons true (cons true (L))))))))), cons true (cons false (cons true (R))), .C⟩ = some ⟨cons true (cons true (cons true (L))), cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (R))))))))), .C⟩ := by
  have hn : 12 = 12 := by omega
  have h0 : steps 12 ⟨cons true (cons true (cons true (cons true (cons true (cons true (cons true (cons true (cons true (L))))))))), cons true (cons false (cons true (R))), .C⟩ = some ⟨cons true (cons true (cons true (L))), cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (R))))))))), .C⟩ := rfl
  exact steps_congr trans hn (h0)

theorem p_merge (L R : Tape) :
    steps (7) ⟨cons true (cons true (cons true (cons true (cons true (cons true (L)))))), cons true (cons false (cons true (R))), .C⟩ = some ⟨cons true (cons true (cons true (L))), cons false (cons true (cons false (cons true (cons false (cons true (R)))))), .D⟩ := by
  have hn : 7 = 7 := by omega
  have h0 : steps 7 ⟨cons true (cons true (cons true (cons true (cons true (cons true (L)))))), cons true (cons false (cons true (R))), .C⟩ = some ⟨cons true (cons true (cons true (L))), cons false (cons true (cons false (cons true (cons false (cons true (R)))))), .D⟩ := rfl
  exact steps_congr trans hn (h0)

theorem p_zz (L R : Tape) :
    steps (26) ⟨cons true (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons true (cons true (cons true (cons true (cons true (L))))))))))))), cons true (cons false (cons true (R))), .C⟩ = some ⟨cons true (cons true (cons true (L))), cons true (cons false (cons true (cons false (cons false (cons false (cons false (cons false (cons true (cons false (cons false (cons false (cons true (R))))))))))))), .C⟩ := by
  have hn : 26 = 26 := by omega
  have h0 : steps 26 ⟨cons true (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons true (cons true (cons true (cons true (cons true (L))))))))))))), cons true (cons false (cons true (R))), .C⟩ = some ⟨cons true (cons true (cons true (L))), cons true (cons false (cons true (cons false (cons false (cons false (cons false (cons false (cons true (cons false (cons false (cons false (cons true (R))))))))))))), .C⟩ := rfl
  exact steps_congr trans hn (h0)

theorem p_23 (L R : Tape) :
    steps (21) ⟨cons true (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons true (cons true (L)))))))))), cons true (cons false (cons true (R))), .C⟩ = some ⟨cons true (cons true (cons true (L))), cons false (cons false (cons false (cons false (cons false (cons true (cons false (cons false (cons false (cons true (R)))))))))), .D⟩ := by
  have hn : 21 = 21 := by omega
  have h0 : steps 21 ⟨cons true (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons true (cons true (L)))))))))), cons true (cons false (cons true (R))), .C⟩ = some ⟨cons true (cons true (cons true (L))), cons false (cons false (cons false (cons false (cons false (cons true (cons false (cons false (cons false (cons true (R)))))))))), .D⟩ := rfl
  exact steps_congr trans hn (h0)

theorem p_end (R : Tape) :
    steps (26) ⟨cons true (cons true (cons true (cons true (cons true (cons true (blank)))))), cons true (cons false (cons true (R))), .C⟩ = some ⟨cons true (cons true (cons true (blank))), cons false (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (R))))))))), .C⟩ := by
  have hn : 26 = 26 := by omega
  have h0 : steps 26 ⟨cons true (cons true (cons true (cons true (cons true (cons true (blank)))))), cons true (cons false (cons true (R))), .C⟩ = some ⟨cons true (cons true (cons true (blank))), cons false (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (R))))))))), .C⟩ := rfl
  exact steps_congr trans hn (h0)

theorem h_000 (L R : Tape) :
    steps (5) ⟨L, cons false (cons false (cons true (cons true (cons true (cons true (R)))))), .C⟩ = some ⟨cons false (cons false (cons true (cons true (cons true (L))))), cons true (R), .E⟩ := by
  have hn : 5 = 5 := by omega
  have h0 : steps 5 ⟨L, cons false (cons false (cons true (cons true (cons true (cons true (R)))))), .C⟩ = some ⟨cons false (cons false (cons true (cons true (cons true (L))))), cons true (R), .E⟩ := rfl
  exact steps_congr trans hn (h0)

theorem h_40 (L R : Tape) :
    steps (16) ⟨L, cons false (cons false (cons true (cons false (cons false (cons false (cons false (cons true (cons true (R))))))))), .C⟩ = some ⟨cons false (cons false (cons true (cons true (cons true (cons true (cons true (cons true (L)))))))), cons true (R), .E⟩ := by
  have hn : 16 = 16 := by omega
  have h0 : steps 16 ⟨L, cons false (cons false (cons true (cons false (cons false (cons false (cons false (cons true (cons true (R))))))))), .C⟩ = some ⟨cons false (cons false (cons true (cons true (cons true (cons true (cons true (cons true (L)))))))), cons true (R), .E⟩ := rfl
  exact steps_congr trans hn (h0)


/-- The gap word `0^g 1` in front of `R`. -/
def gw (g : Nat) (R : Tape) : Tape := rep g [false] (cons true R)

/-- A list of gap words in front of `R`. -/
def gws : List Nat → Tape → Tape
  | [], R => R
  | g :: G, R => gw g (gws G R)

theorem gws_append (G H : List Nat) (R : Tape) : gws (G ++ H) R = gws G (gws H R) := by
  induction G with
  | nil => rfl
  | cons g G ih => show gw g (gws (G ++ H) R) = gw g (gws G (gws H R)); rw [ih]

/-- `1 1 1` and blank tape to the left of the head. -/
abbrev L3 : Tape := cons true (cons true (cons true blank))

/-- The configuration of a gap list: `0^∞ 1 1 1 C> 0 0 1 [gap words] 0^∞`. -/
def cfg (G : List Nat) : Config := ⟨L3, gw 2 (gws G blank), .C⟩

/-- What the right sweep passes. -/
inductive Tok where
  | blk | five | merge | zz | t23
  deriving DecidableEq, Repr

/-- The gaps a token stands for. -/
def Tok.gaps : Tok → List Nat
  | .blk => [3]
  | .five => [5]
  | .merge => [0, 1]
  | .zz => [0, 0, 3, 3]
  | .t23 => [2, 3]

/-- The left tape after the sweep has passed a token (`c_*`). -/
def Tok.left : Tok → Tape → Tape
  | .blk, L => rep 1 [false, true, true, true] L
  | .five, L => cons true (cons true (cons true (cons true (cons true (cons true L)))))
  | .merge, L => cons true (cons true (cons true L))
  | .zz, L => cons false (cons false (cons true (cons false (cons true (cons true (cons true (cons true (cons true
      (cons true L)))))))))
  | .t23, L => cons false (cons false (cons true (cons false (cons true (cons true (cons true L))))))

/-- The left tape after sweeping the tokens (the first one deepest). -/
def sweepL : List Tok → Tape → Tape
  | [], L => L
  | t :: ts, L => sweepL ts (t.left L)

/-- The left tape with the tokens in return order (the first one outermost). -/
def pathL : List Tok → Tape → Tape
  | [], L => L
  | t :: ts, L => t.left (pathL ts L)

theorem pathL_append (xs ys : List Tok) (L : Tape) : pathL (xs ++ ys) L = pathL xs (pathL ys L) := by
  induction xs with
  | nil => rfl
  | cons t xs ih => show t.left (pathL (xs ++ ys) L) = t.left (pathL xs (pathL ys L)); rw [ih]

theorem sweepL_eq (ts : List Tok) : ∀ L, sweepL ts L = pathL ts.reverse L := by
  induction ts with
  | nil => intro L; rfl
  | cons t ts ih =>
    intro L
    show sweepL ts (t.left L) = _
    rw [ih, List.reverse_cons, pathL_append]; rfl

/-- The sweep passes one token. -/
theorem tok_sweep (t : Tok) (L : Tape) (H : List Nat) (S : Tape) :
    ∃ n, steps n ⟨L, gw 2 (gws (t.gaps ++ H) S), .C⟩ = some ⟨t.left L, gw 2 (gws H S), .C⟩ := by
  cases t
  · exact ⟨_, c_blk 1 L (gws H S)⟩
  · exact ⟨_, c_five L (gws H S)⟩
  · exact ⟨_, c_merge L (gws H S)⟩
  · exact ⟨_, c_zz L (gws H S)⟩
  · exact ⟨_, c_23 L (gws H S)⟩

/-- The return states: normal `1 1 1 D> [gaps]`, special `1 1 1 C> 1 [0 1] [gaps]`. -/
inductive Mode where
  | N | P
  deriving DecidableEq, Repr

def retCfg : Mode → Tape → List Nat → Tape → Config
  | .N, L, H, S => ⟨cons true (cons true (cons true L)), gws H S, .D⟩
  | .P, L, H, S => ⟨cons true (cons true (cons true L)), cons true (gws (1 :: H) S), .C⟩

/-- In the normal state the head reads the first bit of a gap word with a positive gap. -/
def good : Mode → List Nat → Prop
  | .N, g :: _ => 0 < g
  | .N, [] => False
  | .P, _ => True

/-- The return over one token. -/
def retStep : Tok → Mode → List Nat → Mode × List Nat
  | .blk, .N, H => (.N, 3 :: H)
  | .five, .N, H => (.N, 1 :: 1 :: 1 :: H)
  | .merge, .N, H => (.P, H)
  | .zz, .N, H => (.P, 3 :: 0 :: 1 :: H)
  | .blk, .P, H => (.P, 3 :: H)
  | .five, .P, H => (.P, 1 :: 1 :: 1 :: H)
  | .merge, .P, H => (.N, 1 :: 1 :: 1 :: H)
  | .zz, .P, H => (.P, 5 :: 3 :: H)
  | .t23, .N, H => (.N, 3 :: 0 :: 1 :: H)
  | .t23, .P, H => (.N, 5 :: 3 :: H)

theorem retStep_good (t : Tok) (m : Mode) (H : List Nat) : good (retStep t m H).1 (retStep t m H).2 := by
  cases t <;> cases m <;> simp [retStep, good]

theorem ret_one (t : Tok) (m : Mode) (L : Tape) (H : List Nat) (S : Tape) (hg : good m H) :
    ∃ n, steps n (retCfg m (t.left L) H S) = some (retCfg (retStep t m H).1 L (retStep t m H).2 S) := by
  cases m with
  | N =>
    rcases H with _ | ⟨g, H⟩
    · exact absurd hg id
    · rcases g with _ | g
      · exact absurd hg (Nat.lt_irrefl 0)
      · cases t
        · exact ⟨_, n_blk 1 L (gw g (gws H S))⟩
        · exact ⟨_, n_five L (gw g (gws H S))⟩
        · exact ⟨_, n_merge L (gw g (gws H S))⟩
        · exact ⟨_, n_zz L (gw g (gws H S))⟩
        · exact ⟨_, n_23 L (gw g (gws H S))⟩
  | P =>
    cases t
    · exact ⟨_, p_blk L (gws H S)⟩
    · exact ⟨_, p_five L (gws H S)⟩
    · exact ⟨_, p_merge L (gws H S)⟩
    · exact ⟨_, p_zz L (gws H S)⟩
    · exact ⟨_, p_23 L (gws H S)⟩

/-- The return over tokens, outermost first. -/
def retAll : List Tok → Mode → List Nat → Mode × List Nat
  | [], m, H => (m, H)
  | t :: ts, m, H => retAll ts (retStep t m H).1 (retStep t m H).2

theorem ret_all (ts : List Tok) : ∀ (m : Mode) (L : Tape) (H : List Nat) (S : Tape), good m H →
    (∃ n, steps n (retCfg m (pathL ts L) H S) = some (retCfg (retAll ts m H).1 L (retAll ts m H).2 S)) ∧
      good (retAll ts m H).1 (retAll ts m H).2 := by
  induction ts with
  | nil => intro m L H S hg; exact ⟨⟨0, rfl⟩, hg⟩
  | cons t ts ih =>
    intro m L H S hg
    obtain ⟨a, ha⟩ := ret_one t m (pathL ts L) H S hg
    obtain ⟨⟨b, hb⟩, hg'⟩ := ih (retStep t m H).1 L (retStep t m H).2 S (retStep_good t m H)
    exact ⟨⟨a + b, steps_seq trans ha hb⟩, hg'⟩

/-- The outcome of a stop. -/
inductive Stop where
  | ret (m : Mode) (H : List Nat)
  | halt

/-- The stops: the first pattern that is not a gap 3 or 5, the pair (0, 1) or the run (0, 0, 3, 3). -/
def stopM : List Nat → Option Stop
  | 1 :: x :: G => some (.ret .N ((x + 2) :: G))
  | 2 :: 1 :: G => some (.ret .N (3 :: 0 :: G))
  | [2] => some (.ret .N [5, 1, 0])
  | 0 :: (x + 2) :: G => some (.ret .N (1 :: 0 :: x :: G))
  | [0] => some (.ret .N [1, 0])
  | 4 :: 1 :: (x + 2) :: G => some (.ret .N (1 :: 1 :: 1 :: 1 :: 0 :: x :: G))
  | (x + 7) :: G => some (.ret .P (1 :: 0 :: (x + 1) :: G))
  | [4] => some (.ret .P [1, 1, 1, 1, 0])
  | [6] => some (.ret .P [1, 0, 0])
  | [2, 0] => some (.ret .P [3, 0])
  | 0 :: 0 :: 0 :: _ => some .halt
  | 4 :: 0 :: _ => some .halt
  | _ => none

theorem stop_ret (G : List Nat) (m : Mode) (H : List Nat) (h : stopM G = some (.ret m H)) (L : Tape) :
    (∃ n, steps n ⟨L, gw 2 (gws G blank), .C⟩ = some (retCfg m L H blank)) ∧ good m H := by
  unfold stopM at h
  split at h <;> (try cases h)
  · exact ⟨⟨_, s_1 L _⟩, by simp [good]⟩
  · exact ⟨⟨_, s_21 L _⟩, by simp [good]⟩
  · exact ⟨⟨_, s_2e L⟩, by simp [good]⟩
  · exact ⟨⟨_, s_0x L _⟩, by simp [good]⟩
  · exact ⟨⟨_, s_0e L⟩, by simp [good]⟩
  · exact ⟨⟨_, s_41x L _⟩, by simp [good]⟩
  · exact ⟨⟨_, s_7x L _⟩, trivial⟩
  · exact ⟨⟨_, s_4e L⟩, trivial⟩
  · exact ⟨⟨_, s_6e L⟩, trivial⟩
  · exact ⟨⟨_, s_20e L⟩, trivial⟩

theorem stop_halt (G : List Nat) (h : stopM G = some .halt) (L : Tape) : Halts trans ⟨L, gw 2 (gws G blank), .C⟩ := by
  unfold stopM at h
  split at h <;> (try cases h)
  · exact ⟨_, _, h_000 L _, rfl⟩
  · exact ⟨_, _, h_40 L _, rfl⟩

/-- The scan: the tokens passed, then the stop. -/
def scanM : List Nat → Option (List Tok × Stop)
  | 3 :: G => (scanM G).map fun r => (.blk :: r.1, r.2)
  | 5 :: G => (scanM G).map fun r => (.five :: r.1, r.2)
  | 0 :: 1 :: G => (scanM G).map fun r => (.merge :: r.1, r.2)
  | 0 :: 0 :: 3 :: 3 :: G => (scanM G).map fun r => (.zz :: r.1, r.2)
  | 2 :: 3 :: G => (scanM G).map fun r => (.t23 :: r.1, r.2)
  | G => (stopM G).map fun s => ([], s)

theorem scan_ret (k : Nat) : ∀ (G : List Nat), G.length ≤ k → ∀ (L : Tape) (ts : List Tok) (m : Mode)
    (H : List Nat), scanM G = some (ts, .ret m H) →
    (∃ n, steps n ⟨L, gw 2 (gws G blank), .C⟩ = some (retCfg m (sweepL ts L) H blank)) ∧ good m H := by
  induction k with
  | zero =>
    intro G hG L ts m H h
    have : G = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    simp [scanM, stopM] at h
  | succ k ih =>
    intro G hG L ts m H h
    rw [scanM.eq_def] at h
    split at h
    · rename_i G'
      obtain ⟨⟨ts', s'⟩, hr, e⟩ := Option.map_eq_some_iff.mp h
      cases e
      obtain ⟨⟨a, ha⟩, hg⟩ := ih G' (by simp at hG; omega) (Tok.blk.left L) ts' m H hr
      obtain ⟨b, hb⟩ := tok_sweep .blk L G' blank
      exact ⟨⟨b + a, steps_seq trans hb ha⟩, hg⟩
    · rename_i G'
      obtain ⟨⟨ts', s'⟩, hr, e⟩ := Option.map_eq_some_iff.mp h
      cases e
      obtain ⟨⟨a, ha⟩, hg⟩ := ih G' (by simp at hG; omega) (Tok.five.left L) ts' m H hr
      obtain ⟨b, hb⟩ := tok_sweep .five L G' blank
      exact ⟨⟨b + a, steps_seq trans hb ha⟩, hg⟩
    · rename_i G'
      obtain ⟨⟨ts', s'⟩, hr, e⟩ := Option.map_eq_some_iff.mp h
      cases e
      obtain ⟨⟨a, ha⟩, hg⟩ := ih G' (by simp at hG; omega) (Tok.merge.left L) ts' m H hr
      obtain ⟨b, hb⟩ := tok_sweep .merge L G' blank
      exact ⟨⟨b + a, steps_seq trans hb ha⟩, hg⟩
    · rename_i G'
      obtain ⟨⟨ts', s'⟩, hr, e⟩ := Option.map_eq_some_iff.mp h
      cases e
      obtain ⟨⟨a, ha⟩, hg⟩ := ih G' (by simp at hG; omega) (Tok.zz.left L) ts' m H hr
      obtain ⟨b, hb⟩ := tok_sweep .zz L G' blank
      exact ⟨⟨b + a, steps_seq trans hb ha⟩, hg⟩
    · rename_i G'
      obtain ⟨⟨ts', s'⟩, hr, e⟩ := Option.map_eq_some_iff.mp h
      cases e
      obtain ⟨⟨a, ha⟩, hg⟩ := ih G' (by simp at hG; omega) (Tok.t23.left L) ts' m H hr
      obtain ⟨b, hb⟩ := tok_sweep .t23 L G' blank
      exact ⟨⟨b + a, steps_seq trans hb ha⟩, hg⟩
    · obtain ⟨s', hs, e⟩ := Option.map_eq_some_iff.mp h
      cases e
      exact stop_ret G m H hs L

theorem scan_halt (k : Nat) : ∀ (G : List Nat), G.length ≤ k → ∀ (L : Tape) (ts : List Tok),
    scanM G = some (ts, .halt) → Halts trans ⟨L, gw 2 (gws G blank), .C⟩ := by
  induction k with
  | zero =>
    intro G hG L ts h
    have : G = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    simp [scanM, stopM] at h
  | succ k ih =>
    intro G hG L ts h
    rw [scanM.eq_def] at h
    split at h
    · rename_i G'
      obtain ⟨⟨ts', s'⟩, hr, e⟩ := Option.map_eq_some_iff.mp h
      cases e
      obtain ⟨b, hb⟩ := tok_sweep .blk L G' blank
      obtain ⟨n, c, h1, h2⟩ := ih G' (by simp at hG; omega) _ ts' hr
      exact ⟨b + n, c, steps_seq trans hb h1, h2⟩
    · rename_i G'
      obtain ⟨⟨ts', s'⟩, hr, e⟩ := Option.map_eq_some_iff.mp h
      cases e
      obtain ⟨b, hb⟩ := tok_sweep .five L G' blank
      obtain ⟨n, c, h1, h2⟩ := ih G' (by simp at hG; omega) _ ts' hr
      exact ⟨b + n, c, steps_seq trans hb h1, h2⟩
    · rename_i G'
      obtain ⟨⟨ts', s'⟩, hr, e⟩ := Option.map_eq_some_iff.mp h
      cases e
      obtain ⟨b, hb⟩ := tok_sweep .merge L G' blank
      obtain ⟨n, c, h1, h2⟩ := ih G' (by simp at hG; omega) _ ts' hr
      exact ⟨b + n, c, steps_seq trans hb h1, h2⟩
    · rename_i G'
      obtain ⟨⟨ts', s'⟩, hr, e⟩ := Option.map_eq_some_iff.mp h
      cases e
      obtain ⟨b, hb⟩ := tok_sweep .zz L G' blank
      obtain ⟨n, c, h1, h2⟩ := ih G' (by simp at hG; omega) _ ts' hr
      exact ⟨b + n, c, steps_seq trans hb h1, h2⟩
    · rename_i G'
      obtain ⟨⟨ts', s'⟩, hr, e⟩ := Option.map_eq_some_iff.mp h
      cases e
      obtain ⟨b, hb⟩ := tok_sweep .t23 L G' blank
      obtain ⟨n, c, h1, h2⟩ := ih G' (by simp at hG; omega) _ ts' hr
      exact ⟨b + n, c, steps_seq trans hb h1, h2⟩
    · obtain ⟨s', hs, e⟩ := Option.map_eq_some_iff.mp h
      cases e
      exact stop_halt G hs L

/-- The left end: a normal return puts a 3 in front, a special one `1 1 1`. -/
def finish : Mode × List Nat → List Nat
  | (.N, H) => 3 :: H
  | (.P, H) => 1 :: 1 :: 1 :: H

theorem finish_ok (m : Mode) (H : List Nat) (hg : good m H) :
    steps 37 (retCfg m L3 H blank) = some (cfg (finish (m, H))) ∨
      steps 26 (retCfg m L3 H blank) = some (cfg (finish (m, H))) := by
  cases m with
  | N =>
    rcases H with _ | ⟨g, H⟩
    · exact absurd hg id
    · rcases g with _ | g
      · exact absurd hg (Nat.lt_irrefl 0)
      · exact Or.inl (n_end (gw g (gws H blank)))
  | P => exact Or.inr (p_end (gws H blank))

/-- The outcome of one bounce. -/
inductive Res where
  | next (G : List Nat)
  | halt
  | stuck
  deriving DecidableEq, Repr

/-- One bounce of the gap counter. -/
def bounceM (G : List Nat) : Res :=
  match scanM G with
  | some (ts, .ret m H) => .next (finish (retAll ts.reverse m H))
  | some (_, .halt) => .halt
  | none => .stuck

/-- **The model is right (steps).**  A `next` of `bounceM` is reached by the machine in at least one step. -/
theorem bounceM_next {G G' : List Nat} (h : bounceM G = .next G') :
    ∃ t, 0 < t ∧ steps t (cfg G) = some (cfg G') := by
  unfold bounceM at h
  split at h
  · rename_i ts m H hs
    cases h
    obtain ⟨⟨a, ha⟩, hg⟩ := scan_ret G.length G (Nat.le_refl _) L3 ts m H hs
    rw [sweepL_eq] at ha
    obtain ⟨⟨b, hb⟩, hg'⟩ := ret_all ts.reverse m L3 H blank hg
    rcases finish_ok _ _ hg' with he | he
    · exact ⟨a + (b + 37), by omega, steps_seq trans ha (steps_seq trans hb he)⟩
    · exact ⟨a + (b + 26), by omega, steps_seq trans ha (steps_seq trans hb he)⟩
  · cases h
  · cases h

/-- **The model is right (halting).**  A `halt` of `bounceM` is a halting configuration of the machine. -/
theorem bounceM_halt {G : List Nat} (h : bounceM G = .halt) : Halts trans (cfg G) := by
  unfold bounceM at h
  split at h
  · cases h
  · rename_i ts hs
    exact scan_halt G.length G (Nat.le_refl _) L3 ts hs
  · cases h

end H58767
