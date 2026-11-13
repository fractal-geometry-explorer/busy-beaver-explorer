import Macro

/-!
# 1RB0LF_1LC0LD_1RD1LB_---1RE_0RA1RE_1LA0LE: the block machine is sound

One lemma per case of `mstep`, each a cell rule of `Rules.lean` with the tapes rewritten into block form, and then
`mstep_sound` (the machine goes from `cfg s` to `cfg s'` in exactly the cost of the macro step) and `mstep_halt`.
Everything is checked by Lean's kernel.
-/

set_option linter.unusedSimpArgs false

namespace H15252

open TM

theorem five (s : Tape) : cons true (cons true (cons true (cons true (cons true s)))) = rep 5 [true] s := rfl

/-- The left tape after a restart: all ones. -/
theorem restart_left (Z k : Nat) (s : Tape) :
    rep Z [true] (cons true (rep k [true, true] (cons true (cons true (cons true (cons true (cons true s))))))) =
      rep (Z + 2 * k + 6) [true] s := by
  rw [five, rep_tt, ones_add, ones_cons, ones_add]; congr 1; omega

theorem merge_right (Z k : Nat) (s : Tape) :
    cons true (cons true (cons true (cons true (cons true (rep k [true, true] (rep Z [true] s)))))) =
      rep (2 * k + Z + 5) [true] s := by
  rw [rep_tt, ones_add, five, ones_add]; congr 1; omega

theorem seven (s : Tape) : cons true (cons true (cons true (cons true (cons true (cons true (cons true s)))))) =
    cons true (cons true (cons true (cons true (cons true (rep 2 [true] s))))) := rfl

theorem left3 (x : Nat) : rep (x + 3) [true] blank = rep 3 [true] (rep x [true] blank) := by
  rw [ones_add, Nat.add_comm]

theorem left5 (x : Nat) : rep (x + 5) [true] blank = rep 5 [true] (rep x [true] blank) := by
  rw [ones_add, Nat.add_comm]

theorem round_left (a : Nat) (L : Tape) :
    cons true (rep a [false, true] (cons false (cons true (cons false (cons true L))))) =
      rep (a + 2) [true, false] (cons true L) := by
  rw [cons_true_ft, ← units_add]; rfl

/-! ## Rounds -/

/-- A round with at least three ones on the left, then the walk back. -/
theorem roundB (x a Y : Nat) (R : Tape) :
    steps (6 * a + 18) ⟨rep (x + 3) [true] blank, cons false (cons false (rep a [true, false] (rep (Y + 2) [true] R))), .F⟩ =
      some ⟨rep (x + 1) [true] blank, cons false (cons false (rep (a + 2) [true, false] (rep Y [true] R))), .F⟩ := by
  have h1 := round Y a (rep x [true] blank) R
  rw [round_left] at h1
  have h2 := walkB (a + 2) (cons true (rep x [true] blank)) (rep Y [true] R)
  have h := steps_seq trans h1 h2
  rw [left3, show rep (Y + 2) [true] R = rep 2 [true] (rep Y [true] R) by rw [ones_add, Nat.add_comm]]
  exact steps_congr trans (by omega) h

/-- A round with nothing on the left, then the walk back to the end of the tape. -/
theorem roundzB (a Y : Nat) (R : Tape) :
    steps (6 * a + 14) ⟨rep 0 [true] blank, cons false (cons false (rep a [true, false] (rep (Y + 2) [true] R))), .F⟩ =
      some ⟨rep 0 [true] blank, cons false (cons false (rep (a + 2) [true, false] (rep Y [true] R))), .F⟩ := by
  have h1 := roundz Y a R
  have e : cons true (rep a [false, true] (cons false (cons true blank))) = rep (a + 2) [true, false] blank := by
    rw [cons_true_ft, ← units_add]; show _ = rep a [true, false] (cons true (cons false (cons true (cons false blank))))
    rw [cons_false_blank]
  rw [e] at h1
  have h2 := walkB (a + 2) blank (rep Y [true] R)
  have h := steps_seq trans h1 h2
  rw [show rep (Y + 2) [true] R = rep 2 [true] (rep Y [true] R) by rw [ones_add, Nat.add_comm]]
  exact steps_congr trans (by omega) h

/-! ## Merges -/

theorem mergeB (x a Z : Nat) (R : Tape) :
    steps (6 * a + 20) ⟨rep (x + 5) [true] blank, cons false (cons false (rep a [true, false] (cons false (rep Z [true] (cons false R))))), .F⟩ =
      some ⟨rep (x + 1) [true] blank, cons false (cons false (rep (2 * a + Z + 5) [true] (cons false R))), .F⟩ := by
  have h := merge Z a (rep x [true] blank) R
  rw [merge_right] at h
  rw [left5]; exact h

/-! ## Restarts at the left end -/

theorem restartB (a Z W : Nat) (R : Tape) :
    steps (Z + 8 * a + 19) ⟨rep 0 [true] blank, cons false (cons false (rep a [true, false] (cons false (rep Z [true] (cons false (rep (W + 1) [true] (cons false R))))))), .F⟩ =
      some ⟨rep (Z + 2 * a + 6) [true] blank, cons false (cons false (rep W [true] (cons false R))), .F⟩ := by
  have h := restart W Z a R
  rw [restart_left] at h
  exact h

theorem restart3B (a Z W : Nat) (R : Tape) :
    steps (Z + 8 * a + 27) ⟨rep 3 [true] blank, cons false (cons false (rep a [true, false] (cons false (rep Z [true] (cons false (rep (W + 1) [true] (cons false R))))))), .F⟩ =
      some ⟨rep (Z + 2 * a + 8) [true] blank, cons false (cons false (rep W [true] (cons false R))), .F⟩ := by
  have h := restart3 W Z a R
  have e : rep Z [true] (cons true (rep a [true, true] (cons true (cons true (cons true (cons true (cons true
      (cons true (cons true blank))))))))) = rep (Z + 2 * a + 8) [true] blank := by
    rw [seven, restart_left, ones_add]
  rw [e] at h
  exact h

/-- C at the right end: the new start `X = n + 4` and a block of 3. -/
theorem cbackB (n : Nat) :
    steps 5 ⟨rep (n + 5) [true] blank, cons true (cons true (cons true (cons true blank))), .C⟩ =
      some (cfg ⟨n + 4, 0, .none, 0, some 0⟩) := by
  have h := cback n
  rw [show rep (n + 5) [true] blank = rep 5 [true] (rep n [true] blank) by rw [ones_add, Nat.add_comm]]
  rw [h]
  simp only [cfg, rtape, menc, tenc, rep_zero]
  have e : cons true (rep 3 [true] (rep n [true] blank)) = rep (n + 4) [true] blank := by
    rw [ones_add, ← ones_succ]; congr 1; omega
  rw [e]; rfl

theorem tail0B (k : Nat) :
    steps (8 * k + 27) ⟨rep 0 [true] blank, cons false (cons false (rep k [true, false] blank)), .F⟩ =
      some (cfg ⟨2 * k + 4, 0, .none, 0, some 0⟩) := by
  have h := tail0 k
  rw [cons_false_blank, show rep k [true, true] (cons true (cons true (cons true (cons true (cons true blank))))) =
    rep (2 * k + 5) [true] blank by rw [five, rep_tt, ones_add]] at h
  exact steps_congr trans (by omega) (steps_seq trans h (cbackB (2 * k)))

theorem tail30B (k : Nat) :
    steps (8 * k + 35) ⟨rep 3 [true] blank, cons false (cons false (rep k [true, false] blank)), .F⟩ =
      some (cfg ⟨2 * k + 6, 0, .none, 0, some 0⟩) := by
  have h := tail30 k
  have e : rep k [true, true] (cons true (cons true (cons true (cons true (cons true (cons true
      (cons true blank))))))) = rep (2 * k + 2 + 5) [true] blank := by
    rw [seven, five, rep_tt, ones_add, ones_add]
  rw [cons_false_blank, e] at h
  exact steps_congr trans (by omega) (steps_seq trans h (cbackB (2 * k + 2)))

theorem tail1B (Z k : Nat) :
    steps (Z + 8 * k + 28) ⟨rep 0 [true] blank, cons false (cons false (rep k [true, false] (cons false (rep (Z + 1) [true] blank)))), .F⟩ =
      some (cfg ⟨Z + 2 * k + 5, 0, .none, 0, some 0⟩) := by
  have h := tail1 Z k
  rw [restart_left, ones_cons] at h
  have h2 := cbackB (Z + 2 * k + 1)
  rw [show Z + 2 * k + 1 + 5 = Z + 2 * k + 6 by omega, show Z + 2 * k + 1 + 4 = Z + 2 * k + 5 by omega] at h2
  exact steps_congr trans (by omega) (steps_seq trans h h2)

theorem tail31B (Z k : Nat) :
    steps (Z + 8 * k + 36) ⟨rep 3 [true] blank, cons false (cons false (rep k [true, false] (cons false (rep (Z + 1) [true] blank)))), .F⟩ =
      some (cfg ⟨Z + 2 * k + 7, 0, .none, 0, some 0⟩) := by
  have h := tail31 Z k
  rw [seven, restart_left, ones_add, ones_cons] at h
  have h2 := cbackB (Z + 2 * k + 3)
  rw [show Z + 2 * k + 3 + 5 = Z + 2 * k + 6 + 2 by omega, show Z + 2 * k + 3 + 4 = Z + 2 * k + 7 by omega] at h2
  exact steps_congr trans (by omega) (steps_seq trans h h2)

/-! ## The cases of `mstep` on configurations -/

theorem c_ev (x a q b : Nat) (t : Option Nat) :
    steps (6 * a + 18) (cfg ⟨x + 3, a, .ev q, b, t⟩) =
      some (cfg ⟨x + 1, a + 2, (evNext q), b, t⟩) := by
  have h := roundB x a (2 * q) (cons false (rep b [true, false] (tenc t)))
  cases q with
  | zero => exact h
  | succ q => rw [show 2 * (q + 1) = 2 * q + 2 by omega] at h; exact h

theorem c_evz (a q b : Nat) (t : Option Nat) :
    steps (6 * a + 14) (cfg ⟨0, a, .ev q, b, t⟩) =
      some (cfg ⟨0, a + 2, (evNext q), b, t⟩) := by
  have h := roundzB a (2 * q) (cons false (rep b [true, false] (tenc t)))
  cases q with
  | zero => exact h
  | succ q => rw [show 2 * (q + 1) = 2 * q + 2 by omega] at h; exact h

theorem c_tail (x a b q : Nat) :
    steps (6 * (a + b) + 18) (cfg ⟨x + 3, a, .none, b, some q⟩) = some (cfg (tailNext (x + 1) (a + b) q)) := by
  have h := roundB x (a + b) (2 * q + 1) blank
  simp only [cfg, rtape, menc, tenc] at h ⊢
  rw [units_add]
  cases q with
  | zero =>
    simp only [tailNext, rtape, menc, tenc, rep_zero] at h ⊢
    rw [show 2 * 0 + 1 = 1 from rfl, one_blank, units_add] at h; exact h
  | succ q =>
    simp only [tailNext, rtape, menc, tenc, rep_zero] at h ⊢
    rw [show 2 * (q + 1) + 1 = 2 * q + 3 by omega] at h; exact h

theorem c_tailz (a b q : Nat) :
    steps (6 * (a + b) + 14) (cfg ⟨0, a, .none, b, some q⟩) = some (cfg (tailNext 0 (a + b) q)) := by
  have h := roundzB (a + b) (2 * q + 1) blank
  simp only [cfg, rtape, menc, tenc] at h ⊢
  rw [units_add]
  cases q with
  | zero =>
    simp only [tailNext, rtape, menc, tenc, rep_zero] at h ⊢
    rw [show 2 * 0 + 1 = 1 from rfl, one_blank, units_add] at h; exact h
  | succ q =>
    simp only [tailNext, rtape, menc, tenc, rep_zero] at h ⊢
    rw [show 2 * (q + 1) + 1 = 2 * q + 3 by omega] at h; exact h

theorem c_two2 (q : Nat) : steps 15 (cfg ⟨2, 0, .none, 0, some q⟩) = some (cfg ⟨5, 0, .ev q, 0, none⟩) := by
  have h := two2 (2 * q + 1) blank
  rw [cons_false_blank] at h
  show steps 15 ⟨rep 2 [true] blank, cons false (cons false (rep (2 * q + 3) [true] blank)), .F⟩ =
    some ⟨rep 5 [true] blank, cons false (cons false (rep (2 * q + 2) [true] (cons false blank))), .F⟩
  rw [cons_false_blank]; exact h

theorem c_two1 (k : Nat) (m : Mid) (b : Nat) (t : Option Nat) (hm : m = .none) :
    steps 15 (cfg ⟨2, k + 1, m, b, t⟩) = some (cfg ⟨5, 0, .zero, k + b, t⟩) := by
  subst hm
  have h := two1 (rep (k + b) [true, false] (tenc t))
  simp only [cfg, rtape, menc, rep_zero]
  rw [show rep (k + 1) [true, false] (rep b [true, false] (tenc t)) =
    cons true (cons false (rep (k + b) [true, false] (tenc t))) by rw [units_add, show k + 1 + b = (k + b) + 1 by omega]; rfl]
  exact h

theorem c_units5 (x a b : Nat) :
    steps (6 * (a + b) + 20) (cfg ⟨x + 5, a, .none, b, none⟩) = some (cfg ⟨x + 1, 0, .none, 0, some (a + b + 1)⟩) := by
  have h := mergeB x (a + b) 0 blank
  simp only [cfg, rtape, menc, tenc, rep_zero] at h ⊢
  rw [cons_false_blank, cons_false_blank] at h
  rw [units_add, h, show 2 * (a + b) + 0 + 5 = 2 * (a + b + 1) + 3 by omega]

theorem c_units0 (a b : Nat) :
    steps (8 * (a + b) + 27) (cfg ⟨0, a, .none, b, none⟩) = some (cfg ⟨2 * (a + b) + 4, 0, .none, 0, some 0⟩) := by
  have h := tail0B (a + b)
  simp only [cfg, rtape, menc, tenc] at h ⊢
  rw [units_add]; exact h

theorem c_units3 (a b : Nat) :
    steps (8 * (a + b) + 35) (cfg ⟨3, a, .none, b, none⟩) = some (cfg ⟨2 * (a + b) + 6, 0, .none, 0, some 0⟩) := by
  have h := tail30B (a + b)
  simp only [cfg, rtape, menc, tenc] at h ⊢
  rw [units_add]; exact h

theorem c_units4 (a b : Nat) : ∃ n c, steps n (cfg ⟨4, a, .none, b, none⟩) = some c ∧ step c = none := by
  have h := haltcfg (a + b)
  have h' : steps (6 * (a + b) + 17) (cfg ⟨4, a, .none, b, none⟩) = some ⟨blank, cons false (cons false (cons true
      (cons true (cons true (cons true (cons true (rep (a + b) [true, true] (cons true blank)))))))), .D⟩ := by
    simp only [cfg, rtape, menc, tenc]
    rw [units_add]; exact h
  exact ⟨_, _, h', rfl⟩

theorem c_zero5_b (x a b : Nat) (t : Option Nat) :
    steps (6 * a + 20) (cfg ⟨x + 5, a, .zero, b + 1, t⟩) = some (cfg ⟨x + 1, 0, .ev (a + 2), b, t⟩) := by
  have h := mergeB x a 1 (rep b [true, false] (tenc t))
  simp only [cfg, rtape, menc, rep_zero] at h ⊢
  rw [show 2 * (a + 2) + 2 = 2 * a + 1 + 5 by omega]
  exact h

theorem c_zero5_q (x a q : Nat) :
    steps (6 * a + 20) (cfg ⟨x + 5, a, .zero, 0, some q⟩) = some (cfg ⟨x + 1, 0, .ev (a + q + 3), 0, none⟩) := by
  have h := mergeB x a (2 * q + 3) blank
  rw [cons_false_blank] at h
  simp only [cfg, rtape, menc, tenc, rep_zero] at h ⊢
  rw [show 2 * (a + q + 3) + 2 = 2 * a + (2 * q + 3) + 5 by omega, cons_false_blank]
  exact h

theorem c_zero5_n (x a : Nat) :
    steps (6 * a + 20) (cfg ⟨x + 5, a, .zero, 0, none⟩) = some (cfg ⟨x + 1, 0, .none, 0, some (a + 1)⟩) := by
  have h := mergeB x a 0 blank
  rw [rep_zero, cons_false_blank, cons_false_blank] at h
  simp only [cfg, rtape, menc, tenc, rep_zero]
  rw [show 2 * (a + 1) + 3 = 2 * a + 0 + 5 by omega, cons_false_blank]
  exact h

/-- The right tape of a gap followed by `b + 2` units: a block of 1, then a block of 1 (the restart reads both). -/
theorem gap_bb (a b : Nat) (S : Tape) :
    rep a [true, false] (menc .zero (rep (b + 2) [true, false] S)) =
      rep a [true, false] (cons false (rep 1 [true] (cons false (rep (0 + 1) [true] (cons false (rep b [true, false] S)))))) := rfl

theorem gap_bq (a q : Nat) :
    rep a [true, false] (menc .zero (rep 1 [true, false] (tenc (some q)))) =
      rep a [true, false] (cons false (rep 1 [true] (cons false (rep (2 * q + 2 + 1) [true] (cons false blank))))) := by
  simp only [menc, tenc]; rw [cons_false_blank]; rfl

theorem c_zero0_bb (a b : Nat) (t : Option Nat) :
    steps (8 * a + 20) (cfg ⟨0, a, .zero, b + 2, t⟩) = some (cfg ⟨2 * a + 7, 0, .zero, b, t⟩) := by
  have h := restartB a 1 0 (rep b [true, false] (tenc t))
  simp only [cfg, rtape]
  rw [gap_bb, show 2 * a + 7 = 1 + 2 * a + 6 by omega]
  exact steps_congr trans (by omega) h

theorem c_zero3_bb (a b : Nat) (t : Option Nat) :
    steps (8 * (a + 1) + 20) (cfg ⟨3, a, .zero, b + 2, t⟩) = some (cfg ⟨2 * (a + 1) + 7, 0, .zero, b, t⟩) := by
  have h := restart3B a 1 0 (rep b [true, false] (tenc t))
  simp only [cfg, rtape]
  rw [gap_bb, show 2 * (a + 1) + 7 = 1 + 2 * a + 8 by omega]
  exact steps_congr trans (by omega) h

theorem c_zero0_bq (a q : Nat) :
    steps (8 * a + 20) (cfg ⟨0, a, .zero, 1, some q⟩) = some (cfg ⟨2 * a + 7, 0, .ev q, 0, none⟩) := by
  have h := restartB a 1 (2 * q + 2) blank
  simp only [cfg, rtape]
  rw [gap_bq, show 2 * a + 7 = 1 + 2 * a + 6 by omega]
  simp only [menc, rep_zero, tenc]
  exact steps_congr trans (by omega) h

theorem c_zero3_bq (a q : Nat) :
    steps (8 * (a + 1) + 20) (cfg ⟨3, a, .zero, 1, some q⟩) = some (cfg ⟨2 * (a + 1) + 7, 0, .ev q, 0, none⟩) := by
  have h := restart3B a 1 (2 * q + 2) blank
  simp only [cfg, rtape]
  rw [gap_bq, show 2 * (a + 1) + 7 = 1 + 2 * a + 8 by omega]
  simp only [menc, rep_zero, tenc]
  exact steps_congr trans (by omega) h

theorem c_zero0_1n (a : Nat) :
    steps (8 * a + 28) (cfg ⟨0, a, .zero, 1, none⟩) = some (cfg ⟨2 * a + 5, 0, .none, 0, some 0⟩) := by
  have h := tail1B 0 a
  simp only [cfg, rtape, menc, tenc] at h ⊢
  rw [show rep 1 [true, false] blank = cons true blank by
    show cons true (cons false blank) = _; rw [cons_false_blank]]
  rw [show 2 * a + 5 = 0 + 2 * a + 5 by omega]
  exact steps_congr trans (by omega) h

theorem c_zero3_1n (a : Nat) :
    steps (8 * (a + 1) + 28) (cfg ⟨3, a, .zero, 1, none⟩) = some (cfg ⟨2 * (a + 1) + 5, 0, .none, 0, some 0⟩) := by
  have h := tail31B 0 a
  simp only [cfg, rtape, menc, tenc] at h ⊢
  rw [show rep 1 [true, false] blank = cons true blank by
    show cons true (cons false blank) = _; rw [cons_false_blank]]
  rw [show 2 * (a + 1) + 5 = 0 + 2 * a + 7 by omega]
  exact steps_congr trans (by omega) h

theorem c_zero0_0q (a q : Nat) :
    steps (8 * a + 2 * q + 30) (cfg ⟨0, a, .zero, 0, some q⟩) = some (cfg ⟨2 * a + 2 * q + 7, 0, .none, 0, some 0⟩) := by
  have h := tail1B (2 * q + 2) a
  simp only [cfg, rtape, menc, tenc, rep_zero] at h ⊢
  rw [show 2 * q + 3 = 2 * q + 2 + 1 by omega, show 2 * a + 2 * q + 7 = 2 * q + 2 + 2 * a + 5 by omega]
  exact steps_congr trans (by omega) h

theorem c_zero3_0q (a q : Nat) :
    steps (8 * (a + 1) + 2 * q + 30) (cfg ⟨3, a, .zero, 0, some q⟩) =
      some (cfg ⟨2 * (a + 1) + 2 * q + 7, 0, .none, 0, some 0⟩) := by
  have h := tail31B (2 * q + 2) a
  simp only [cfg, rtape, menc, tenc, rep_zero] at h ⊢
  rw [show 2 * q + 3 = 2 * q + 2 + 1 by omega, show 2 * (a + 1) + 2 * q + 7 = 2 * q + 2 + 2 * a + 7 by omega]
  exact steps_congr trans (by omega) h

theorem c_zero0_0n (a : Nat) :
    steps (8 * a + 27) (cfg ⟨0, a, .zero, 0, none⟩) = some (cfg ⟨2 * a + 4, 0, .none, 0, some 0⟩) := by
  have h := tail0B a
  simp only [cfg, rtape, menc, tenc, rep_zero] at h ⊢
  rw [cons_false_blank]; exact h

theorem c_zero3_0n (a : Nat) :
    steps (8 * (a + 1) + 27) (cfg ⟨3, a, .zero, 0, none⟩) = some (cfg ⟨2 * (a + 1) + 4, 0, .none, 0, some 0⟩) := by
  have h := tail30B a
  simp only [cfg, rtape, menc, tenc, rep_zero] at h ⊢
  rw [cons_false_blank, show 2 * (a + 1) + 4 = 2 * a + 6 by omega]
  exact steps_congr trans (by omega) h

/-! ## Soundness -/

theorem withNorm_sound {s s1 : Q} {n : Nat} (h : steps n (cfg s) = some (cfg s1)) {s' : Q} {n' : Nat}
    (hw : withNorm s1 n = .go s' n') : steps n' (cfg s) = some (cfg s') := by
  unfold withNorm at hw; cases hw; exact steps_seq trans h (norm_sound s1)

theorem go_sound {s s1 : Q} {n : Nat} (h : steps n (cfg s) = some (cfg s1)) {s' : Q} {n' : Nat}
    (hw : MS.go s1 n = .go s' n') : steps n' (cfg s) = some (cfg s') := by
  cases hw; exact h

/-- **The machine follows the macro machine**, with the exact step count. -/
theorem mstep_sound (s : Q) {s' : Q} {n : Nat} (h : mstep s = .go s' n) : steps n (cfg s) = some (cfg s') := by
  obtain ⟨X, a, m, b, t⟩ := s
  cases m with
  | ev q =>
    simp only [mstep] at h
    split at h
    · obtain ⟨x, rfl⟩ : ∃ x, X = x + 3 := ⟨X - 3, by omega⟩
      rw [show x + 3 - 2 = x + 1 by omega] at h
      exact withNorm_sound (c_ev x a q b t) h
    · split at h
      · subst_vars; exact go_sound (c_evz a q b t) h
      · cases h
  | none =>
    cases t with
    | some q =>
      simp only [mstep] at h
      split at h
      · subst_vars
        split at h
        · obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := by omega
          exact go_sound (c_two2 q) h
        · obtain ⟨k, hk⟩ : ∃ k, a + b = k + 1 := ⟨a + b - 1, by omega⟩
          cases a with
          | zero =>
            -- all the units are in `b`: the same tape with them in `a`
            have e : cfg ⟨2, 0, .none, b, some q⟩ = cfg ⟨2, b, .none, 0, some q⟩ := by
              simp only [cfg, rtape, menc, rep_zero]
            rw [e]; obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
            exact go_sound (c_two1 b' .none 0 (some q) rfl)
              (by rw [show 0 + (b' + 1) - 1 = b' + 0 by omega] at h; exact h)
          | succ a =>
            rw [show a + 1 + b - 1 = a + b by omega] at h
            exact go_sound (c_two1 a .none b (some q) rfl) h
      · split at h
        · obtain ⟨x, rfl⟩ : ∃ x, X = x + 3 := ⟨X - 3, by omega⟩
          rw [show x + 3 - 2 = x + 1 by omega] at h
          exact withNorm_sound (c_tail x a b q) h
        · split at h
          · subst_vars; exact go_sound (c_tailz a b q) h
          · cases h
    | none =>
      simp only [mstep] at h
      split at h
      · subst_vars
        split at h
        · cases h
        · cases a with
          | zero =>
            have e : cfg ⟨2, 0, .none, b, none⟩ = cfg ⟨2, b, .none, 0, none⟩ := by
              simp only [cfg, rtape, menc, rep_zero]
            rw [e]; obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
            exact go_sound (c_two1 b' .none 0 none rfl) (by rw [show 0 + (b' + 1) - 1 = b' + 0 by omega] at h; exact h)
          | succ a =>
            rw [show a + 1 + b - 1 = a + b by omega] at h
            exact go_sound (c_two1 a .none b none rfl) h
      · split at h
        · obtain ⟨x, rfl⟩ : ∃ x, X = x + 5 := ⟨X - 5, by omega⟩
          rw [show x + 5 - 4 = x + 1 by omega] at h
          exact withNorm_sound (c_units5 x a b) h
        · split at h
          · cases h
          · split at h
            · subst_vars; exact go_sound (c_units0 a b) h
            · split at h
              · subst_vars; exact go_sound (c_units3 a b) h
              · cases h
  | zero =>
    simp only [mstep] at h
    split at h
    · obtain ⟨x, rfl⟩ : ∃ x, X = x + 5 := ⟨X - 5, by omega⟩
      rw [show x + 5 - 4 = x + 1 by omega] at h
      split at h
      · exact withNorm_sound (c_zero5_b x a _ t) h
      · exact withNorm_sound (c_zero5_q x a _) h
      · exact withNorm_sound (c_zero5_n x a) h
    · split at h
      · rename_i hX
        rcases hX with rfl | rfl
        · simp only [show (0 = 3) = False from by simp, ite_false] at h
          split at h
          · exact go_sound (c_zero0_bb a _ t) h
          · exact go_sound (c_zero0_bq a _) h
          · exact go_sound (c_zero0_1n a) h
          · exact go_sound (c_zero0_0q a _) h
          · exact go_sound (c_zero0_0n a) h
        · simp only [ite_true] at h
          split at h
          · exact go_sound (c_zero3_bb a _ t) h
          · exact go_sound (c_zero3_bq a _) h
          · exact go_sound (c_zero3_1n a) h
          · exact go_sound (c_zero3_0q a _) h
          · exact go_sound (c_zero3_0n a) h
      · cases h

/-- **The macro halt is a real halt.** -/
theorem mstep_halt (s : Q) (h : mstep s = .halt) : ∃ n c, steps n (cfg s) = some c ∧ step c = none := by
  obtain ⟨X, a, m, b, t⟩ := s
  cases m with
  | ev q =>
    simp only [mstep] at h
    split at h
    · simp [withNorm] at h
    · split at h <;> cases h
  | none =>
    cases t with
    | some q =>
      simp only [mstep] at h
      split at h
      · split at h <;> cases h
      · split at h
        · simp [withNorm] at h
        · split at h <;> cases h
    | none =>
      simp only [mstep] at h
      split at h
      · split at h <;> cases h
      · split at h
        · simp [withNorm] at h
        · split at h
          · subst_vars; exact c_units4 a b
          · split at h
            · cases h
            · split at h <;> cases h
  | zero =>
    simp only [mstep] at h
    split at h
    · split at h <;> simp [withNorm] at h
    · split at h
      · split at h <;> (split at h <;> cases h)
      · cases h

end H15252
