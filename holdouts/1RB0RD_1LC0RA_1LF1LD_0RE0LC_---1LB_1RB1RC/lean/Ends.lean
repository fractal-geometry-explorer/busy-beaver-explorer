import Event

/-!
# Every end event of 1RB0RD_1LC0RA_1LF1LD_0RE0LC_---1LB_1RB1RC, for every counter

`Sweep.lean` proves a sweep whose carry stops inside the digits; `Event.lean` follows the one end event of the run
from blank tape.  Here the tape right of the wall is `x0 1 x1 1 ... xk 1 d` with blank tape after the last cell d
(the shape of the run from blank tape, and the shape every sweep below leaves behind), and every sweep is proved,
whatever the digits:

* the carry stops inside x1..xk: `sweep` (`Sweep.lean`);
* it runs through all of them (`exitQ .a xs = some q`) and reads d in state q:
  * q = a, d = 0: d becomes 1 (`last_stop_event`);
  * q = a, d = 1: the counter gains a digit: the digits become `thru xs ++ [1]`, the last cell 1 (`ext_event`);
  * q = b, d = 0 or q = c, d = 1: **the machine halts** (`halt_event_b`, `halt_event_c`);
  * q = b, d = 1 or q = c, d = 0: the pass back runs in another mode and turns the whole wall of n + 1 pairs into
    digits: the new counter is `1^n 0 (cind xs) 1`, last cell 1, with a new wall of one pair (`conv_event`).
    `cind` marks the digits after which the carry was in state c.

`evstep` is this as a map on (wall, digits, last cell), `none` for a halt.  `halts_iff_events`: from any such
arrival the machine halts if and only if iterating `evstep` reaches `none`; `blank_halts_iff_events`: from blank
tape, if and only if it does so from (9, `X0`, 1).  `second_arrival`: where the run from blank tape is after its
first end event.  Written by hand.
-/

namespace H74982

open TM

/-! ## The carry running through all the digits -/

/-- The state in which the carry leaves the digits (`none` if it stops inside them). -/
def exitQ : Q → List Bool → Option Q
  | q, [] => some q
  | .a, false :: _ => none
  | .a, true :: ds => exitQ .b ds
  | .b, false :: ds => exitQ .a ds
  | .b, true :: ds => exitQ .c ds
  | .c, false :: ds => exitQ .c ds
  | .c, true :: ds => exitQ .a ds

/-- The digits a carry writes when it runs through all of them. -/
def thru : Q → List Bool → List Bool
  | _, [] => []
  | .a, false :: ds => true :: ds
  | .a, true :: ds => false :: thru .b ds
  | .b, false :: ds => true :: thru .a ds
  | .b, true :: ds => false :: thru .c ds
  | .c, false :: ds => false :: thru .c ds
  | .c, true :: ds => true :: thru .a ds

/-- For each digit the carry runs through: is it in state c afterwards? -/
def cind : Q → List Bool → List Bool
  | _, [] => []
  | .a, false :: _ => []
  | .a, true :: ds => false :: cind .b ds
  | .b, false :: ds => false :: cind .a ds
  | .b, true :: ds => true :: cind .c ds
  | .c, false :: ds => true :: cind .c ds
  | .c, true :: ds => false :: cind .a ds

theorem exit_of_carry_none (xs : List Bool) : ∀ q, carry q xs = none → ∃ q', exitQ q xs = some q' := by
  induction xs with
  | nil => intro q _; exact ⟨q, by cases q <;> rfl⟩
  | cons d ds ih =>
    intro q h
    cases q <;> cases d <;> simp only [carry, Option.map_eq_none_iff] at h
    · cases h
    · exact ih .b h
    · exact ih .a h
    · exact ih .c h
    · exact ih .c h
    · exact ih .a h

theorem carry_none_of_exit (xs : List Bool) : ∀ q q', exitQ q xs = some q' → carry q xs = none := by
  induction xs with
  | nil => intro q q' _; cases q <;> rfl
  | cons d ds ih =>
    intro q q' h
    cases q <;> cases d <;> simp only [exitQ] at h <;> simp only [carry, Option.map_eq_none_iff]
    · cases h
    · exact ih _ _ h
    · exact ih _ _ h
    · exact ih _ _ h
    · exact ih _ _ h
    · exact ih _ _ h

theorem off_of_exit (xs : List Bool) : ∀ (q q' : Q) (acc : List (Bool × Bool)), exitQ q xs = some q' →
    ∃ acc', offPairs q xs acc = some (q', acc') := by
  induction xs with
  | nil =>
    intro q q' acc h
    have e : q = q' := by cases q <;> simpa [exitQ] using h
    subst e
    exact ⟨acc, by cases q <;> rfl⟩
  | cons d ds ih =>
    intro q q' acc h
    cases q <;> cases d <;> simp only [exitQ] at h <;> simp only [offPairs]
    · cases h
    · exact ih _ _ _ h
    · exact ih _ _ _ h
    · exact ih _ _ _ h
    · exact ih _ _ _ h
    · exact ih _ _ _ h

theorem cells_append (xs ys : List Bool) (R : Tape) : cells (xs ++ ys) R = cells xs (cells ys R) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [cells, ih]

theorem rep_ones (n : Nat) (R : Tape) : rep n [true, true] R = cells (List.replicate n true) R := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h : rep (n + 1) [true, true] R = cons true (cons true (rep n [true, true] R)) := rfl
    rw [h, ih, List.replicate_succ]
    rfl

/-! ## The carry reaches the last cell in state a: an ordinary pass back -/

/-- Carry in state a on the last cell, a 0 with blank tape after it: the cell becomes 1 and the head turns back. -/
theorem last_stop (t : Bool) (L : Tape) :
    steps 5 ⟨cons true (cons false (cons t L)), cons false blank, .B⟩ =
      some ⟨L, cons t (cons true (cons true (cons true blank))), .C⟩ := by
  cases t <;> rfl

/-- Carry in state a on the last cell, a 1 with blank tape after it: two new cells, and the head turns back. -/
theorem last_ext (t : Bool) (L : Tape) :
    steps 11 ⟨cons true (cons false (cons t L)), cons true blank, .B⟩ =
      some ⟨L, cons t (cons true (cons true (cons true (cons true (cons true blank))))), .C⟩ := by
  cases t <;> rfl

/-- The carry from state q runs through all of xs and leaves in state a, where the tape T turns it back as a
stopping digit would (`hT`): right, then back to the pair p. -/
theorem run_thru (xs : List Bool) (T T' : Tape)
    (hT : ∀ (p : Bool × Bool) (ps : List (Bool × Bool)) (W : Tape),
      ∃ s, steps s (fwd .a (p :: ps) W T) = some (back p ps W (cons true (cons true T')))) :
    ∀ (q : Q), exitQ q xs = some .a → ∀ (p : Bool × Bool) (ps : List (Bool × Bool)) (W : Tape),
      ∃ s, steps s (fwd q (p :: ps) W (cells xs T)) =
        some (back p ps W (cons (prev q) (cons true (cells (thru q xs) T')))) := by
  induction xs with
  | nil =>
    intro q h p ps W
    have e : q = .a := by cases q <;> simp [exitQ] at h <;> rfl
    subst e
    exact hT p ps W
  | cons d ds ih =>
    intro q h p ps W
    cases q <;> cases d <;> simp only [exitQ] at h
    · cases h
    · have h1 := fwd_a1 (cons true (cons false (lt (p :: ps) W))) (cells ds T)
      obtain ⟨s2, h2⟩ := ih .b h (false, true) (p :: ps) W
      obtain ⟨s3, h3⟩ := back_step (false, true) (by decide) p ps W (cons false (cons true (cells (thru .b ds) T')))
      exact ⟨_, steps_seq trans h1 (steps_seq trans h2 h3)⟩
    · have h1 := fwd_b0 (lt (p :: ps) W) (cells ds T)
      obtain ⟨s2, h2⟩ := ih .a h (true, true) (p :: ps) W
      obtain ⟨s3, h3⟩ := back_step (true, true) (by decide) p ps W (cons true (cons true (cells (thru .a ds) T')))
      exact ⟨_, steps_seq trans h1 (steps_seq trans h2 h3)⟩
    · have h1 := fwd_b1 (lt (p :: ps) W) (cells ds T)
      obtain ⟨s2, h2⟩ := ih .c h (true, false) (p :: ps) W
      obtain ⟨s3, h3⟩ := back_step (true, false) (by decide) p ps W (cons false (cons true (cells (thru .c ds) T')))
      exact ⟨_, steps_seq trans h1 (steps_seq trans h2 h3)⟩
    · have h1 := fwd_c0 (cons false (cons true (lt (p :: ps) W))) (cells ds T)
      obtain ⟨s2, h2⟩ := ih .c h (true, false) (p :: ps) W
      obtain ⟨s3, h3⟩ := back_step (true, false) (by decide) p ps W (cons false (cons true (cells (thru .c ds) T')))
      exact ⟨_, steps_seq trans h1 (steps_seq trans h2 h3)⟩
    · have h1 := fwd_c1 (lt (p :: ps) W) (cells ds T)
      obtain ⟨s2, h2⟩ := ih .a h (true, true) (p :: ps) W
      obtain ⟨s3, h3⟩ := back_step (true, true) (by decide) p ps W (cons true (cons true (cells (thru .a ds) T')))
      exact ⟨_, steps_seq trans h1 (steps_seq trans h2 h3)⟩

/-- A whole sweep whose carry runs through all the digits and is turned back by the tape T after them. -/
theorem thru_sweep (n : Nat) (xs : List Bool) (T T' : Tape)
    (hT : ∀ (p : Bool × Bool) (ps : List (Bool × Bool)) (W : Tape),
      ∃ s, steps s (fwd .a (p :: ps) W T) = some (back p ps W (cons true (cons true T'))))
    (h : exitQ .a xs = some .a) :
    ∃ s, 0 < s ∧ steps s (arrival (n + 1) xs T) = some (arrival (n + 2) (thru .a xs) T') := by
  have h1 := fwd_c1 (wall n) (cells xs T)
  obtain ⟨s2, h2⟩ := run_thru xs T T' hT .a h (true, true) [] (wall n)
  have h3 := back_end n (cells (thru .a xs) T')
  rw [wall_snoc] at h3
  exact ⟨_, by omega, steps_seq trans h1 (steps_seq trans h2 h3)⟩

/-- The carry reads the last cell, a 0, in state a: the cell becomes 1. -/
theorem last_stop_event (n : Nat) (xs : List Bool) (h : exitQ .a xs = some .a) :
    ∃ s, 0 < s ∧ steps s (arrival (n + 1) xs (cons false blank)) =
      some (arrival (n + 2) (thru .a xs) (cons true blank)) := by
  apply thru_sweep n xs _ _ _ h
  rintro ⟨w, t⟩ ps W
  exact ⟨_, last_stop t (cons w (lt ps W))⟩

/-- The carry reads the last cell, a 1, in state a: the counter gains a digit 1, and the last cell is 1 again. -/
theorem ext_event (n : Nat) (xs : List Bool) (h : exitQ .a xs = some .a) :
    ∃ s, 0 < s ∧ steps s (arrival (n + 1) xs (cons true blank)) =
      some (arrival (n + 2) (thru .a xs ++ [true]) (cons true blank)) := by
  rw [cells_arrival_append]
  apply thru_sweep n xs _ _ _ h
  rintro ⟨w, t⟩ ps W
  exact ⟨_, last_ext t (cons w (lt ps W))⟩
where
  cells_arrival_append : arrival (n + 2) (thru .a xs ++ [true]) (cons true blank) =
      arrival (n + 2) (thru .a xs) (cons true (cons true (cons true blank))) := by
    simp only [arrival, cells_append]
    rfl

/-! ## The halting end events -/

theorem halts_of_reach {c c' : Config} {s : Nat} (h : steps s c = some c') (h' : Halts trans c') :
    Halts trans c := (halts_iff_of_steps h).mpr h'

theorem halts_fwd_b (ps : List (Bool × Bool)) (W : Tape) : Halts trans (fwd .b ps W (cons false blank)) :=
  ⟨1, ⟨cons false (cons false (cons false (lt ps W))), blank, .E⟩, rfl, rfl⟩

theorem halts_fwd_c (ps : List (Bool × Bool)) (W : Tape) : Halts trans (fwd .c ps W (cons true blank)) :=
  ⟨2, ⟨cons false (cons false (cons false (cons true (lt ps W)))), blank, .E⟩, rfl, rfl⟩

/-- The carry reads the last cell, a 0, in state b: the machine halts. -/
theorem halt_event_b (n : Nat) (xs : List Bool) (h : exitQ .a xs = some .b) :
    Halts trans (arrival (n + 1) xs (cons false blank)) := by
  obtain ⟨acc, ha⟩ := off_of_exit xs .a .b [(true, true)] h
  have h1 := fwd_c1 (wall n) (cells xs (cons false blank))
  obtain ⟨s2, h2⟩ := run_off xs .a (true, true) [] .b acc (wall n) (cons false blank) ha
  exact halts_of_reach (steps_seq trans h1 h2) (halts_fwd_b acc (wall n))

/-- The carry reads the last cell, a 1, in state c: the machine halts. -/
theorem halt_event_c (n : Nat) (xs : List Bool) (h : exitQ .a xs = some .c) :
    Halts trans (arrival (n + 1) xs (cons true blank)) := by
  obtain ⟨acc, ha⟩ := off_of_exit xs .a .c [(true, true)] h
  have h1 := fwd_c1 (wall n) (cells xs (cons true blank))
  obtain ⟨s2, h2⟩ := run_off xs .a (true, true) [] .c acc (wall n) (cons true blank) ha
  exact halts_of_reach (steps_seq trans h1 h2) (halts_fwd_c acc (wall n))

/-! ## The converting end events -/

/-- Carry in state b on the last cell, a 1: one new cell, and state C starts back one cell out of step. -/
theorem turn_b1 (L : Tape) :
    steps 10 ⟨cons false (cons false L), cons true blank, .D⟩ =
      some ⟨L, cons true (cons true (cons true (cons true blank))), .C⟩ := rfl

/-- Carry in state c on the last cell, a 0: the same. -/
theorem turn_c0 (L : Tape) :
    steps 6 ⟨cons false (cons true L), cons false blank, .A⟩ =
      some ⟨L, cons true (cons true (cons true (cons true blank))), .C⟩ := rfl

/-- State C going back out of step: on the cell v right of the pending pair (w, t), not both t and v zero.  The
separator t becomes the digit `!t`, the cell v a separator 1, and C is on w. -/
theorem cb_step (w t v : Bool) (h : (t || v) = true) (L R : Tape) :
    ∃ s, steps s ⟨cons t (cons w L), cons v R, .C⟩ = some ⟨L, cons w (cons (!t) (cons true R)), .C⟩ := by
  cases t <;> cases v
  · cases h
  · exact ⟨4, by cases w <;> rfl⟩
  · exact ⟨4, by cases w <;> rfl⟩
  · exact ⟨2, by cases w <;> rfl⟩

/-- No pending pair has separator 0 with a 0 on the cell right of it (v, then the pairs' own first cells). -/
def okC : Bool → List (Bool × Bool) → Bool
  | _, [] => true
  | v, (w, t) :: ps => (t || v) && okC w ps

/-- The tape right of the head after the out-of-step pass back over the pending pairs. -/
def cunw : List (Bool × Bool) → Bool → Tape → Tape
  | [], v, r => cons v r
  | (w, t) :: ps, _, r => cunw ps w (cons (!t) (cons true r))

theorem cb_all (ps : List (Bool × Bool)) : ∀ (v : Bool) (W r : Tape), okC v ps = true →
    ∃ s, steps s ⟨lt ps W, cons v r, .C⟩ = some ⟨W, cunw ps v r, .C⟩ := by
  induction ps with
  | nil => intro v W r _; exact ⟨0, rfl⟩
  | cons p ps ih =>
    intro v W r h
    obtain ⟨w, t⟩ := p
    simp only [okC, Bool.and_eq_true] at h
    obtain ⟨s1, h1⟩ := cb_step w t v h.1 (lt ps W) r
    obtain ⟨s2, h2⟩ := ih w W (cons (!t) (cons true r)) h.2
    exact ⟨_, steps_seq trans h1 h2⟩

theorem ok_off (xs : List Bool) : ∀ (q q' : Q) (acc0 acc : List (Bool × Bool)),
    offPairs q xs acc0 = some (q', acc) → okC true acc0 = true → (q = .a → okC false acc0 = true) →
    okC true acc = true ∧ (q' = .a → okC false acc = true) := by
  induction xs with
  | nil =>
    intro q q' acc0 acc h h1 h2
    simp only [offPairs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨h1, h2⟩
  | cons d ds ih =>
    intro q q' acc0 acc h h1 h2
    cases q <;> cases d <;> simp only [offPairs] at h
    · cases h
    · exact ih _ _ _ _ h (by simp [okC, h2 rfl]) (by intro e; cases e)
    · exact ih _ _ _ _ h (by simp [okC, h1]) (by intro _; simp [okC, h1])
    · exact ih _ _ _ _ h (by simp [okC, h1]) (by intro e; cases e)
    · exact ih _ _ _ _ h (by simp [okC, h1]) (by intro e; cases e)
    · exact ih _ _ _ _ h (by simp [okC, h1]) (by intro _; simp [okC, h1])

/-- The first cell of the pending pair of the first digit (v if there is no digit). -/
def firstW : Q → List Bool → Bool → Bool
  | _, [], v => v
  | .a, _ :: _, _ => false
  | _, _ :: _, _ => true

theorem cunw_off (xs : List Bool) : ∀ (q q' : Q) (acc0 acc : List (Bool × Bool)) (v : Bool) (r : Tape),
    offPairs q xs acc0 = some (q', acc) → cunw acc v r = cunw acc0 (firstW q xs v) (cells (cind q xs) r) := by
  induction xs with
  | nil =>
    intro q q' acc0 acc v r h
    simp only [offPairs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    cases q <;> rfl
  | cons d ds ih =>
    intro q q' acc0 acc v r h
    cases q <;> cases d <;> simp only [offPairs] at h
    · cases h
    · rw [ih _ _ _ _ v r h]; rfl
    · rw [ih _ _ _ _ v r h]; rfl
    · rw [ih _ _ _ _ v r h]; rfl
    · rw [ih _ _ _ _ v r h]; rfl
    · rw [ih _ _ _ _ v r h]; rfl

/-- At the blank left end after the wall has been turned into digits: a new wall of one pair, and A arrives. -/
theorem left_restart (R : Tape) :
    steps 7 ⟨blank, cons true R, .C⟩ = some ⟨cons false (cons true blank), cons true (cons true R), .A⟩ := rfl

/-- The digits after a converting end event: the old wall, a 0, the marks of the carry, and a 1. -/
def convDigits (n : Nat) (xs : List Bool) : List Bool :=
  List.replicate n true ++ false :: (cind .a xs ++ [true])

/-- From the out-of-step turn at the right end to the next arrival, for every wall and every digit string. -/
theorem conv_back (n : Nat) (xs : List Bool) (q : Q) (acc : List (Bool × Bool))
    (ha : offPairs .a xs [(true, true)] = some (q, acc)) :
    ∃ s, steps s ⟨lt acc (wall n), cons true (cons true (cons true (cons true blank))), .C⟩ =
      some (arrival 1 (convDigits n xs) (cons true blank)) := by
  have hok := (ok_off xs .a q [(true, true)] acc ha rfl (fun _ => rfl)).1
  obtain ⟨s1, h1⟩ := cb_all acc true (wall n) (cons true (cons true (cons true blank))) hok
  rw [cunw_off xs .a q [(true, true)] acc true _ ha] at h1
  have e1 : cunw [(true, true)] (firstW .a xs true) (cells (cind .a xs) (cons true (cons true (cons true blank)))) =
      cons true (cells (false :: (cind .a xs ++ [true])) (cons true blank)) := by
    simp only [cunw, cells, cells_append]
    rfl
  rw [e1] at h1
  have h2 := wall_left_C n blank (cells (false :: (cind .a xs ++ [true])) (cons true blank))
  have h3 := left_restart (rep n [true, true] (cells (false :: (cind .a xs ++ [true])) (cons true blank)))
  have e3 : (⟨cons false (cons true blank), cons true (cons true
      (rep n [true, true] (cells (false :: (cind .a xs ++ [true])) (cons true blank)))), .A⟩ : Config) =
      arrival 1 (convDigits n xs) (cons true blank) := by
    simp only [arrival, convDigits, rep_ones, cells_append]
    rfl
  rw [e3] at h3
  exact ⟨_, steps_seq trans h1 (steps_seq trans h2 h3)⟩

/-- The carry reads the last cell, a 1, in state b: the wall of n + 1 pairs becomes digits. -/
theorem conv_event_b (n : Nat) (xs : List Bool) (h : exitQ .a xs = some .b) :
    ∃ s, 0 < s ∧ steps s (arrival (n + 1) xs (cons true blank)) =
      some (arrival 1 (convDigits n xs) (cons true blank)) := by
  obtain ⟨acc, ha⟩ := off_of_exit xs .a .b [(true, true)] h
  have h1 := fwd_c1 (wall n) (cells xs (cons true blank))
  obtain ⟨s2, h2⟩ := run_off xs .a (true, true) [] .b acc (wall n) (cons true blank) ha
  have h3 := turn_b1 (lt acc (wall n))
  obtain ⟨s4, h4⟩ := conv_back n xs .b acc ha
  exact ⟨_, by omega, steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 h4))⟩

/-- The carry reads the last cell, a 0, in state c: the same. -/
theorem conv_event_c (n : Nat) (xs : List Bool) (h : exitQ .a xs = some .c) :
    ∃ s, 0 < s ∧ steps s (arrival (n + 1) xs (cons false blank)) =
      some (arrival 1 (convDigits n xs) (cons true blank)) := by
  obtain ⟨acc, ha⟩ := off_of_exit xs .a .c [(true, true)] h
  have h1 := fwd_c1 (wall n) (cells xs (cons false blank))
  obtain ⟨s2, h2⟩ := run_off xs .a (true, true) [] .c acc (wall n) (cons false blank) ha
  have h3 := turn_c0 (lt acc (wall n))
  obtain ⟨s4, h4⟩ := conv_back n xs .c acc ha
  exact ⟨_, by omega, steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 h4))⟩

/-! ## The machine as a system of events -/

/-- An arrival with blank tape after the last cell: the wall has n + 1 pairs, the digits are xs, the last cell d. -/
structure Ev where
  n : Nat
  xs : List Bool
  d : Bool

def Ev.cfg (e : Ev) : Config := arrival (e.n + 1) e.xs (cons e.d blank)

/-- One sweep on (wall, digits, last cell); `none` when the machine halts in it. -/
def evstep (e : Ev) : Option Ev :=
  match carry .a e.xs with
  | some ys => some ⟨e.n + 1, ys, e.d⟩
  | none =>
    match exitQ .a e.xs, e.d with
    | some .a, false => some ⟨e.n + 1, thru .a e.xs, true⟩
    | some .a, true => some ⟨e.n + 1, thru .a e.xs ++ [true], true⟩
    | some .b, true => some ⟨0, convDigits e.n e.xs, true⟩
    | some .c, false => some ⟨0, convDigits e.n e.xs, true⟩
    | _, _ => none

theorem sweep_pos (n : Nat) (xs ys : List Bool) (h : carry .a xs = some ys) (R : Tape) :
    ∃ s, 0 < s ∧ steps s (arrival (n + 1) xs R) = some (arrival (n + 2) ys R) := by
  have h1 := fwd_c1 (wall n) (cells xs R)
  obtain ⟨s2, h2⟩ := run .a xs ys h (true, true) [] (wall n) R
  have h3 := back_end n (cells ys R)
  rw [wall_snoc] at h3
  exact ⟨_, by omega, steps_seq trans h1 (steps_seq trans h2 h3)⟩

/-- A sweep that does not halt: the machine goes from the arrival e to the arrival e'. -/
theorem evstep_some (e e' : Ev) (h : evstep e = some e') : ∃ s, 0 < s ∧ steps s e.cfg = some e'.cfg := by
  obtain ⟨n, xs, d⟩ := e
  unfold evstep at h
  simp only at h
  cases hc : carry .a xs with
  | some ys =>
    rw [hc] at h
    simp only [Option.some.injEq] at h
    subst h
    exact sweep_pos n xs ys hc _
  | none =>
    rw [hc] at h
    obtain ⟨q, hq⟩ := exit_of_carry_none xs .a hc
    rw [hq] at h
    cases q <;> cases d <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h
    · exact last_stop_event n xs hq
    · exact ext_event n xs hq
    · exact conv_event_b n xs hq
    · exact conv_event_c n xs hq

/-- A sweep that halts. -/
theorem evstep_none (e : Ev) (h : evstep e = none) : Halts trans e.cfg := by
  obtain ⟨n, xs, d⟩ := e
  unfold evstep at h
  simp only at h
  cases hc : carry .a xs with
  | some ys => rw [hc] at h; cases h
  | none =>
    rw [hc] at h
    obtain ⟨q, hq⟩ := exit_of_carry_none xs .a hc
    rw [hq] at h
    cases q <;> cases d <;> simp only [reduceCtorEq] at h
    · exact halt_event_b n xs hq
    · exact halt_event_c n xs hq

/-- k sweeps (`none` once the machine has halted). -/
def evrun : Nat → Ev → Option Ev
  | 0, e => some e
  | k + 1, e => (evrun k e).bind evstep

theorem evrun_reach (k : Nat) (e e' : Ev) (h : evrun k e = some e') :
    ∃ s, k ≤ s ∧ steps s e.cfg = some e'.cfg := by
  induction k generalizing e' with
  | zero =>
    simp only [evrun, Option.some.injEq] at h
    subst h
    exact ⟨0, Nat.le_refl _, rfl⟩
  | succ k ih =>
    simp only [evrun, Option.bind_eq_some_iff] at h
    obtain ⟨e1, h1, h2⟩ := h
    obtain ⟨s1, hk, hs1⟩ := ih e1 h1
    obtain ⟨s2, hp, hs2⟩ := evstep_some e1 e' h2
    exact ⟨s1 + s2, by omega, steps_seq trans hs1 hs2⟩

/-- **The machine is the event system.**  From an arrival with blank tape after the last cell, the machine halts
if and only if some sweep of the event system halts. -/
theorem halts_iff_events (e : Ev) : Halts trans e.cfg ↔ ∃ k, evrun k e = none := by
  constructor
  · intro hh
    apply Classical.byContradiction
    intro hne
    have hall : ∀ k, ∃ e', evrun k e = some e' := by
      intro k
      cases hk : evrun k e with
      | none => exact absurd ⟨k, hk⟩ hne
      | some e' => exact ⟨e', rfl⟩
    refine absurd hh (not_halts_of_forall trans ?_)
    apply forall_of_unbounded trans (fun s => ∃ c, steps s e.cfg = some c)
    · intro m
      obtain ⟨e', he⟩ := hall m
      obtain ⟨s, hs, hr⟩ := evrun_reach m e e' he
      exact ⟨s, hs, _, hr⟩
    · intro m hm
      exact hm
  · rintro ⟨k, hk⟩
    induction k with
    | zero => simp [evrun] at hk
    | succ k ih =>
      cases h1 : evrun k e with
      | none => exact ih h1
      | some e1 =>
        simp only [evrun, h1, Option.bind_some] at hk
        obtain ⟨s, -, hs⟩ := evrun_reach k e e1 h1
        exact halts_of_reach hs (evstep_none e1 hk)

/-- The run from blank tape: the machine halts if and only if the event system does, started from a wall of 10
pairs, the digits `X0` and last cell 1 (the arrival at step 30,225). -/
theorem blank_halts_iff_events : HaltsFromBlank ↔ ∃ k, evrun k ⟨9, X0, true⟩ = none := by
  rw [← halts_iff_events]
  exact halts_iff_of_steps first_arrival

/-! ## The run from blank tape after its first end event -/

theorem exit_Y0 : exitQ .a Y0 = some .b := by decide +kernel

/-- The first end event of the run from blank tape is a converting one: afterwards the counter is
8,072,508,832 ones, a 0, the 109 marks of the last carry and a 1, the last cell is 1, and the wall has one pair. -/
theorem second_arrival : ∃ s, steps s init = some (arrival 1 (convDigits 8072508832 Y0) (cons true blank)) := by
  obtain ⟨s1, -, h1⟩ := arrival_sweeps 8072508823 9 X0 Y0 (cons true blank) sweeps_X0
  obtain ⟨s2, -, h2⟩ := conv_event_b 8072508832 Y0 exit_Y0
  exact ⟨_, steps_seq trans first_arrival (steps_seq trans h1 h2)⟩

/-- The machine halts from blank tape if and only if the event system halts from the counter after the first end
event. -/
theorem blank_halts_iff_second :
    HaltsFromBlank ↔ ∃ k, evrun k ⟨0, convDigits 8072508832 Y0, true⟩ = none := by
  rw [← halts_iff_events]
  obtain ⟨s, h⟩ := second_arrival
  exact halts_iff_of_steps h

end H74982
