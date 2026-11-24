import Layers

/-! # The events after 10^128 events of 1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_1LE---: an empty Z and a chain of left words

The five left rows (`lv_d0` … `lv_top`) were written by
`holdouts/1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RA_0LB---/py/stage_rows.py`; the rest was written by hand.

**Why the stage law has the gifts it has.** After about 10^128 events the run reaches *stages* (`py/latestage.py`,
`py/stages.py`), where the head turns back again and again at one cell in state C on a 0. Those turning points are
not a new mechanism. They are events of the chain law of `Layers.lean` with the word Z **empty**:

    [left words] 0 | A> 0 (11 [Q] 01 [P] 10)* 11 [Q] 01 [R] ...

With Z empty, every event wraps Z, so every event sends one unit into the first item of the chain (`dU`). On the way
the head passes twice through the cell left of the event cell in state C on a 0: these are the two *visits* of a
stage, one in the middle of the unit and one just before the next event. So a pair of visits is one event.

On the left the event's increment (the cell left of the event cell in state D) runs through a chain of base-3 words
instead of the single counter N. The words are parted by `1010`, and the last one ends at the old top `0^inf 1 0`.
Cut leftwards from the head into *units*, each beginning with a 0 cell: a digit (`100` = 0, `110` = 1, `010` = 2),
a separator `1010`, and the top `10` before blank tape. One increment entering a unit in state D does this
(`LVis`, the mirror image of `Vis` in `Visit.lean`):

- digit 0 or 1: add 1, and leave in E;
- digit 2: becomes 0 and passes one increment to the next unit (a carry);
- separator: passes **two** increments to the next unit, so a wrap of a word adds 2 to the next word;
- top: a new digit 0 below it (the last word grows by a digit).

The chain may also end in any tape at all (`rest`, as R may be followed by any tape on the right): no visit reads it
unless a carry reaches it. Early in the first stage the last left word ends in such a tape, the rest of the old N.

The function `linc` computes this on the list of units. So each event adds 1 to the lowest left word, a word that
wraps sends 2 to the next, and an empty word (two separators in a row, as in the block `1010…1` of
`py/stages.py`) passes on twice what it got. On the right each event is one unit: Q₁ + 3, a wrap of Q adds 3 to P,
and a wrap of P sends a unit into the next item. These are the gifts that `py/stages.py` fitted.

`chain_event` holds for every Z, empty or not, every list of left units, and any tape after R. -/

namespace H64715

open TM

/-- One visit of the left tape in state `q`. The head is on the stream's first cell, which is a 0, and `y` is the
stream left of that cell. The first time the head leaves the stream to the right it is in state `r`, the cell it
lands on and everything right of it are untouched, and the stream is `0 y'`. -/
def LVis (q : St) (y : Tape) (r : St) (y' : Tape) : Prop :=
  ∀ (a : Bool) (R : Tape), ∃ t, steps t ⟨y, cons false (cons a R), q⟩ = some ⟨cons false y', cons a R, r⟩

/-- A visit in state C turns straight back in state A. -/
theorem lv_bounce (y : Tape) : LVis .C y .A y := fun _ _ => ⟨1, rfl⟩

/-- A digit 0 (`100`), entered in D: becomes 1, out in E. -/
theorem lv_d0 {z : Tape}  :
    LVis .D (cons false (cons true (cons false (z)))) .E (cons true (cons true (cons false (z)))) := by
  intro a R
  have s0 : steps 3 ⟨cons false (cons true (cons false (z))), cons false (cons a R), .D⟩ = some ⟨cons false (cons true (cons true (cons false (z)))), cons a R, .E⟩ := rfl
  exact ⟨_, s0⟩

/-- A digit 1 (`110`), entered in D: becomes 2, out in E. -/
theorem lv_d1 {z : Tape}  :
    LVis .D (cons true (cons true (cons false (z)))) .E (cons true (cons false (cons false (z)))) := by
  intro a R
  have s0 : steps 7 ⟨cons true (cons true (cons false (z))), cons false (cons a R), .D⟩ = some ⟨cons false (cons true (cons false (cons false (z)))), cons a R, .E⟩ := rfl
  exact ⟨_, s0⟩

/-- A digit 2 (`010`), entered in D: becomes 0 and carries (nested C→A, D→E, C→A), out in E. -/
theorem lv_d2 {z z1 z2 z3 : Tape} (h1 : LVis .C z .A z1) (h2 : LVis .D z1 .E z2) (h3 : LVis .C z2 .A z3) :
    LVis .D (cons true (cons false (cons false (z)))) .E (cons false (cons true (cons false (z3)))) := by
  intro a R
  have s0 : steps 3 ⟨cons true (cons false (cons false (z))), cons false (cons a R), .D⟩ = some ⟨z, cons false (cons false (cons false (cons true (cons a R)))), .C⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons false (cons true (cons a R)))
  have s1 : steps 3 ⟨cons false (z1), cons false (cons false (cons true (cons a R))), .A⟩ = some ⟨z1, cons false (cons false (cons true (cons true (cons a R)))), .D⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 false (cons true (cons true (cons a R)))
  have s2 : steps 1 ⟨cons false (z2), cons false (cons true (cons true (cons a R))), .E⟩ = some ⟨z2, cons false (cons false (cons true (cons true (cons a R)))), .C⟩ := rfl
  obtain ⟨t3, c3⟩ := h3 false (cons true (cons true (cons a R)))
  have s3 : steps 3 ⟨cons false (z3), cons false (cons true (cons true (cons a R))), .A⟩ = some ⟨cons false (cons false (cons true (cons false (z3)))), cons a R, .E⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (steps_seq trans s2 (steps_seq trans c3 (s3))))))⟩

/-- A separator `1010`, entered in D: passes two increments (nested D→E, C→A, D→E, C→A), out in E. -/
theorem lv_sep {z z1 z2 z3 z4 : Tape} (h1 : LVis .D z .E z1) (h2 : LVis .C z1 .A z2) (h3 : LVis .D z2 .E z3) (h4 : LVis .C z3 .A z4) :
    LVis .D (cons true (cons false (cons true (cons false (z))))) .E (cons true (cons false (cons true (cons false (z4))))) := by
  intro a R
  have s0 : steps 4 ⟨cons true (cons false (cons true (cons false (z)))), cons false (cons a R), .D⟩ = some ⟨z, cons false (cons false (cons false (cons false (cons true (cons a R))))), .D⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons false (cons false (cons true (cons a R))))
  have s1 : steps 1 ⟨cons false (z1), cons false (cons false (cons false (cons true (cons a R)))), .E⟩ = some ⟨z1, cons false (cons false (cons false (cons false (cons true (cons a R))))), .C⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 false (cons false (cons false (cons true (cons a R))))
  have s2 : steps 3 ⟨cons false (z2), cons false (cons false (cons false (cons true (cons a R)))), .A⟩ = some ⟨z2, cons false (cons false (cons true (cons false (cons true (cons a R))))), .D⟩ := rfl
  obtain ⟨t3, c3⟩ := h3 false (cons true (cons false (cons true (cons a R))))
  have s3 : steps 1 ⟨cons false (z3), cons false (cons true (cons false (cons true (cons a R)))), .E⟩ = some ⟨z3, cons false (cons false (cons true (cons false (cons true (cons a R))))), .C⟩ := rfl
  obtain ⟨t4, c4⟩ := h4 false (cons true (cons false (cons true (cons a R))))
  have s4 : steps 6 ⟨cons false (z4), cons false (cons true (cons false (cons true (cons a R)))), .A⟩ = some ⟨cons false (cons true (cons false (cons true (cons false (z4))))), cons a R, .E⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (steps_seq trans s2 (steps_seq trans c3 (steps_seq trans s3 (steps_seq trans c4 (s4))))))))⟩

/-- The top `1 0` and blank tape, entered in D: a new digit 0 below it, out in E. -/
theorem lv_top  :
    LVis .D (cons true (blank)) .E (cons false (cons true (cons false (cons true (blank))))) := by
  intro a R
  have s0 : steps 15 ⟨cons true (blank), cons false (cons a R), .D⟩ = some ⟨cons false (cons false (cons true (cons false (cons true (blank))))), cons a R, .E⟩ := rfl
  exact ⟨_, s0⟩

/-! ## The left units and their increment -/

/-- A unit of the left tape, read leftwards from its first cell (a 0): digits `100` = 0, `110` = 1, `010` = 2 of
a base-3 word, the separator `1010` between words, the top `10` before blank tape, or `rest`: any tape at all
(left of a 0 cell), which the law never reads unless a carry reaches it. -/
inductive LU where
  | d0 | d1 | d2 | sep | top | rest

/-- The left tape strictly left of the first unit's first cell; `BL` is the tape that `rest` stands for. -/
def lenc (BL : Tape) : List LU → Tape
  | [] => blank
  | .d0 :: r => cons false (cons true (cons false (lenc BL r)))
  | .d1 :: r => cons true (cons true (cons false (lenc BL r)))
  | .d2 :: r => cons true (cons false (cons false (lenc BL r)))
  | .sep :: r => cons true (cons false (cons true (cons false (lenc BL r))))
  | .top :: _ => cons true blank
  | .rest :: _ => BL

/-- One increment entering the first unit (`n` bounds the recursion; `none` when it runs out, when a carry reaches
`rest`, or for a list without an end). -/
def linc : Nat → List LU → Option (List LU)
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, .d0 :: r => some (.d1 :: r)
  | _ + 1, .d1 :: r => some (.d2 :: r)
  | n + 1, .d2 :: r => match linc n r with
    | none => none
    | some r' => some (.d0 :: r')
  | n + 1, .sep :: r => match linc n r with
    | none => none
    | some r1 => match linc n r1 with
      | none => none
      | some r2 => some (.sep :: r2)
  | _ + 1, .top :: _ => some [.d0, .top]
  | _ + 1, .rest :: _ => none

theorem linc_sound (BL : Tape) : ∀ (n : Nat) (us us' : List LU), linc n us = some us' →
    LVis .D (lenc BL us) .E (lenc BL us') := by
  intro n
  induction n with
  | zero => intro us us' h; simp [linc] at h
  | succ n ih =>
    intro us us' h
    match us with
    | [] => simp [linc] at h
    | .d0 :: r =>
      simp only [linc, Option.some.injEq] at h
      subst h
      exact lv_d0
    | .d1 :: r =>
      simp only [linc, Option.some.injEq] at h
      subst h
      exact lv_d1
    | .d2 :: r =>
      simp only [linc] at h
      cases h1 : linc n r with
      | none => simp [h1] at h
      | some r' =>
        simp only [h1, Option.some.injEq] at h
        subst h
        exact lv_d2 (lv_bounce _) (ih r r' h1) (lv_bounce _)
    | .sep :: r =>
      simp only [linc] at h
      cases h1 : linc n r with
      | none => simp [h1] at h
      | some r1 =>
        simp only [h1] at h
        cases h2 : linc n r1 with
        | none => simp [h2] at h
        | some r2 =>
          simp only [h2, Option.some.injEq] at h
          subst h
          exact lv_sep (ih r r1 h1) (lv_bounce _) (ih r1 r2 h2) (lv_bounce _)
    | .top :: _ =>
      simp only [linc, Option.some.injEq] at h
      subst h
      exact lv_top
    | .rest :: _ => simp [linc] at h

/-- **The end of an event on a chain of left words**: from the cell left of the event cell in state D, back on the
event cell in state A, with the left words increased by one (`linc`). On the way the head is in state C on that
cell, which is the second visit of the pair. -/
theorem left_end (BL : Tape) {n : Nat} {us us' : List LU} (h : linc n us = some us') (T : Tape) :
    ∃ t, steps t ⟨lenc BL us, cons false (cons false T), .D⟩ =
      some ⟨cons false (lenc BL us'), cons false T, .A⟩ := by
  obtain ⟨t1, h1⟩ := linc_sound BL n us us' h false T
  have h2 : steps 2 ⟨cons false (lenc BL us'), cons false T, .E⟩ =
      some ⟨cons false (lenc BL us'), cons false T, .A⟩ := rfl
  exact ⟨_, steps_seq trans h1 h2⟩

/-! ## The right half of an event with Z empty -/

variable {B : Tape}

/-- **An event with Z empty**: one unit into the chain. On the way the head is in state C on the cell left of the
event cell (the first visit of the pair). -/
theorem event_vis_empty {its : List Item} {l : Item} {r : List Item × Item}
    (h : dU (its.length + 1) its l = some r) (L : Tape) :
    ∃ t, steps t ⟨cons false L, cons false (encT B its l), .A⟩ =
      some ⟨L, cons false (cons false (encT B r.1 r.2)), .D⟩ := by
  obtain ⟨y1, y2, u1, ub, u2, u3⟩ := dU_sound (B := B) _ its l r h
  have s0 : steps 1 ⟨cons false L, cons false (encT B its l), .A⟩ = some ⟨cons true (cons false L), encT B its l, .B⟩ := rfl
  obtain ⟨t1, c1⟩ := u1 true (cons false L)
  have s1 : steps 1 ⟨cons false L, cons true y1, .E⟩ = some ⟨cons false (cons false L), y1, .E⟩ := rfl
  obtain ⟨t2, c2⟩ := ub false (cons false L)
  have s2 : steps 1 ⟨cons false L, cons false y1, .C⟩ = some ⟨cons false (cons false L), y1, .A⟩ := rfl
  obtain ⟨t3, c3⟩ := u2 false (cons false L)
  have s3 : steps 3 ⟨cons false L, cons false y2, .E⟩ = some ⟨cons true (cons false L), y2, .B⟩ := rfl
  obtain ⟨t4, c4⟩ := u3 true (cons false L)
  have s4 : steps 1 ⟨cons false L, cons true (encT B r.1 r.2), .C⟩ =
      some ⟨L, cons false (cons false (encT B r.1 r.2)), .D⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2
    (steps_seq trans s2 (steps_seq trans c3 (steps_seq trans s3 (steps_seq trans c4 s4)))))))⟩

/-- The right half of an event for every Z, empty or not (`evNext`). -/
theorem event_right {z : List Bool} {its : List Item} {l : Item} {r : List Bool × List Item × Item}
    (h : evNext z its l = some r) (L : Tape) :
    ∃ t, steps t ⟨cons false L, cons false (enc zd z (encT B its l)), .A⟩ =
      some ⟨L, cons false (cons false (enc zd r.1 (encT B r.2.1 r.2.2))), .D⟩ := by
  cases z with
  | nil =>
    simp only [evNext, incB] at h
    cases hu : dU (its.length + 1) its l with
    | none => simp [hu] at h
    | some x =>
      simp only [hu, Option.some.injEq] at h
      subst h
      exact event_vis_empty hu L
  | cons b w => exact event_vis (List.cons_ne_nil b w) h false L

/-! ## The law -/

/-- **The chain law with left words.** From one event to the next: the left words get one increment (`linc`) and
the right side moves by `evNext` (Z + 1, or with Z empty one unit into the chain), for every Z, every list of left
units, any tape `BL` for `rest` and any tape `B` after R. -/
theorem chain_event (BL : Tape) {n : Nat} {us us' : List LU} {z : List Bool} {its : List Item} {l : Item}
    {r : List Bool × List Item × Item} (hl : linc n us = some us') (h : evNext z its l = some r) :
    ∃ t, steps t ⟨cons false (lenc BL us), cons false (enc zd z (encT B its l)), .A⟩ =
      some ⟨cons false (lenc BL us'), cons false (enc zd r.1 (encT B r.2.1 r.2.2)), .A⟩ := by
  obtain ⟨t1, h1⟩ := event_right (B := B) h (lenc BL us)
  obtain ⟨t2, h2⟩ := left_end BL hl (enc zd r.1 (encT B r.2.1 r.2.2))
  exact ⟨_, steps_seq trans h1 h2⟩

end H64715
