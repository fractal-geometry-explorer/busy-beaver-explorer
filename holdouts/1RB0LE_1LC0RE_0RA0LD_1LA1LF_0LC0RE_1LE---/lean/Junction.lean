import Stage

/-! # The half-digit item of 1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_1LE---: what a wrap of its first word hands on

Written by hand.

At about 10^137 events (stage 13 of `py/stage_law.py`, and once before in stage 11) the chain holds an item outside
the grammar:

    11 [Q] 00 11 [Q2] 01 [P2] 10 11 …        where the grammar has  11 [Q] 01 [P] 10 11 [Q2] 01 [P2] 10 11 …

`chain_event_open` of `Stage.lean` covers it up to a wrap of Q. This file covers the wraps. The four cells after Q
(`0011`, the *junction*) act as one more digit of Q with two extra states:

- `A> 00 x`: the first wrap of Q turns `0011` into `0111` and the carry stops there (`l_c_A0`);
- `A> 0111 x` (`j_A1`): the second wrap turns `0111` into the Q digit `0001` and sends **two** increments into Q2.

After the second wrap the cells read in the grammar again, as one item whose Q is Q, the digit 0 and Q2 (`hld`): the
half-digit item has healed. So in value the junction is a digit worth 2 (`0011`) or 3 (`0111`) times its place, and
the item is the one word Q + 2^|Q|·(2 + b) + 2^(|Q|+1)·Q2: every event still adds exactly one to the number of
`Layers.lean`.

`chain_event_junction` is the chain law with left words and such an item anywhere in the chain (items before it,
and after it the item (Q2, P2) and the rest of the chain up to R), for every width, until a carry leaves R. It is
`none` only where a carry leaves R, or where the junction would wrap into an empty Q2 (not met in the run). -/

namespace H64715

open TM

variable {B : Tape}

/-- A visit in E bounces off any stream that starts with a 0. -/
theorem e_bounce0 (x : Tape) : Vis .E (cons false x) .C (cons false x) := fun _ _ => ⟨1, rfl⟩

/-- `A> 0111 x`, nested visits E→C A→D E→C A→D: out in state D, leaving `0001 x'`. The closed junction: a carry
into it leaves the Q digit 0 and sends two increments on. -/
theorem j_A1 {x x1 x2 x3 x4 : Tape} (h1 : Vis .E x .C x1) (h2 : Vis .A x1 .D x2) (h3 : Vis .E x2 .C x3)
    (h4 : Vis .A x3 .D x4) :
    Vis .A (cons false (cons true (cons true (cons true x)))) .D
      (cons false (cons false (cons false (cons true x4)))) := by
  intro a L
  have s0 : steps 4 ⟨cons a L, cons false (cons true (cons true (cons true x))), .A⟩ =
      some ⟨cons false (cons false (cons false (cons true (cons a L)))), x, .E⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons false (cons false (cons true (cons a L))))
  have s1 : steps 1 ⟨cons false (cons false (cons true (cons a L))), cons false x1, .C⟩ =
      some ⟨cons false (cons false (cons false (cons true (cons a L)))), x1, .A⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 false (cons false (cons false (cons true (cons a L))))
  have s2 : steps 3 ⟨cons false (cons false (cons true (cons a L))), cons false x2, .D⟩ =
      some ⟨cons false (cons true (cons false (cons true (cons a L)))), x2, .E⟩ := rfl
  obtain ⟨t3, c3⟩ := h3 false (cons true (cons false (cons true (cons a L))))
  have s3 : steps 1 ⟨cons true (cons false (cons true (cons a L))), cons false x3, .C⟩ =
      some ⟨cons false (cons true (cons false (cons true (cons a L)))), x3, .A⟩ := rfl
  obtain ⟨t4, c4⟩ := h4 false (cons true (cons false (cons true (cons a L))))
  have s4 : steps 4 ⟨cons true (cons false (cons true (cons a L))), cons false x4, .D⟩ =
      some ⟨L, cons a (cons false (cons false (cons false (cons true x4)))), .D⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2
    (steps_seq trans s2 (steps_seq trans c3 (steps_seq trans s3 (steps_seq trans c4 s4)))))))⟩

/-- An increment of a Q word followed by any tape X that a visit in E bounces off: a wrap is one visit A → D of X. -/
theorem q_inc_any (q : List Bool) {X X' : Tape} (hb : Vis .E X .C X) (h1 : (incB q).2 = true → Vis .A X .D X')
    (h2 : (incB q).2 = false → X' = X) : Vis .A (enc qd q X) .D (enc qd (incB q).1 X') := by
  induction q with
  | nil => exact h1 rfl
  | cons b w ih =>
    cases b with
    | false =>
      have e : X' = X := h2 rfl
      subst e
      exact l_q_A_0
    | true =>
      cases w with
      | nil => exact l_q_A_1d hb (h1 rfl)
      | cons c w => exact l_q_A_1d (q_bounce_open _ (List.cons_ne_nil c w) X) (ih h1 h2)

theorem enc_append (d : Bool → List Bool) (a c : List Bool) (s : Tape) : enc d (a ++ c) s = enc d a (enc d c s) := by
  induction a with
  | nil => rfl
  | cons b w ih => simp only [List.cons_append, enc, ih]

/-! ## The half-digit item from its first word on -/

/-- The half-digit item: not yet healed (Q, the junction `0011` (b = false) or `0111` (b = true), then the item
(Q2, P2) and what follows P2), or healed (one item of the grammar). -/
inductive JW (σ : Type)
  | unh (q : List Bool) (b : Bool) (q2 p2 : List Bool) (s : σ)
  | hld (q p : List Bool) (s : σ)

section
variable {σ : Type} (k : σ → Option σ) (te : σ → Tape)

/-- The tape from the item's first word on. -/
def jT : JW σ → Tape
  | .unh q b q2 p2 s => enc qd q (cons false (cons b (cons true (cons true (QT te q2 p2 s)))))
  | .hld q p s => QT te q p s

/-- One increment of the item's first word (`k`: the unit sent on when P2 wraps). -/
def jInc : JW σ → Option (JW σ)
  | .hld [] _ _ => none
  | .hld (b :: w) p s => match qInc k (b :: w) p s with
    | none => none
    | some x => some (.hld x.1 x.2.1 x.2.2)
  | .unh q b q2 p2 s =>
    match (incB q).2, b with
    | false, _ => some (.unh (incB q).1 b q2 p2 s)
    | true, false => some (.unh (incB q).1 true q2 p2 s)
    | true, true => match q2 with
      | [] => none
      | c :: w => match qInc k (c :: w) p2 s with
        | none => none
        | some x => match qInc k x.1 x.2.1 x.2.2 with
          | none => none
          | some y => some (.hld ((incB q).1 ++ false :: y.1) y.2.1 y.2.2)

/-- A unit into the item: three increments of its first word. -/
def jUnit (w : JW σ) : Option (JW σ) :=
  match jInc k w with
  | none => none
  | some w1 => match jInc k w1 with
    | none => none
    | some w2 => jInc k w2

theorem j_bounce (w : JW σ) : Vis .E (jT te w) .C (jT te w) := by
  cases w with
  | unh q b q2 p2 s =>
    cases q with
    | nil => exact e_bounce0 _
    | cons c w => exact q_bounce_open _ (List.cons_ne_nil c w) _
  | hld q p s => exact q_bounce _ _

theorem qInc_ne_nil {q p : List Bool} {s : σ} {r : List Bool × List Bool × σ} (h : qInc k q p s = some r)
    (hq : q ≠ []) : r.1 ≠ [] := by
  intro e
  have w := qInc_width k h
  rw [e] at w
  exact hq (List.length_eq_zero_iff.mp w.symm)

variable (hk : ∀ s s', k s = some s' → PS (te s) (te s'))
include hk

theorem jInc_sound {w w' : JW σ} (h : jInc k w = some w') : Vis .A (jT te w) .D (jT te w') := by
  cases w with
  | hld q p s =>
    cases q with
    | nil => simp [jInc] at h
    | cons b w =>
      simp only [jInc] at h
      cases hx : qInc k (b :: w) p s with
      | none => simp [hx] at h
      | some x =>
        simp only [hx, Option.some.injEq] at h
        subst h
        exact (qInc_sound k te hk hx).1 (List.cons_ne_nil b w)
  | unh q b q2 p2 s =>
    cases hc : (incB q).2 with
    | false =>
      simp only [jInc, hc, Option.some.injEq] at h
      subst h
      exact q_inc_any q (e_bounce0 _) (fun e => by rw [hc] at e; cases e) (fun _ => rfl)
    | true =>
      cases b with
      | false =>
        simp only [jInc, hc, Option.some.injEq] at h
        subst h
        exact q_inc_any q (e_bounce0 _) (fun _ => l_c_A0) (fun e => by rw [hc] at e; cases e)
      | true =>
        cases q2 with
        | nil => simp [jInc, hc] at h
        | cons c w =>
          simp only [jInc, hc] at h
          cases hx : qInc k (c :: w) p2 s with
          | none => simp [hx] at h
          | some x =>
            simp only [hx] at h
            cases hy : qInc k x.1 x.2.1 x.2.2 with
            | none => simp [hy] at h
            | some y =>
              simp only [hy, Option.some.injEq] at h
              subst h
              have a1 := (qInc_sound k te hk hx).1 (List.cons_ne_nil c w)
              have a2 := (qInc_sound k te hk hy).1 (qInc_ne_nil k hx (List.cons_ne_nil c w))
              have r := j_A1 (q_bounce _ _) a1 (q_bounce _ _) a2
              show Vis .A (enc qd q _) .D (enc qd ((incB q).1 ++ false :: y.1) _)
              rw [enc_append]
              exact q_inc_any q (e_bounce0 _) (fun _ => r) (fun e => by rw [hc] at e; cases e)

theorem jUnit_sound {w w' : JW σ} (h : jUnit k w = some w') :
    UD (cons true (cons true (jT te w))) (cons true (cons true (jT te w'))) := by
  unfold jUnit at h
  cases h1 : jInc k w with
  | none => simp [h1] at h
  | some w1 =>
    simp only [h1] at h
    cases h2 : jInc k w1 with
    | none => simp [h2] at h
    | some w2 =>
      simp only [h2] at h
      exact ud_d (j_bounce te w) (jInc_sound k te hk h1) (j_bounce te w1) (jInc_sound k te hk h2)
        (j_bounce te w2) (jInc_sound k te hk h)

end

/-! ## The chain with a half-digit item -/

/-- What follows P2: the block `10` and the rest of the chain up to R, then any tape `B`. -/
def teC (B : Tape) (s : List Item × Item) : Tape := cons true (cons false (encT B s.1 s.2))

/-- The unit that a wrap of P2 sends into the rest of the chain. -/
def kC (s : List Item × Item) : Option (List Item × Item) := dU (s.1.length + 1) s.1 s.2

theorem hkC : ∀ s s', kC s = some s' → PS (teC B s) (teC B s') :=
  fun s _ e => a_ps (dU_sound _ s.1 s.2 _ e)

abbrev JWC := JW (List Item × Item)

/-- The tape from the first item on: the items `its` of the grammar, then the half-digit item `11 …`. -/
def encJ (B : Tape) : List Item → JWC → Tape
  | [], w => cons true (cons true (jT (teC B) w))
  | i :: rest, w =>
    cons true (cons true (enc qd i.1 (cons false (cons true (enc pd i.2 (cons true (cons false (encJ B rest w))))))))

/-- Once healed, the chain is one of the grammar again. -/
theorem encJ_hld (its : List Item) (q p : List Bool) (s : List Item × Item) :
    encJ B its (.hld q p s) = encT B (its ++ (q, p) :: s.1) s.2 := by
  induction its with
  | nil => rfl
  | cons i rest ih => simp only [encJ, List.cons_append, encT, ih]

/-- A unit into the chain with a half-digit item (`none` when a carry leaves R). -/
def dUJ : Nat → List Item → JWC → Option (List Item × JWC)
  | 0, _, _ => none
  | _ + 1, [], w => match jUnit kC w with
    | none => none
    | some w' => some ([], w')
  | n + 1, i :: rest, w => match qUnit (fun s : List Item × JWC => dUJ n s.1 s.2) i.1 i.2 (rest, w) with
    | none => none
    | some x => some ((x.1, x.2.1) :: x.2.2.1, x.2.2.2)

theorem dUJ_sound : ∀ (n : Nat) (its : List Item) (w : JWC) (r : List Item × JWC), dUJ n its w = some r →
    UD (encJ B its w) (encJ B r.1 r.2) := by
  intro n
  induction n with
  | zero => intro its w r h; simp [dUJ] at h
  | succ n ih =>
    intro its w r h
    cases its with
    | nil =>
      simp only [dUJ] at h
      cases hu : jUnit kC w with
      | none => simp [hu] at h
      | some w' =>
        simp only [hu, Option.some.injEq] at h
        subst h
        exact jUnit_sound kC (teC B) hkC hu
    | cons i rest =>
      simp only [dUJ] at h
      cases hu : qUnit (fun s : List Item × JWC => dUJ n s.1 s.2) i.1 i.2 (rest, w) with
      | none => simp [hu] at h
      | some x =>
        simp only [hu, Option.some.injEq] at h
        subst h
        exact qUnit_sound (fun s : List Item × JWC => dUJ n s.1 s.2)
          (fun s : List Item × JWC => cons true (cons false (encJ B s.1 s.2)))
          (fun s s' e => a_ps (ih s.1 s.2 s' e)) hu

/-- The next event's Z and chain with a half-digit item (`none` when a carry leaves R). -/
def evNextJ (z : List Bool) (its : List Item) (w : JWC) : Option (List Bool × List Item × JWC) :=
  match (incB z).2 with
  | false => some ((incB z).1, its, w)
  | true => match dUJ (its.length + 1) its w with
    | none => none
    | some r => some ((incB z).1, r.1, r.2)

theorem event_right_junction {z : List Bool} {its : List Item} {w : JWC} {r : List Bool × List Item × JWC}
    (h : evNextJ z its w = some r) (L : Tape) :
    ∃ t, steps t ⟨cons false L, cons false (enc zd z (encJ B its w)), .A⟩ =
      some ⟨L, cons false (cons false (enc zd r.1 (encJ B r.2.1 r.2.2))), .D⟩ := by
  unfold evNextJ at h
  cases hc : (incB z).2 with
  | false =>
    simp only [hc, Option.some.injEq] at h
    subst h
    cases z with
    | nil => simp [incB] at hc
    | cons b w' =>
      exact l_e (z_inc (b :: w') (List.cons_ne_nil b w') (fun e => by rw [hc] at e; cases e) (fun _ => rfl)) false L
  | true =>
    simp only [hc] at h
    cases hu : dUJ (its.length + 1) its w with
    | none => simp [hu] at h
    | some x =>
      simp only [hu, Option.some.injEq] at h
      subst h
      have hd := dUJ_sound (B := B) _ its w x hu
      cases z with
      | nil =>
        obtain ⟨y1, y2, u1, ub, u2, u3⟩ := hd
        have s0 : steps 1 ⟨cons false L, cons false (encJ B its w), .A⟩ =
            some ⟨cons true (cons false L), encJ B its w, .B⟩ := rfl
        obtain ⟨t1, c1⟩ := u1 true (cons false L)
        have s1 : steps 1 ⟨cons false L, cons true y1, .E⟩ = some ⟨cons false (cons false L), y1, .E⟩ := rfl
        obtain ⟨t2, c2⟩ := ub false (cons false L)
        have s2 : steps 1 ⟨cons false L, cons false y1, .C⟩ = some ⟨cons false (cons false L), y1, .A⟩ := rfl
        obtain ⟨t3, c3⟩ := u2 false (cons false L)
        have s3 : steps 3 ⟨cons false L, cons false y2, .E⟩ = some ⟨cons true (cons false L), y2, .B⟩ := rfl
        obtain ⟨t4, c4⟩ := u3 true (cons false L)
        have s4 : steps 1 ⟨cons false L, cons true (encJ B x.1 x.2), .C⟩ =
            some ⟨L, cons false (cons false (encJ B x.1 x.2)), .D⟩ := rfl
        exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2
          (steps_seq trans s2 (steps_seq trans c3 (steps_seq trans s3 (steps_seq trans c4 s4)))))))⟩
      | cons b w' =>
        exact l_e (z_inc (b :: w') (List.cons_ne_nil b w') (fun _ => hd) (fun e => by rw [hc] at e; cases e)) false L

/-- **The chain law with left words and a half-digit item.** As `chain_event`, with the chain holding the item
`11 [Q] J [Q2] 01 [P2]` (J = `0011` or `0111`) after the items `its`: a unit adds 3 to Q; a wrap of Q turns `0011`
into `0111`, or turns `0111` into the digit 0 of one healed word Q 0 Q2 and adds 2 to Q2 (a wrap of Q2 adds 3 to
P2, a wrap of P2 sends a unit on, as in the grammar). -/
theorem chain_event_junction (BL : Tape) {n : Nat} {us us' : List LU} {z : List Bool} {its : List Item} {w : JWC}
    {r : List Bool × List Item × JWC} (hl : linc n us = some us') (h : evNextJ z its w = some r) :
    ∃ t, steps t ⟨cons false (lenc BL us), cons false (enc zd z (encJ B its w)), .A⟩ =
      some ⟨cons false (lenc BL us'), cons false (enc zd r.1 (encJ B r.2.1 r.2.2)), .A⟩ := by
  obtain ⟨t1, h1⟩ := event_right_junction (B := B) h (lenc BL us)
  obtain ⟨t2, h2⟩ := left_end BL hl (enc zd r.1 (encJ B r.2.1 r.2.2))
  exact ⟨_, steps_seq trans h1 h2⟩

end H64715
