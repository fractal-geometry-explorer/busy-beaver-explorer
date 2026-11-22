/-! ## Words and their increments -/

/-- A digit of Z: `0010` = 0, `1010` = 1. -/
def zd : Bool → List Bool
  | false => [false, false, true, false]
  | true => [true, false, true, false]

/-- A digit of Q: `0001` = 0, `0101` = 1. -/
def qd : Bool → List Bool
  | false => [false, false, false, true]
  | true => [false, true, false, true]

/-- A digit of P (and R): `1000` = 0, `1010` = 1. -/
def pd : Bool → List Bool
  | false => [true, false, false, false]
  | true => [true, false, true, false]

/-- A word of digits (lowest first) in front of a stream. -/
def enc (d : Bool → List Bool) : List Bool → Tape → Tape
  | [], s => s
  | b :: w, s => app (d b) (enc d w s)

/-- Binary increment, lowest digit first: the new digits and whether the word wrapped. -/
def incB : List Bool → List Bool × Bool
  | [] => ([], true)
  | false :: w => (true :: w, false)
  | true :: w => (false :: (incB w).1, (incB w).2)

theorem incB_length (w : List Bool) : (incB w).1.length = w.length := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> simp [incB, ih]

/-- A visit of a P stream in state F or B that comes out in E (one increment). -/
def PS (x x' : Tape) : Prop := Vis .F x .E x' ∧ Vis .B x .E x'

/-- Three visits F, F, B, each out in E: an addition of 3 to a P stream. -/
def UP (x x' : Tape) : Prop := ∃ x1 x2, Vis .F x .E x1 ∧ Vis .F x1 .E x2 ∧ Vis .B x2 .E x'

/-- A unit into an item: three visits B → F, A → F, B → C. -/
def UD (y y' : Tape) : Prop := ∃ y1 y2, Vis .B y .F y1 ∧ Vis .A y1 .F y2 ∧ Vis .B y2 .C y'

/-- An increment of an empty Q: two visits A → C, A → D. -/
def IAcd (y y' : Tape) : Prop := ∃ y1, Vis .A y .C y1 ∧ Vis .A y1 .D y'

/-! ## P: increments -/

theorem p_inc (p : List Bool) {T T' : Tape} (h1 : (incB p).2 = true → PS T T') (h2 : (incB p).2 = false → T' = T) :
    PS (enc pd p T) (enc pd (incB p).1 T') := by
  induction p with
  | nil => exact h1 rfl
  | cons b w ih =>
    cases b with
    | false =>
      have e : T' = T := h2 rfl
      subst e
      exact ⟨l_p_F_0, l_p_B_0⟩
    | true =>
      have h := ih h1 h2
      exact ⟨l_p_F_1 h.2, l_p_B_1 h.2⟩

/-- The block `10` after P passes a unit on. -/
theorem a_ps {Y Y' : Tape} (h : UD Y Y') : PS (cons true (cons false Y)) (cons true (cons false Y')) := by
  obtain ⟨y1, y2, h1, h2, h3⟩ := h
  exact ⟨l_a_F h1 h2 h3, l_a_B h1 h2 h3⟩

/-! ## Q: increments -/

/-- A visit in F bounces off every Q stream (it starts with a 0). -/
theorem q_bounce (w : List Bool) (X : Tape) :
    Vis .F (enc qd w (cons false (cons true X))) .C (enc qd w (cons false (cons true X))) := by
  cases w with
  | nil => exact l_c_F
  | cons b w => cases b with
    | false => exact l_q_F_0
    | true => exact l_q_F_1

theorem q_inc (q : List Bool) {X X' : Tape} (h1 : (incB q).2 = true → UP X X') (h2 : (incB q).2 = false → X' = X) :
    (q ≠ [] → Vis .A (enc qd q (cons false (cons true X))) .D (enc qd (incB q).1 (cons false (cons true X')))) ∧
    (q = [] → IAcd (enc qd q (cons false (cons true X))) (enc qd (incB q).1 (cons false (cons true X')))) := by
  induction q with
  | nil =>
    refine ⟨fun h => absurd rfl h, fun _ => ?_⟩
    obtain ⟨x1, x2, u1, u2, u3⟩ := h1 rfl
    exact ⟨_, l_c_A u1 u2 u3, l_c_A0⟩
  | cons b w ih =>
    refine ⟨fun _ => ?_, fun h => absurd h (List.cons_ne_nil b w)⟩
    cases b with
    | false =>
      have e : X' = X := h2 rfl
      subst e
      exact l_q_A_0
    | true =>
      have ih' := ih h1 h2
      cases w with
      | nil => obtain ⟨y1, c1, c2⟩ := ih'.2 rfl; exact l_q_A_1cd (q_bounce [] X) c1 c2
      | cons c w => exact l_q_A_1d (q_bounce _ X) (ih'.1 (List.cons_ne_nil c w))

/-- A unit into `11 [Q] …` when Q is not empty: three increments of Q. -/
theorem ud_d {Y Y1 Y2 Y3 : Tape} (h1 : Vis .A Y .D Y1) (h2 : Vis .A Y1 .D Y2) (hb : Vis .F Y2 .C Y2)
    (h3 : Vis .A Y2 .D Y3) : UD (cons true (cons true Y)) (cons true (cons true Y3)) :=
  ⟨_, _, l_d_B_dd h1 h2, l_d_A_d hb h3, l_d_B_01⟩

/-- A unit into `11 01 …` (Q empty): three increments, each two visits. -/
theorem ud_cd {Y Y1 Y2 Y3 : Tape} (h1 : IAcd Y Y1) (h2 : IAcd Y1 Y2) (hb : Vis .F Y2 .C Y2)
    (h3 : IAcd Y2 Y3) : UD (cons true (cons true Y)) (cons true (cons true Y3)) := by
  obtain ⟨a1, a2, a3⟩ := h1
  obtain ⟨b1, b2, b3⟩ := h2
  obtain ⟨c1, c2, c3⟩ := h3
  exact ⟨_, _, l_d_B_cdcd a2 a3 b2 b3, l_d_A_cd hb c2 c3, l_d_B_01⟩

/-! ## The carry law as functions on the digits

`σ` is what follows P (the rest of the chain), `k` the unit sent into it when P wraps (`none`: not covered). -/

section
variable {σ : Type} (k : σ → Option σ)

/-- One increment of P. -/
def pInc (p : List Bool) (s : σ) : Option (List Bool × σ) :=
  match (incB p).2 with
  | false => some ((incB p).1, s)
  | true => match k s with
    | none => none
    | some s' => some ((incB p).1, s')

/-- Three increments of P. -/
def pUnit (p : List Bool) (s : σ) : Option (List Bool × σ) :=
  match pInc k p s with
  | none => none
  | some x => match pInc k x.1 x.2 with
    | none => none
    | some y => pInc k y.1 y.2

/-- One increment of Q (a wrap adds 3 to P). -/
def qInc (q p : List Bool) (s : σ) : Option (List Bool × List Bool × σ) :=
  match (incB q).2 with
  | false => some ((incB q).1, p, s)
  | true => match pUnit k p s with
    | none => none
    | some x => some ((incB q).1, x.1, x.2)

/-- A unit into an item: three increments of Q. -/
def qUnit (q p : List Bool) (s : σ) : Option (List Bool × List Bool × σ) :=
  match qInc k q p s with
  | none => none
  | some x => match qInc k x.1 x.2.1 x.2.2 with
    | none => none
    | some y => qInc k y.1 y.2.1 y.2.2

theorem qInc_width {q p : List Bool} {s : σ} {r : List Bool × List Bool × σ} (h : qInc k q p s = some r) :
    r.1.length = q.length := by
  unfold qInc at h
  cases hc : (incB q).2 with
  | false =>
    simp only [hc, Option.some.injEq] at h
    subst h; exact incB_length q
  | true =>
    simp only [hc] at h
    cases hu : pUnit k p s with
    | none => simp [hu] at h
    | some x =>
      simp only [hu, Option.some.injEq] at h
      subst h; exact incB_length q

variable (te : σ → Tape) (hk : ∀ s s', k s = some s' → PS (te s) (te s'))
include hk

theorem pInc_sound {p : List Bool} {s : σ} {r : List Bool × σ} (h : pInc k p s = some r) :
    PS (enc pd p (te s)) (enc pd r.1 (te r.2)) := by
  unfold pInc at h
  cases hc : (incB p).2 with
  | false =>
    simp only [hc, Option.some.injEq] at h
    subst h
    exact p_inc p (fun e => by rw [hc] at e; cases e) (fun _ => rfl)
  | true =>
    simp only [hc] at h
    cases hs : k s with
    | none => simp [hs] at h
    | some s' =>
      simp only [hs, Option.some.injEq] at h
      subst h
      exact p_inc p (fun _ => hk s s' hs) (fun e => by rw [hc] at e; cases e)

theorem pUnit_sound {p : List Bool} {s : σ} {r : List Bool × σ} (h : pUnit k p s = some r) :
    UP (enc pd p (te s)) (enc pd r.1 (te r.2)) := by
  unfold pUnit at h
  cases h1 : pInc k p s with
  | none => simp [h1] at h
  | some x =>
    simp only [h1] at h
    cases h2 : pInc k x.1 x.2 with
    | none => simp [h2] at h
    | some y =>
      simp only [h2] at h
      exact ⟨_, _, (pInc_sound k te hk h1).1, (pInc_sound k te hk h2).1, (pInc_sound k te hk h).2⟩

/-- The tape from Q on: `[Q] 01 [P] (what follows P)`. -/
def QT (q p : List Bool) (s : σ) : Tape := enc qd q (cons false (cons true (enc pd p (te s))))

theorem qInc_sound {q p : List Bool} {s : σ} {r : List Bool × List Bool × σ} (h : qInc k q p s = some r) :
    (q ≠ [] → Vis .A (QT te q p s) .D (QT te r.1 r.2.1 r.2.2)) ∧ (q = [] → IAcd (QT te q p s) (QT te r.1 r.2.1 r.2.2)) := by
  unfold qInc at h
  cases hc : (incB q).2 with
  | false =>
    simp only [hc, Option.some.injEq] at h
    subst h
    exact q_inc q (fun e => by rw [hc] at e; cases e) (fun _ => rfl)
  | true =>
    simp only [hc] at h
    cases hu : pUnit k p s with
    | none => simp [hu] at h
    | some x =>
      simp only [hu, Option.some.injEq] at h
      subst h
      exact q_inc q (fun _ => pUnit_sound k te hk hu) (fun e => by rw [hc] at e; cases e)

theorem qUnit_sound {q p : List Bool} {s : σ} {r : List Bool × List Bool × σ} (h : qUnit k q p s = some r) :
    UD (cons true (cons true (QT te q p s))) (cons true (cons true (QT te r.1 r.2.1 r.2.2))) := by
  unfold qUnit at h
  cases h1 : qInc k q p s with
  | none => simp [h1] at h
  | some x =>
    simp only [h1] at h
    cases h2 : qInc k x.1 x.2.1 x.2.2 with
    | none => simp [h2] at h
    | some y =>
      simp only [h2] at h
      have w1 := qInc_width k h1
      have w2 := qInc_width k h2
      have hb : Vis .F (QT te y.1 y.2.1 y.2.2) .C (QT te y.1 y.2.1 y.2.2) := q_bounce _ _
      have s1 := qInc_sound k te hk h1
      have s2 := qInc_sound k te hk h2
      have s3 := qInc_sound k te hk h
      cases q with
      | nil =>
        have ex : x.1 = [] := List.length_eq_zero_iff.mp (by simpa using w1)
        have ey : y.1 = [] := List.length_eq_zero_iff.mp (by rw [w2, ex]; rfl)
        exact ud_cd (s1.2 rfl) (s2.2 ex) hb (s3.2 ey)
      | cons b w =>
        have ex : x.1 ≠ [] := fun e => by rw [e] at w1; simp at w1
        have ey : y.1 ≠ [] := fun e => by rw [e] at w2; exact ex (List.length_eq_zero_iff.mp (by simpa using w2.symm))
        exact ud_d (s1.1 (List.cons_ne_nil b w)) (s2.1 ex) hb (s3.1 ey)

end

/-! ## The chain of items -/

/-- An item: its words Q and P. -/
abbrev Item := List Bool × List Bool

/-- The tape from the first item on: `(11 [Q] 01 [P] 10)* 11 [Q] 01 [R] 0^inf`, the last item `l` holding R. -/
def encT : List Item → Item → Tape
  | [], l => cons true (cons true (enc qd l.1 (cons false (cons true (enc pd l.2 blank)))))
  | i :: rest, l =>
    cons true (cons true (enc qd i.1 (cons false (cons true (enc pd i.2 (cons true (cons false (encT rest l))))))))

/-- A unit into the chain (`n` bounds the recursion; `none` when a carry leaves R). -/
def dU : Nat → List Item → Item → Option (List Item × Item)
  | 0, _, _ => none
  | _ + 1, [], l => match qUnit (σ := Unit) (fun _ => none) l.1 l.2 () with
    | none => none
    | some x => some ([], (x.1, x.2.1))
  | n + 1, i :: rest, l => match qUnit (fun s : List Item × Item => dU n s.1 s.2) i.1 i.2 (rest, l) with
    | none => none
    | some x => some ((x.1, x.2.1) :: x.2.2.1, x.2.2.2)

theorem dU_sound : ∀ (n : Nat) (its : List Item) (l : Item) (r : List Item × Item), dU n its l = some r →
    UD (encT its l) (encT r.1 r.2) := by
  intro n
  induction n with
  | zero => intro its l r h; simp [dU] at h
  | succ n ih =>
    intro its l r h
    cases its with
    | nil =>
      simp only [dU] at h
      cases hu : qUnit (σ := Unit) (fun _ => none) l.1 l.2 () with
      | none => simp [hu] at h
      | some x =>
        simp only [hu, Option.some.injEq] at h
        subst h
        exact qUnit_sound (σ := Unit) (fun _ => none) (fun _ => blank) (fun _ _ e => by cases e) hu
    | cons i rest =>
      simp only [dU] at h
      cases hu : qUnit (fun s : List Item × Item => dU n s.1 s.2) i.1 i.2 (rest, l) with
      | none => simp [hu] at h
      | some x =>
        simp only [hu, Option.some.injEq] at h
        subst h
        exact qUnit_sound (fun s : List Item × Item => dU n s.1 s.2)
          (fun s : List Item × Item => cons true (cons false (encT s.1 s.2)))
          (fun s s' e => a_ps (ih s.1 s.2 s' e)) hu

/-! ## Z and the event -/

theorem z_inc (z : List Bool) (hz : z ≠ []) {T T' : Tape} (h1 : (incB z).2 = true → UD T T')
    (h2 : (incB z).2 = false → T' = T) : Vis .B (enc zd z T) .C (enc zd (incB z).1 T') := by
  induction z with
  | nil => exact absurd rfl hz
  | cons b w ih =>
    cases b with
    | false =>
      have e : T' = T := h2 rfl
      subst e
      exact l_z_B_0
    | true =>
      cases w with
      | nil =>
        obtain ⟨y1, y2, u1, u2, u3⟩ := h1 rfl
        exact l_z_B_1u u1 u2 u3
      | cons c w => exact l_z_B_1c (ih (List.cons_ne_nil c w) h1 h2)

/-- The next event's Z and chain (`none` when a carry leaves R). -/
def evNext (z : List Bool) (its : List Item) (l : Item) : Option (List Bool × List Item × Item) :=
  match (incB z).2 with
  | false => some ((incB z).1, its, l)
  | true => match dU (its.length + 1) its l with
    | none => none
    | some r => some ((incB z).1, r.1, r.2)

/-- **The right half of an event, for every layout.** -/
theorem event_vis {z : List Bool} {its : List Item} {l : Item} {r : List Bool × List Item × Item}
    (hz : z ≠ []) (h : evNext z its l = some r) :
    Vis .A (cons false (enc zd z (encT its l))) .D (cons false (enc zd r.1 (encT r.2.1 r.2.2))) := by
  unfold evNext at h
  cases hc : (incB z).2 with
  | false =>
    simp only [hc, Option.some.injEq] at h
    subst h
    exact l_e (z_inc z hz (fun e => by rw [hc] at e; cases e) (fun _ => rfl))
  | true =>
    simp only [hc] at h
    cases hu : dU (its.length + 1) its l with
    | none => simp [hu] at h
    | some x =>
      simp only [hu, Option.some.injEq] at h
      subst h
      exact l_e (z_inc z hz (fun _ => dU_sound _ its l x hu) (fun e => by rw [hc] at e; cases e))

/-- **The layer law.**  If the end of the event (from the cell left of the event cell, in state D, to the next
event) is the step of N from `L0` to `L1`, the machine goes from the event to the next one with the right side
computed by `evNext`. -/
theorem layer_event {z : List Bool} {its : List Item} {l : Item} {r : List Bool × List Item × Item}
    (hz : z ≠ []) (h : evNext z its l = some r) {L0 L1 : Tape}
    (hn : ∀ T : Tape, ∃ t, steps t ⟨L0, cons false (cons false T), .D⟩ = some ⟨L1, cons false T, .A⟩) :
    ∃ t, steps t ⟨cons false L0, cons false (enc zd z (encT its l)), .A⟩ =
      some ⟨L1, cons false (enc zd r.1 (encT r.2.1 r.2.2)), .A⟩ := by
  obtain ⟨t1, h1⟩ := event_vis hz h false L0
  obtain ⟨t2, h2⟩ := hn (enc zd r.1 (encT r.2.1 r.2.2))
  exact ⟨_, steps_seq trans h1 h2⟩

