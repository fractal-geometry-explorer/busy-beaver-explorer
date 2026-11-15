import Machine

/-!
# 1RB1RD_1RC1RB_1LD0RA_1RA0LE_1LF0LC_---1LE: the visit rule of a zone, for every zone

At a visit (A on the blank cell right of the tape) the tape ends in a *zone*

    t  (011)^n_k s_k ... (011)^n_1 s_1 (011)^n_0 0  A>          s_j = 11 (bit 0) or 01 (bit 1)

`zoneT n0 lv t` is that tape (left of the head, nearest cell first), `lv` the list of the pairs (bit of s_j, n_j)
from j = 1 up.  `inc lv` is the binary increment of the bits with what it does to the counts: the lowest 0 bit is
set and its count loses 1; a bit that is cleared leaves its count alone if the next bit is cleared too, and gives it
one more if the next bit is the one that is set.  `visit`: whenever `inc lv = some lv'`, the machine goes from the
zone `n0, lv` to the zone `n0 + 2, lv'` (lowest bit 0) or `n0 + 1, lv'` (lowest bit 1), whatever the tape `t`
left of the zone.  Written by hand; the proof follows the head: it walks left through the counters behind the 1
bits (D turns 011 into 100), turns at the 0 bit, and walks back (C turns 100 into 011).
-/

namespace H172044

open TM

/-- `c` reaches `c'`. -/
def Reach (c c' : Config) : Prop := ∃ n, steps n c = some c'

theorem Reach.refl (c : Config) : Reach c c := ⟨0, rfl⟩

theorem Reach.seq {a b c : Config} (h₁ : Reach a b) (h₂ : Reach b c) : Reach a c := by
  obtain ⟨n, hn⟩ := h₁
  obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, steps_seq trans hn hm⟩

theorem Reach.of_steps {n : Nat} {c c' : Config} (h : steps n c = some c') : Reach c c' := ⟨n, h⟩

/-- The word 011, nearest cell first as seen from its right. -/
abbrev W : List Bool := [true, true, false]
/-- The same repeat read one cell later: `1 (101)^n = (110)^n 1`. -/
abbrev U : List Bool := [true, false, true]
/-- The word 100 that D leaves on its way left (on the right of the head, in reading order). -/
abbrev X : List Bool := [true, false, false]

/-- The counters above the last one: (bit, count) pairs, lowest first, in front of the tape `t`. -/
def lvT : List (Bool × Nat) → Tape → Tape
  | [], t => t
  | (b, n) :: r, t => cons true (cons (!b) (rep n W (lvT r t)))

/-- The zone: the 0 at the right end, the last counter, the other counters, the rest of the tape. -/
def zoneT (n0 : Nat) (lv : List (Bool × Nat)) (t : Tape) : Tape := cons false (rep n0 W (lvT lv t))

/-- The bit of the first level (`false` for no level). -/
def hd : List (Bool × Nat) → Bool
  | [] => false
  | (b, _) :: _ => b

/-- The binary increment of the bits, with its effect on the counts; `none` if the bits overflow or a count
that must give a unit is 0. -/
def inc : List (Bool × Nat) → Option (List (Bool × Nat))
  | [] => none
  | (false, n) :: r => if n = 0 then none else some ((true, n - 1) :: r)
  | (true, n) :: r => if n = 0 then none else (inc r).map (fun r' => (false, if hd r then n else n + 1) :: r')

/-! ## Tape identities -/

theorem rot (n : Nat) (s : Tape) : rep n W (cons true s) = cons true (rep n U s) :=
  (rep_rotate n [true] U W rfl s).symm

/-! ## The pieces -/

/-- From the visit to D on the last cell of the last counter. -/
theorem p_start (T : Tape) :
    steps 6 ⟨cons false (cons true T), blank, .A⟩ =
      some ⟨T, cons true (cons true (cons false (cons false (cons true blank)))), .D⟩ := rfl

/-- D walks left through a counter. -/
theorem p_left (n : Nat) (L R : Tape) :
    steps (n * 3) ⟨rep n U L, cons true R, .D⟩ = some ⟨L, cons true (rep n X R), .D⟩ :=
  cross_l (u := [true]) trans (fun _ _ => rfl) n L R

/-- D passes a 1 bit (the word 01) and the last 011 of the counter behind it. -/
theorem p_pass (T R : Tape) :
    steps 5 ⟨cons false (cons true (cons true (cons false (cons true T)))), cons true R, .D⟩ =
      some ⟨T, cons true (cons true (cons false (cons true (cons true (cons false R))))), .D⟩ := rfl

/-- D turns at a 0 bit (the word 11): the counter behind it loses its last 011, the bit becomes 01, and a new 011
is left for the counter in front. -/
theorem p_turn (T R : Tape) :
    steps 5 ⟨cons true (cons true T), cons true R, .D⟩ = some ⟨app W T, R, .C⟩ := rfl

/-- C walks right through what D left of a counter. -/
theorem p_right (n : Nat) (L R : Tape) :
    steps (n * 3) ⟨L, rep n X R, .C⟩ = some ⟨rep n W L, R, .C⟩ :=
  cross_r (u := []) trans (fun _ _ => rfl) n L R

/-- C rebuilds the last 011 of a counter and the bit after it, now 11. -/
theorem p_sep (L R : Tape) :
    steps 5 ⟨L, cons true (cons false (cons true (cons true (cons false R)))), .C⟩ =
      some ⟨cons true (cons true (app W L)), R, .C⟩ := rfl

/-- C at the right end: one more 011, the 0, and the next visit. -/
theorem p_end (L : Tape) :
    steps 4 ⟨L, cons true (cons false (cons false (cons true blank))), .C⟩ =
      some ⟨cons false (app W L), blank, .A⟩ := rfl

/-! ## The carry -/

/-- What the counters from the carry's level up look like when C comes back to them. -/
def ext (lv lv' : List (Bool × Nat)) (t : Tape) : Tape :=
  if hd lv then lvT lv' t else app W (lvT lv' t)

/-- D on the second cell of the bit of the first level of `lv`, everything below already crossed (it is `R`, and C
rebuilds it by `F`). -/
theorem carry (t : Tape) : ∀ (lv lv' : List (Bool × Nat)) (b : Bool) (n : Nat) (r : List (Bool × Nat))
    (R : Tape) (F : Tape → Tape), lv = (b, n) :: r → inc lv = some lv' →
    (∀ L, Reach ⟨L, R, .C⟩ ⟨F L, blank, .A⟩) →
    Reach ⟨cons (!b) (rep n W (lvT r t)), cons true R, .D⟩ ⟨F (ext lv lv' t), blank, .A⟩ := by
  intro lv
  induction lv with
  | nil => intro lv' b n r R F h; cases h
  | cons p r ih =>
    intro lv' b n r0 R F h hinc hF
    cases h
    cases b with
    | false =>
      cases n with
      | zero => simp [inc] at hinc
      | succ m =>
        simp only [inc] at hinc
        have e : lv' = (true, m) :: r := by simpa using hinc.symm
        subst e
        exact (Reach.of_steps (p_turn (cons true (cons false (rep m W (lvT r t)))) R)).seq (hF _)
    | true =>
      cases n with
      | zero => simp [inc] at hinc
      | succ m =>
        cases r with
        | nil => simp [inc] at hinc
        | cons q r2 =>
          obtain ⟨b2, n2⟩ := q
          -- the levels above
          have hr : ∃ r', inc ((b2, n2) :: r2) = some r' ∧
              lv' = (false, if b2 then m + 1 else m + 2) :: r' := by
            rw [inc] at hinc
            simp only [Nat.succ_ne_zero, ite_false] at hinc
            cases hi : inc ((b2, n2) :: r2) with
            | none => rw [hi] at hinc; simp at hinc
            | some r' =>
              rw [hi] at hinc
              refine ⟨r', rfl, ?_⟩
              cases b2 <;> simpa [hd] using hinc.symm
          obtain ⟨r', hr', e⟩ := hr
          subst e
          -- walk left: the bit 01, the last 011, the rest of the counter
          let Y : Tape := cons (!b2) (rep n2 W (lvT r2 t))
          let R2 : Tape := cons true (cons false (cons true (cons true (cons false R))))
          have e1 : (⟨cons (!true) (rep (m + 1) W (lvT ((b2, n2) :: r2) t)), cons true R, .D⟩ : Config) =
              ⟨cons false (cons true (cons true (cons false (cons true (rep m U Y))))), cons true R, .D⟩ := by
            show (⟨cons false (rep (m + 1) W (cons true Y)), cons true R, .D⟩ : Config) = _
            rw [rot]; rfl
          rw [e1]
          have h1 := Reach.of_steps (p_pass (rep m U Y) R)
          have h2 := Reach.of_steps (p_left m Y R2)
          -- back
          have hF' : ∀ L, Reach ⟨L, rep m X R2, .C⟩ ⟨F (cons true (cons true (rep (m + 1) W L))), blank, .A⟩ := by
            intro L
            exact (Reach.of_steps (p_right m L R2)).seq ((Reach.of_steps (p_sep (rep m W L) R)).seq (hF _))
          have h3 := ih r' b2 n2 r2 (rep m X R2) (fun L => F (cons true (cons true (rep (m + 1) W L)))) rfl hr' hF'
          have e2 : F (cons true (cons true (rep (m + 1) W (ext ((b2, n2) :: r2) r' t)))) =
              F (ext ((true, m + 1) :: (b2, n2) :: r2) ((false, if b2 then m + 1 else m + 2) :: r') t) := by
            cases b2 with
            | false =>
              show F (cons true (cons true (rep (m + 1) W (app W (lvT r' t))))) = _
              rw [rep_app_comm]; rfl
            | true => rfl
          rw [← e2]
          exact Reach.seq h1 (Reach.seq h2 h3)

/-- **The visit rule.**  One visit of a zone is the binary increment of its bits. -/
theorem visit (n0 : Nat) (lv lv' : List (Bool × Nat)) (t : Tape) (h : inc lv = some lv') :
    Reach ⟨zoneT n0 lv t, blank, .A⟩
      ⟨zoneT (n0 + (if hd lv then 1 else 2)) lv' t, blank, .A⟩ := by
  cases lv with
  | nil => simp [inc] at h
  | cons p r =>
    obtain ⟨b, n⟩ := p
    let Y : Tape := cons (!b) (rep n W (lvT r t))
    let R1 : Tape := cons true (cons false (cons false (cons true blank)))
    have e1 : (⟨zoneT n0 ((b, n) :: r) t, blank, .A⟩ : Config) = ⟨cons false (cons true (rep n0 U Y)), blank, .A⟩ := by
      show (⟨cons false (rep n0 W (cons true Y)), blank, .A⟩ : Config) = _
      rw [rot]
    rw [e1]
    have h1 := Reach.of_steps (p_start (rep n0 U Y))
    have h2 := Reach.of_steps (p_left n0 Y R1)
    have hF : ∀ L, Reach ⟨L, rep n0 X R1, .C⟩ ⟨cons false (rep (n0 + 1) W L), blank, .A⟩ := by
      intro L
      exact (Reach.of_steps (p_right n0 L R1)).seq (Reach.of_steps (p_end (rep n0 W L)))
    have h3 := carry t ((b, n) :: r) lv' b n r (rep n0 X R1) (fun L => cons false (rep (n0 + 1) W L)) rfl h hF
    have e2 : cons false (rep (n0 + 1) W (ext ((b, n) :: r) lv' t)) =
        zoneT (n0 + (if hd ((b, n) :: r) then 1 else 2)) lv' t := by
      cases b with
      | false =>
        show cons false (rep (n0 + 1) W (app W (lvT lv' t))) = _
        rw [rep_app_comm]; rfl
      | true => rfl
    rw [← e2]
    exact Reach.seq h1 (Reach.seq h2 h3)

end H172044
