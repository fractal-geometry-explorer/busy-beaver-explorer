
/-! ## Blocks, the two sweep configurations, and lists of blocks -/

/-- `Sl n X`: the block S_n = 1 (01)^(n+1) written on the left tape, nearest cell first, in front of `X`. -/
def Sl (n : Nat) (X : Tape) : Tape := rep (n + 1) [true, false] (cons true X)

/-- `Dr n R`: the block D_n = 1 (11)^n 00 on the right tape in front of `R`. -/
def Dr (n : Nat) (R : Tape) : Tape := cons true (rep n [true, true] (cons false (cons false R)))

/-- The blocks of a list, left to right, on the left tape: `SL [m1, m2] X` reads `X S_m1 S_m2`. -/
def SL : List Nat → Tape → Tape
  | [], X => X
  | n :: ns, X => SL ns (Sl n X)

/-- The blocks of a list, left to right, as D-blocks on the right tape. -/
def DR : List Nat → Tape → Tape
  | [], R => R
  | n :: ns, R => Dr n (DR ns R)

/-- The left sweep:  `L <C 1 R`. -/
def CL (L R : Tape) : Config := ⟨L, cons true R, .C⟩

/-- The right sweep:  `L 1 B> 1 0 0 R`. -/
def CR (L R : Tape) : Config := ⟨cons true L, cons true (cons false (cons false R)), .B⟩

/-- `c` reaches `c'`. -/
def Reach (c c' : Config) : Prop := ∃ t, steps t c = some c'

theorem Reach.trans {a b c : Config} (h1 : Reach a b) (h2 : Reach b c) : Reach a c := by
  obtain ⟨t1, h1⟩ := h1
  obtain ⟨t2, h2⟩ := h2
  exact ⟨t1 + t2, TM.steps_seq _ h1 h2⟩

theorem reach_of {c c' : Config} {t : Nat} (h : steps t c = some c') : Reach c c' := ⟨t, h⟩

theorem sl_eq (n : Nat) (X : Tape) : rep n [true, false] (cons true (cons false X)) = rep (n + 1) [true, false] X :=
  rep_app_comm n [true, false] X

theorem SL_append (ms : List Nat) (x : Nat) : ∀ X, SL (ms ++ [x]) X = Sl x (SL ms X) := by
  induction ms with
  | nil => intro X; rfl
  | cons m ms ih => intro X; exact ih (Sl m X)

theorem DR_append (ms : List Nat) (x : Nat) (R : Tape) : DR (ms ++ [x]) R = DR ms (Dr x R) := by
  induction ms with
  | nil => rfl
  | cons m ms ih => show Dr m (DR (ms ++ [x]) R) = Dr m (DR ms (Dr x R)); rw [ih]

theorem DR_zeros (c : Nat) (R : Tape) : rep c [true, false, false] R = DR (List.replicate c 0) R := by
  induction c with
  | zero => rfl
  | succ c ih => show app [true, false, false] (rep c [true, false, false] R) = Dr 0 (DR (List.replicate c 0) R); rw [ih]; rfl

theorem sweep_left' (n : Nat) (L R : Tape) : Reach (CL (Sl n L) R) (CL L (Dr n R)) := ⟨_, sweep_left n L R⟩

theorem sweep_right' (n : Nat) (L R : Tape) : Reach (CR L (Dr n R)) (CR (Sl n L) R) := by
  have h := sweep_right n L R
  rw [sl_eq] at h
  exact ⟨_, h⟩

theorem wall_turn' (k n : Nat) (L R : Tape) : Reach (CL (rep (k + 3) [true] L) (Dr n R)) (CR (Sl n (rep k [true] L)) R) := by
  have h := wall_turn k n L R
  rw [sl_eq] at h
  exact ⟨_, h⟩

/-- The left sweep crosses any list of blocks. -/
theorem sweep_left_all (ms : List Nat) : ∀ L R, Reach (CL (SL ms L) R) (CL L (DR ms R)) := by
  induction ms with
  | nil => intro L R; exact ⟨0, rfl⟩
  | cons n ns ih => intro L R; exact (ih (Sl n L) R).trans (sweep_left' n L (DR ns R))

/-- The right sweep crosses any list of blocks. -/
theorem sweep_right_all (ms : List Nat) : ∀ L R, Reach (CR L (DR ms R)) (CR (SL ms L) R) := by
  induction ms with
  | nil => intro L R; exact ⟨0, rfl⟩
  | cons n ns ih => intro L R; exact (sweep_right' n L (DR ns R)).trans (ih (Sl n L) R)

/-- At the wall the sweep turns, and the right sweep then crosses the rest. -/
theorem turn_all (a : Nat) (L0 : Tape) (ms : List Nat) (x : Nat) (R : Tape) :
    Reach (CL (rep (a + 3) [true] L0) (DR ms (Dr x R))) (CR (Sl x (SL ms (rep a [true] L0))) R) := by
  cases ms with
  | nil => exact wall_turn' a x L0 R
  | cons m ms =>
    have h2 := sweep_right_all (ms ++ [x]) (Sl m (rep a [true] L0)) R
    rw [DR_append, SL_append] at h2
    exact (wall_turn' a m L0 (DR ms (Dr x R))).trans h2

/-! ## Regime I: the gadget 101100 / 101101 at the right end -/

/-- `X 101100 (110)^(c+2)`, the left tape before a long visit (nearest cell first). -/
def GI (c : Nat) (X : Tape) : Tape :=
  rep (c + 2) [false, true, true] (cons false (cons false (cons true (cons true (cons false (cons true X))))))

/-- `X 101101 1 (101)^c 10110` (which is `X 101101 (110)^(c+2)`), the left tape before a short visit. -/
def HI (c : Nat) (X : Tape) : Tape :=
  cons false (cons true (cons true (cons false (cons true (rep c [true, false, true]
    (cons true (cons true (cons false (cons true (cons true (cons false (cons true X))))))))))))

theorem ones_rot (k : Nat) (Z : Tape) : cons true (rep k [true, true] Z) = rep k [true, true] (cons true Z) :=
  rep_rotate k [true] [true, true] [true, true] rfl Z

theorem dI_eq (n : Nat) (Y : Tape) :
    cons true (cons true (rep (n + 1) [true, true] (cons true (cons true (cons true (cons false (cons false Y)))))))
    = Dr (n + 3) Y := by
  show cons true (cons true (rep (n + 1) [true, true] (app [true, true] (cons true (cons false (cons false Y))))))
    = cons true (rep (n + 3) [true, true] (cons false (cons false Y)))
  rw [rep_app_comm, ones_rot,
    show cons true (cons true (cons false (cons false Y))) = app [true, true] (cons false (cons false Y)) from rfl,
    rep_app_comm]

/-- A long visit in regime I, for every wall `1^(a+3)`, every list `ms` of blocks behind it and every last block:
`L0 1^(a+3) S_ms S_n 101100 (110)^(c+2) D>` reaches `L0 1^a S_ms S_(n+3) 101101 (110)^(c+2) D>`. -/
theorem round_I (a c n : Nat) (ms : List Nat) (L0 : Tape) :
    Reach ⟨GI c (Sl n (SL ms (rep (a + 3) [true] L0))), blank, .D⟩
      ⟨HI c (Sl (n + 3) (SL ms (rep a [true] L0))), blank, .D⟩ := by
  have h1 := endI_left c n (SL ms (rep (a + 3) [true] L0))
  rw [dI_eq] at h1
  exact (((reach_of h1).trans (sweep_left_all ms _ _)).trans (turn_all a L0 ms (n + 3) _)).trans
    (reach_of (endI_right c _))

theorem hI_eq (c : Nat) (L : Tape) : HI c (cons true L) =
    rep (c + 2) [false, true, true] (cons true (cons false (cons true (cons true (cons false (cons true (cons true L))))))) := by
  show cons false (cons true (cons true (app [false, true] (rep c [true, false, true] _)))) = _
  rw [rep_rotate c [false, true] [true, false, true] [false, true, true] rfl]
  show app [false, true, true] (rep c [false, true, true] (app [false, true, true]
    (cons true (cons false (cons true (cons true (cons false (cons true (cons true L))))))))) = _
  rw [rep_app_comm]
  rfl

theorem gI_eq (c : Nat) (L : Tape) :
    cons false (cons true (cons true (cons false (cons true (rep (c + 1) [true, false, true] (cons true (cons false
      (cons false (cons true (cons true (cons false (cons true (cons true L)))))))))))))
    = GI (c + 1) (cons true L) := by
  show cons false (cons true (cons true (app [false, true] (rep (c + 1) [true, false, true] _)))) = _
  rw [rep_rotate (c + 1) [false, true] [true, false, true] [false, true, true] rfl]
  show app [false, true, true] (rep (c + 1) [false, true, true] (app [false, true, true]
    (cons false (cons false (cons true (cons true (cons false (cons true (cons true L))))))))) = _
  rw [rep_app_comm]
  rfl

/-- The short visit in regime I: `X 101101 (110)^(c+2) D>` reaches `X 101100 (110)^(c+3) D>` (X ends in 1). -/
theorem short_I (c : Nat) (L : Tape) :
    Reach ⟨HI c (cons true L), blank, .D⟩ ⟨GI (c + 1) (cons true L), blank, .D⟩ := by
  have h := shortI (c + 1) L
  rw [gI_eq] at h
  rw [hI_eq]
  exact ⟨_, h⟩

/-- A whole round in regime I (a long visit and a short one): the wall loses three 1s, the last block grows by
three and the gadget's tail by one copy of 110; every block in between is unchanged. -/
theorem roundpair_I (a c n : Nat) (ms : List Nat) (L0 : Tape) :
    Reach ⟨GI c (Sl n (SL ms (rep (a + 3) [true] L0))), blank, .D⟩
      ⟨GI (c + 1) (Sl (n + 3) (SL ms (rep a [true] L0))), blank, .D⟩ := by
  have h := short_I c (cons false (rep (n + 3) [true, false] (cons true (SL ms (rep a [true] L0)))))
  exact (round_I a c n ms L0).trans h

/-- `k` rounds in a row in regime I. -/
theorem rounds_I (n0 : Nat) (ms : List Nat) (L0 : Tape) : ∀ k a c,
    Reach ⟨GI c (Sl n0 (SL ms (rep (a + 3 * k) [true] L0))), blank, .D⟩
      ⟨GI (c + k) (Sl (n0 + 3 * k) (SL ms (rep a [true] L0))), blank, .D⟩ := by
  intro k
  induction k generalizing n0 with
  | zero => intro a c; exact ⟨0, rfl⟩
  | succ k ih =>
    intro a c
    have h1 := roundpair_I (a + 3 * k) c n0 ms L0
    have h2 := ih (n0 + 3) a (c + 1)
    rw [show a + 3 * k + 3 = a + 3 * (k + 1) by omega] at h1
    rw [show c + 1 + k = c + (k + 1) by omega, show n0 + 3 + 3 * k = n0 + 3 * (k + 1) by omega] at h2
    exact h1.trans h2

/-! ## Regime II: no gadget, every visit is long -/

/-- A visit in regime II: `L0 1^(a+3) S_ms S_n (011)^c 0 D>` reaches `L0 1^a S_ms S_(n+1) S_0^c 10110 D>`. -/
theorem round_II (a c n : Nat) (ms : List Nat) (L0 : Tape) :
    Reach ⟨cons false (rep c [true, true, false] (Sl n (SL ms (rep (a + 3) [true] L0)))), blank, .D⟩
      ⟨cons false (cons true (cons true (cons false (cons true
        (SL (List.replicate c 0) (Sl (n + 1) (SL ms (rep a [true] L0)))))))), blank, .D⟩ := by
  have h1 := endII_left c n (SL ms (rep (a + 3) [true] L0))
  rw [DR_zeros] at h1
  exact ((((reach_of h1).trans (sweep_left_all ms _ _)).trans
    (turn_all a L0 ms (n + 1) _)).trans (sweep_right_all _ _ _)).trans (reach_of (endII_right _))

/-! ## A wall of exactly three 1s -/

/-- `1 (01)^n` on the left tape: the block S_n with one `01` less. -/
def Sm (n : Nat) (X : Tape) : Tape := rep n [true, false] (cons true X)

theorem wall3_turn' (n : Nat) (L R : Tape) :
    Reach (CL (cons true (cons true (cons false L))) (Dr n R)) (CR (Sm n (cons false (cons false L))) R) :=
  reach_of (wall3_turn n L R)

/-- A long visit in regime I at a wall of three 1s, for a chamber `m :: ms` in front of the last block:
`L0 0 111 (01)^(m+1) S_ms S_n 101100 (110)^(c+2) D>` reaches `L0 00 1 (01)^m S_ms S_(n+3) 101101 (110)^(c+2) D>`. -/
theorem round_I3 (c n m : Nat) (ms : List Nat) (L0 : Tape) :
    Reach ⟨GI c (Sl n (SL ms (Sl m (cons true (cons true (cons false L0)))))), blank, .D⟩
      ⟨HI c (Sl (n + 3) (SL ms (Sm m (cons false (cons false L0))))), blank, .D⟩ := by
  have h1 := endI_left c n (SL ms (Sl m (cons true (cons true (cons false L0)))))
  rw [dI_eq] at h1
  have h3 := sweep_right_all (ms ++ [n + 3]) (Sm m (cons false (cons false L0))) (cons true (cons false (cons true
    (cons false (cons true (rep c [false, false, true] (cons false (cons false (cons true blank)))))))))
  rw [DR_append, SL_append] at h3
  exact ((((reach_of h1).trans (sweep_left_all (m :: ms) _ _)).trans (wall3_turn' m L0 _)).trans h3).trans
    (reach_of (endI_right c _))

/-- A visit in regime II at a wall of three 1s, for a chamber `m :: ms` in front of the last block. -/
theorem round_II3 (c n m : Nat) (ms : List Nat) (L0 : Tape) :
    Reach ⟨cons false (rep c [true, true, false] (Sl n (SL ms (Sl m (cons true (cons true (cons false L0))))))), blank, .D⟩
      ⟨cons false (cons true (cons true (cons false (cons true
        (SL (List.replicate c 0) (Sl (n + 1) (SL ms (Sm m (cons false (cons false L0)))))))))), blank, .D⟩ := by
  have h1 := endII_left c n (SL ms (Sl m (cons true (cons true (cons false L0)))))
  rw [DR_zeros] at h1
  have h3 := sweep_right_all (ms ++ [n + 1]) (Sm m (cons false (cons false L0))) (DR (List.replicate c 0) (cons true blank))
  rw [DR_append, SL_append] at h3
  exact (((((reach_of h1).trans (sweep_left_all (m :: ms) _ _)).trans (wall3_turn' m L0 _)).trans h3).trans
    (sweep_right_all _ _ _)).trans (reach_of (endII_right _))
