import Cert
import Blank

/-!
# From blank tape to the first end event, and through it

* `arrival_sweeps`: k sweeps that each stop inside the digits (`sweeps k xs = some ys`) take an arrival with wall
  n + 1 to the arrival with wall n + 1 + k; `halts_arrival_iff`: halting is unchanged along the way;
  `not_halts_arrival`: if no sweep ever runs off the digits, the machine never halts.  So it can halt only at an
  end event, a sweep whose carry runs into the last cell.
* `first_arrival`: from blank tape, step 30,225 is the arrival with a wall of 10 pairs, digits `X0`, last cell 1.
* `sweeps_X0` (`Cert.lean`): the next 8,072,508,823 sweeps all stop inside the digits.
* `event`: the sweep after them runs off the digits; for every wall it passes the last cell without halting and
  comes back across the whole wall, turning each pair `10` into `11`, to `post n`.
* `halts_iff_post`: the machine halts from blank tape if and only if it halts from `post 8072508832`, the
  configuration about 1.96·10^20 steps in (`reaches_post`).

The simulation of the end event's fixed part uses `lsteps`, a list simulator with an unknown tape left of its
left list, proved to agree with `steps` for every such tape (`lsteps_sound`).  Written by hand.
-/

namespace H74982

open TM

/-! ## Halting along a run -/

theorem steps_add (a b : Nat) (c : Config) :
    TM.steps trans (a + b) c = (TM.steps trans a c).bind (TM.steps trans b) := by
  induction a generalizing c with
  | zero => simp
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega]
    cases hs : TM.step trans c with
    | none => simp [TM.steps, hs]
    | some d => rw [steps_succ_of_step trans _ hs, steps_succ_of_step trans _ hs, ih]

/-- A run from c to c' does not change whether the machine halts. -/
theorem halts_iff_of_steps {n : Nat} {c c' : Config} (h : TM.steps trans n c = some c') :
    Halts trans c ↔ Halts trans c' := by
  constructor
  · rintro ⟨m, d, hm, hd⟩
    by_cases hmn : n ≤ m
    · refine ⟨m - n, d, ?_, hd⟩
      have := steps_add n (m - n) c
      rw [show n + (m - n) = m by omega, hm, h] at this
      simpa using this.symm
    · have := steps_halt trans hm hd (n - m - 1)
      rw [show m + (n - m - 1 + 1) = n by omega, h] at this
      cases this
  · rintro ⟨m, d, hm, hd⟩
    exact ⟨n + m, d, steps_seq trans h hm, hd⟩

/-! ## Many sweeps -/

theorem wall_true : ∀ (m n : Nat), n < m → wall m (2 * n + 1) = true
  | 0, n, h => absurd h (Nat.not_lt_zero n)
  | _ + 1, 0, _ => rfl
  | m + 1, n + 1, h => by
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 by omega]
    exact wall_true m n (by omega)

theorem wall_false : ∀ (m n : Nat), m ≤ n → wall m (2 * n + 1) = false
  | 0, _, _ => rfl
  | _ + 1, 0, h => absurd h (by omega)
  | m + 1, n + 1, h => by
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 by omega]
    exact wall_false m n (by omega)

theorem arrival_ne (n k : Nat) (xs ys : List Bool) (R R' : Tape) (hk : 0 < k) :
    arrival n xs R ≠ arrival (n + k) ys R' := by
  intro h
  have hl : wall n = wall (n + k) := congrArg TM.Cfg.l h
  have h1 := wall_true (n + k) n (by omega)
  rw [← hl, wall_false n n (Nat.le_refl n)] at h1
  cases h1

/-- k sweeps that stop inside the digits: from the arrival with wall n + 1 to the one with wall n + 1 + k, in at
least k steps. -/
theorem arrival_sweeps (k n : Nat) (xs ys : List Bool) (R : Tape) (h : sweeps k xs = some ys) :
    ∃ s, k ≤ s ∧ steps s (arrival (n + 1) xs R) = some (arrival (n + 1 + k) ys R) := by
  induction k generalizing n xs with
  | zero => simp [sweeps] at h; subst h; exact ⟨0, Nat.le_refl _, rfl⟩
  | succ k ih =>
    simp only [sweeps, Option.bind_eq_some_iff] at h
    obtain ⟨ys1, h1, h2⟩ := h
    obtain ⟨s1, hs1⟩ := sweep n xs ys1 h1 R
    obtain ⟨s2, hk, hs2⟩ := ih (n + 1) ys1 h2
    have hpos : 0 < s1 := by
      rcases Nat.eq_zero_or_pos s1 with e | e
      · subst e
        simp only [steps_zero, Option.some.injEq] at hs1
        exact absurd hs1 (arrival_ne (n + 1) 1 xs ys1 R R (by omega))
      · exact e
    refine ⟨s1 + s2, by omega, ?_⟩
    have := steps_seq trans hs1 hs2
    rwa [show n + 1 + 1 + k = n + 1 + (k + 1) by omega] at this

theorem halts_arrival_iff (k n : Nat) (xs ys : List Bool) (R : Tape) (h : sweeps k xs = some ys) :
    Halts trans (arrival (n + 1) xs R) ↔ Halts trans (arrival (n + 1 + k) ys R) := by
  obtain ⟨s, -, hs⟩ := arrival_sweeps k n xs ys R h
  exact halts_iff_of_steps hs

/-- If no sweep ever runs off the end of the digits, the machine never halts: it can halt only at an end event. -/
theorem not_halts_arrival (n : Nat) (xs : List Bool) (R : Tape) (h : ∀ k, (sweeps k xs).isSome) :
    ¬ Halts trans (arrival (n + 1) xs R) := by
  apply not_halts_of_forall
  apply forall_of_unbounded trans (fun s => ∃ c, steps s (arrival (n + 1) xs R) = some c)
  · intro m
    obtain ⟨ys, hy⟩ := Option.isSome_iff_exists.mp (h m)
    obtain ⟨s, hs, e⟩ := arrival_sweeps m n xs ys R hy
    exact ⟨s, hs, _, e⟩
  · intro m hm
    exact hm

/-! ## From blank tape to the first arrival -/

def cellsL : List Bool → List Bool
  | [] => []
  | x :: xs => x :: true :: cellsL xs

theorem cells_app (xs t : List Bool) (s : Tape) : cells xs (app t s) = app (cellsL xs ++ t) s := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [cells, cellsL, ih]

theorem app_flatten (n : Nat) (w : List Bool) (s : Tape) :
    app (List.replicate n w).flatten s = rep n w s := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ← app_app, ih]

/-- Step 30,225 from blank tape: A arrives at the counter, with a wall of 10 pairs, digits `X0` and last cell 1. -/
theorem first_arrival : steps 30225 init = some (arrival 10 X0 (cons true blank)) := by
  have h := blank_reaches trans (q := St.A) (n := 30225)
    (c := ⟨(List.replicate 10 [false, true]).flatten, true :: true :: (cellsL X0 ++ [true]), .A⟩) (by decide +kernel)
  show TM.steps trans 30225 (blankCfg St.A) = _
  rw [h]
  simp only [FCfg.toCfg, arrival, app_flatten, app_cons]
  rfl

/-! ## The end event -/

/-- The carry from state q running off the end of xs: the state it ends in and the pending pairs it leaves
(`none` if it stops inside xs). -/
def offPairs : Q → List Bool → List (Bool × Bool) → Option (Q × List (Bool × Bool))
  | q, [], acc => some (q, acc)
  | .a, false :: _, _ => none
  | .a, true :: ds, acc => offPairs .b ds ((false, true) :: acc)
  | .b, false :: ds, acc => offPairs .a ds ((true, true) :: acc)
  | .b, true :: ds, acc => offPairs .c ds ((true, false) :: acc)
  | .c, false :: ds, acc => offPairs .c ds ((true, false) :: acc)
  | .c, true :: ds, acc => offPairs .a ds ((true, true) :: acc)

/-- The way right of a carry that runs off the end of the digits. -/
theorem run_off (xs : List Bool) : ∀ (q : Q) (p : Bool × Bool) (ps : List (Bool × Bool)) (q' : Q)
    (acc : List (Bool × Bool)) (W R : Tape), offPairs q xs (p :: ps) = some (q', acc) →
    ∃ s, steps s (fwd q (p :: ps) W (cells xs R)) = some (fwd q' acc W R) := by
  induction xs with
  | nil =>
    intro q p ps q' acc W R h
    simp only [offPairs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨0, rfl⟩
  | cons d ds ih =>
    intro q p ps q' acc W R h
    cases q <;> cases d
    · simp [offPairs] at h
    · obtain ⟨s2, h2⟩ := ih .b (false, true) (p :: ps) q' acc W R h
      exact ⟨_, steps_seq trans (fwd_a1 (cons true (cons false (lt (p :: ps) W))) (cells ds R)) h2⟩
    · obtain ⟨s2, h2⟩ := ih .a (true, true) (p :: ps) q' acc W R h
      exact ⟨_, steps_seq trans (fwd_b0 (lt (p :: ps) W) (cells ds R)) h2⟩
    · obtain ⟨s2, h2⟩ := ih .c (true, false) (p :: ps) q' acc W R h
      exact ⟨_, steps_seq trans (fwd_b1 (lt (p :: ps) W) (cells ds R)) h2⟩
    · obtain ⟨s2, h2⟩ := ih .c (true, false) (p :: ps) q' acc W R h
      exact ⟨_, steps_seq trans (fwd_c0 (cons false (cons true (lt (p :: ps) W))) (cells ds R)) h2⟩
    · obtain ⟨s2, h2⟩ := ih .a (true, true) (p :: ps) q' acc W R h
      exact ⟨_, steps_seq trans (fwd_c1 (lt (p :: ps) W) (cells ds R)) h2⟩

def ltL : List (Bool × Bool) → List Bool
  | [] => []
  | (w, t) :: ps => t :: w :: ltL ps

theorem lt_eq (ps : List (Bool × Bool)) (W : Tape) : lt ps W = app (ltL ps) W := by
  induction ps with
  | nil => rfl
  | cons p ps ih => obtain ⟨w, t⟩ := p; simp [lt, ltL, ih]

/-- One step on lists, with an unknown tape left of the left list (`none` if it halts or would read it). -/
def lstep (l r : List Bool) (q : St) : Option (List Bool × List Bool × St) :=
  match trans q (r.headD false) with
  | none => none
  | some (w, .R, s) => some (w :: l, r.tail, s)
  | some (w, .L, s) =>
    match l with
    | [] => none
    | x :: l' => some (l', x :: w :: r.tail, s)

def lsteps : Nat → List Bool → List Bool → St → Option (List Bool × List Bool × St)
  | 0, l, r, q => some (l, r, q)
  | n + 1, l, r, q =>
    match lstep l r q with
    | none => none
    | some (l', r', q') => lsteps n l' r' q'

theorem lstep_sound (l r : List Bool) (q : St) (l' r' : List Bool) (q' : St) (h : lstep l r q = some (l', r', q'))
    (W : Tape) : TM.step trans ⟨app l W, app r blank, q⟩ = some ⟨app l' W, app r' blank, q'⟩ := by
  unfold lstep at h
  unfold TM.step
  simp only [app_head]
  cases e : trans q (r.headD false) with
  | none => rw [e] at h; cases h
  | some t =>
    obtain ⟨w, d, s⟩ := t
    rw [e] at h
    cases d
    · cases l with
      | nil => cases h
      | cons x l =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        simp [app_tail]
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simp [app_tail]

theorem lsteps_sound (n : Nat) : ∀ (l r : List Bool) (q : St) (l' r' : List Bool) (q' : St),
    lsteps n l r q = some (l', r', q') → ∀ W : Tape,
    TM.steps trans n ⟨app l W, app r blank, q⟩ = some ⟨app l' W, app r' blank, q'⟩ := by
  induction n with
  | zero =>
    intro l r q l' r' q' h W
    simp only [lsteps, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl
  | succ n ih =>
    intro l r q l' r' q' h W
    simp only [lsteps] at h
    cases e : lstep l r q with
    | none => rw [e] at h; cases h
    | some t =>
      obtain ⟨l1, r1, q1⟩ := t
      rw [e] at h
      rw [steps_succ_of_step trans n (lstep_sound l r q l1 r1 q1 e W)]
      exact ih l1 r1 q1 l' r' q' h W

/-- State C runs left across the wall in the end event, turning each `10` into `11`, four steps per pair. -/
theorem wall_left_C (n : Nat) (L R : Tape) :
    steps (4 * n) ⟨rep n [false, true] L, cons true R, .C⟩ = some ⟨L, cons true (rep n [true, true] R), .C⟩ := by
  have c0 : ∀ L R : Tape, steps 4 ⟨app [false, true] L, app [true] R, .C⟩ =
      some ⟨L, app [true] (app [true, true] R), .C⟩ := fun _ _ => rfl
  exact steps_congr trans (by omega) (cross_l trans c0 n L R)

/-- The pending pairs of the carry that runs off the end of `Y0`. -/
def acc0 : List (Bool × Bool) := ((offPairs .a Y0 [(true, true)]).map Prod.snd).getD []

theorem off_Y0 : offPairs .a Y0 [(true, true)] = some (.b, acc0) := by decide +kernel

/-- The tape right of the head when it is back at the wall after the end event (head on its first cell). -/
def R1 : List Bool := bits "0101110101110101010101011111010101010101010101011111110101010101010101010111110101111101010101010101010101111101010101111111111111111111010111010111111101011101011101010101010111111111010111010111110101111111111101010101111"

theorem back_Y0 : lsteps 380 ([false, false] ++ ltL acc0) [true] .D = some ([], true :: R1, .C) := by
  decide +kernel

/-- After the first end event: the wall of n pairs has become n pairs `11`, the head is at its left end. -/
def post (n : Nat) : Config := ⟨blank, cons true (rep n [true, true] (app R1 blank)), .C⟩

/-- The sweep from the arrival with digits `Y0` runs off the end of the digits (in state b, on the last cell),
passes it without halting and comes back across the whole wall, for every wall. -/
theorem event (n : Nat) : ∃ s, steps s (arrival (n + 1) Y0 (cons true blank)) = some (post n) := by
  have h1 := fwd_c1 (wall n) (cells Y0 (cons true blank))
  obtain ⟨s2, h2⟩ := run_off Y0 .a (true, true) [] .b acc0 (wall n) (cons true blank) off_Y0
  have h3 := lsteps_sound 380 _ _ _ _ _ _ back_Y0 (wall n)
  have h3' : steps 380 (fwd .b acc0 (wall n) (cons true blank)) =
      some ⟨wall n, cons true (app R1 blank), .C⟩ := by
    have e1 : app ([false, false] ++ ltL acc0) (wall n) = cons false (cons false (app (ltL acc0) (wall n))) := by
      rw [← app_app]; simp only [app_cons, app_nil]
    have e2 : app [true] blank = cons true blank := by simp only [app_cons, app_nil]
    have e3 : app [] (wall n) = wall n := rfl
    have e4 : app (true :: R1) blank = cons true (app R1 blank) := app_cons _ _ _
    rw [e1, e2, e3, e4] at h3
    simp only [fwd, lt_eq]
    exact h3
  have h4 := wall_left_C n blank (app R1 blank)
  exact ⟨_, steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3' h4))⟩

theorem carry_Y0 : carry .a Y0 = none := by decide +kernel

/-- From blank tape the machine reaches `post 8072508832` (about 1.96·10^20 steps in) without halting. -/
theorem reaches_post : ∃ s, steps s init = some (post 8072508832) := by
  obtain ⟨s1, -, h1⟩ := arrival_sweeps 8072508823 9 X0 Y0 (cons true blank) sweeps_X0
  obtain ⟨s2, h2⟩ := event 8072508832
  exact ⟨_, steps_seq trans first_arrival (steps_seq trans h1 h2)⟩

/-- The machine halts from blank tape if and only if it halts from `post 8072508832`. -/
theorem halts_iff_post : HaltsFromBlank ↔ Halts trans (post 8072508832) := by
  obtain ⟨s, h⟩ := reaches_post
  exact halts_iff_of_steps h

end H74982
