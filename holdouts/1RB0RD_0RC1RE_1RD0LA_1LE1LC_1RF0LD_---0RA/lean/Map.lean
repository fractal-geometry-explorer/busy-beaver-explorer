import Rules

/-!
# 1RB0RD_0RC1RE_1RD0LA_1LE1LC_1RF0LD_---0RA: the run from blank tape is the orbit of a map on two numbers

A *phase start* is the configuration

    P m n  =  0^inf (1011)^m 1^n (10)^3 A> 1 0^inf

(`m` copies of `1011`, then a block of `n` ones, then `101010`, the head in state A on a 1 at the right end).
Blank tape reaches `P 14 5` (`init_P`).  From `P m n` with `n ≥ 3`, writing `n = 3k + 3 + r` (`r < 3`), the machine
reaches the next phase start `next m n` (`next_reach`):

    r = 0 :  m ≥ 1 : P (m-1) (8k+19)        m = 0 : P (2k+4) 5
    r = 1 :  m ≥ 2 : P (m-2) (8k+29)        m = 1 : halts         m = 0 : P 0 (8k+18)
    r = 2 :  m ≥ 2 : P (m-2) (8k+35)        m = 1 : P (2k+8) 5    m = 0 : P 0 (8k+18)

and from `P 1 (3k+4)` it halts (`halts_P1`).  So the machine halts from blank tape if and only if the orbit of
`(14, 5)` under `next` reaches a point `(1, n)` with `n % 3 = 1` (`halts_iff`).

Inside a phase the head bounces at the right end: each round eats three ones of the block and adds four `10`s
(`Rules.cycle`, iterated in `loop`), so `n = 3k + 3 + r` ones become `r` ones and `4k + 7` copies of `10`.  Then one
sweep turns every `10` into `11` and the block is rebuilt (`b1`, `b2`, `b3`, `z1`, `z2`, `entry`), using up one or two
`1011`s; with no `1011` left (`reset`, `r1a`, `r1b`) the `10`s are paired into a new stack of `1011`s.
-/

namespace H166535

open TM

/-- The word `1011`, as the left stream reads it (nearest the head first). -/
abbrev W : List Bool := [true, true, false, true]

/-- The phase start `0^inf (1011)^m 1^n (10)^3 A> 1 0^inf`. -/
def P (m n : Nat) : Config := ⟨rep 3 [false, true] (rep n [true] (rep m W blank)), cons true blank, .A⟩

/-! ## Tape identities -/

theorem rep_succ' (n : Nat) (w : List Bool) (s : Tape) : rep (n + 1) w s = rep n w (app w s) :=
  (rep_app_comm n w s).symm

theorem ones_tt (q : Nat) (s : Tape) : rep q [true, true] s = rep (2 * q) [true] s := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [show 2 * (q + 1) = 2 * q + 1 + 1 by omega, rep_succ, ih]; rfl

theorem ft_double (q : Nat) (s : Tape) : rep (2 * q) [false, true] s = rep q [false, true, false, true] s := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [show 2 * (q + 1) = 2 * q + 1 + 1 by omega, rep_succ, rep_succ, ih]; rfl

theorem ones_add (a b : Nat) (s : Tape) : rep a [true] (rep b [true] s) = rep (a + b) [true] s :=
  (rep_add a b [true] s).symm

theorem cons_ones (n : Nat) (s : Tape) : cons true (rep n [true] s) = rep (n + 1) [true] s := rfl

/-! ## Reaching -/

/-- `c'` is reached from `c` in `t ≥ 1` steps. -/
def Reach (c c' : Config) : Prop := ∃ t, 0 < t ∧ steps t c = some c'

theorem reach_of {t : Nat} {c c' : Config} (h : steps t c = some c') (ht : 0 < t) : Reach c c' := ⟨t, ht, h⟩

/-- The inner bouncer, `k` rounds: `L 1^(3k+r) (10)^(p+1) A> 1`  reaches  `L 1^r (10)^(p+1+4k) A> 1`. -/
theorem loop (r : Nat) (L : Tape) : ∀ k p : Nat, ∃ t,
    steps t ⟨rep (p + 1) [false, true] (rep (3 * k + r) [true] L), cons true blank, .A⟩ =
      some ⟨rep (p + 1 + 4 * k) [false, true] (rep r [true] L), cons true blank, .A⟩ := by
  intro k
  induction k with
  | zero => intro p; exact ⟨0, by simp⟩
  | succ k ih =>
    intro p
    have h : steps (6 * p + 37) ⟨rep (p + 1) [false, true] (rep (3 * k + r + 3) [true] L), cons true blank, .A⟩ =
        some ⟨rep (p + 4 + 1) [false, true] (rep (3 * k + r) [true] L), cons true blank, .A⟩ := by
      rw [cycle]
      show some (⟨app [false, true] (app [false, true] (rep (p + 1) [false, true]
        (app [false, true] (app [false, true] (rep (3 * k + r) [true] L))))), _, _⟩ : Config) = _
      rw [rep_app_comm, rep_app_comm]; rfl
    obtain ⟨t, ht⟩ := ih (p + 4)
    refine ⟨6 * p + 37 + t, ?_⟩
    rw [show 3 * (k + 1) + r = 3 * k + r + 3 by omega, show p + 1 + 4 * (k + 1) = p + 4 + 1 + 4 * k by omega]
    exact steps_seq trans h ht

/-- A phase start runs its inner bouncer down to `r` ones and `4k + 7` copies of `10`. -/
theorem phase_loop (m k r : Nat) : ∃ t,
    steps t (P m (3 * k + 3 + r)) =
      some ⟨rep (4 * k + 7) [false, true] (rep r [true] (rep m W blank)), cons true blank, .A⟩ := by
  obtain ⟨t, h⟩ := loop r (rep m W blank) (k + 1) 2
  rw [show 3 * (k + 1) + r = 3 * k + 3 + r by omega, show 2 + 1 + 4 * (k + 1) = 4 * k + 7 by omega] at h
  exact ⟨t, h⟩

/-- `(10)^(4k+7)` re-bracketed as `(1010)^(2k+3) 10`. -/
theorem ft_split (k : Nat) (s : Tape) :
    rep (4 * k + 7) [false, true] s = rep (2 * k + 3) [false, true, false, true] (cons false (cons true s)) := by
  rw [show 4 * k + 7 = 2 * (2 * k + 3) + 1 by omega, rep_add, ft_double]; rfl

/-- The end of a conversion sweep, `L 0 1 D> 1 0 1 0 1` with `L = 1^a (11)^q 1^b (1011)^m`, is a phase start. -/
theorem finish (q a b m : Nat) :
    steps 42 ⟨cons true (cons false (rep a [true] (rep q [true, true] (rep b [true] (rep m W blank))))),
      cons true (cons false (cons true (cons false (cons true blank)))), .D⟩ = some (P m (2 + a + 2 * q + b)) := by
  rw [entry]; unfold P
  rw [ones_tt, ones_add, ones_add, show 2 + a + 2 * q + b = a + 2 * q + b + 1 + 1 by omega]; rfl

/-- `reset`, ending at a phase start. -/
theorem reset_P (k : Nat) :
    steps (16 * k + 109) ⟨rep (2 * k + 3) [false, true, false, true] (cons false (cons true blank)), cons true blank, .A⟩ =
      some (P (2 * k + 4) 5) := by
  rw [reset]
  show some (⟨app [false, true] (app [false, true] (app [false, true] (app [true, true, true, true]
    (rep (2 * k + 3) [true, true, true, false] (app [true] (app W blank)))))), _, _⟩ : Config) = _
  rw [← rep_rotate (2 * k + 3) [true] W [true, true, true, false] rfl, rep_app_comm]; rfl

/-! ## The phases -/

theorem phase_r0 (m k : Nat) : Reach (P (m + 1) (3 * k + 3)) (P m (8 * k + 19)) := by
  obtain ⟨t, h⟩ := phase_loop (m + 1) k 0
  have h3 := finish (4 * k + 7) 0 3 m
  rw [show 2 + 0 + 2 * (4 * k + 7) + 3 = 8 * k + 19 by omega] at h3
  exact reach_of (steps_seq trans h (steps_seq trans (b1 k m) h3)) (by omega)

theorem phase_r0_zero (k : Nat) : Reach (P 0 (3 * k + 3)) (P (2 * k + 4) 5) := by
  obtain ⟨t, h⟩ := phase_loop 0 k 0
  rw [ft_split] at h
  exact reach_of (steps_seq trans h (reset_P k)) (by omega)

theorem phase_r1 (m k : Nat) : Reach (P (m + 2) (3 * k + 4)) (P m (8 * k + 29)) := by
  obtain ⟨t, h⟩ := phase_loop (m + 2) k 1
  have h3 := finish (4 * k + 7) 4 9 m
  rw [show 2 + 4 + 2 * (4 * k + 7) + 9 = 8 * k + 29 by omega] at h3
  exact reach_of (steps_seq trans h (steps_seq trans (b2 k m) h3)) (by omega)

theorem phase_r1_zero (k : Nat) : Reach (P 0 (3 * k + 4)) (P 0 (8 * k + 18)) := by
  obtain ⟨t, h⟩ := phase_loop 0 k 1
  have h3 := finish (4 * k + 7) 0 2 0
  rw [show 2 + 0 + 2 * (4 * k + 7) + 2 = 8 * k + 18 by omega] at h3
  exact reach_of (steps_seq trans h (steps_seq trans (z1 k) h3)) (by omega)

theorem phase_r2 (m k : Nat) : Reach (P (m + 2) (3 * k + 5)) (P m (8 * k + 35)) := by
  obtain ⟨t, h⟩ := phase_loop (m + 2) k 2
  have h3 := finish (4 * k + 7) 8 11 m
  rw [show 2 + 8 + 2 * (4 * k + 7) + 11 = 8 * k + 35 by omega] at h3
  exact reach_of (steps_seq trans h (steps_seq trans (b3 k m) h3)) (by omega)

theorem phase_r2_one (k : Nat) : Reach (P 1 (3 * k + 5)) (P (2 * k + 8) 5) := by
  obtain ⟨t, h⟩ := phase_loop 1 k 2
  rw [ft_split] at h
  have h3 : steps (24 * k + 99) ⟨cons false (cons true (cons false (cons true (rep (2 * k + 3) [false, true, false, true]
      (app [false, true, false, true] (app [false, true, true, false] (cons true blank))))))), cons true blank, .A⟩ =
      some ⟨rep (2 * (k + 2) + 3) [false, true, false, true] (cons false (cons true blank)), cons true blank, .A⟩ := by
    refine (r1b k).trans ?_
    show some (⟨app [false, true, false, true] (app [false, true, false, true] (rep (2 * k + 3) [false, true, false, true]
      (app [false, true, false, true] (app [false, true, false, true] (cons false (cons true blank)))))), _, _⟩ : Config) = _
    rw [rep_app_comm, rep_app_comm, show 2 * (k + 2) + 3 = 2 * k + 3 + 1 + 1 + 1 + 1 by omega]; rfl
  have h4 := reset_P (k + 2)
  rw [show 2 * (k + 2) + 4 = 2 * k + 8 by omega] at h4
  exact reach_of (steps_seq trans h (steps_seq trans (r1a k) (steps_seq trans h3 h4))) (by omega)

theorem phase_r2_zero (k : Nat) : Reach (P 0 (3 * k + 5)) (P 0 (8 * k + 18)) := by
  obtain ⟨t, h⟩ := phase_loop 0 k 2
  have h3 := finish (4 * k + 7) 0 2 0
  rw [show 2 + 0 + 2 * (4 * k + 7) + 2 = 8 * k + 18 by omega] at h3
  exact reach_of (steps_seq trans h (steps_seq trans (z2 k) h3)) (by omega)

/-- From `P 1 (3k+4)` the machine halts. -/
theorem halts_P1 (k : Nat) : TM.Halts trans (P 1 (3 * k + 4)) := by
  obtain ⟨t, h⟩ := phase_loop 1 k 1
  rw [ft_split] at h
  exact ⟨_, _, steps_seq trans h (h_pre k), rfl⟩

/-! ## The map -/

/-- The next phase start after `P m n`, or `none` where the machine halts (and for `n < 3`, which never occurs). -/
def next (m n : Nat) : Option (Nat × Nat) :=
  if n < 3 then none else
  let k := (n - 3) / 3
  match (n - 3) % 3, m with
  | 0, 0 => some (2 * k + 4, 5)
  | 0, m + 1 => some (m, 8 * k + 19)
  | 1, 0 => some (0, 8 * k + 18)
  | 1, 1 => none
  | 1, m + 2 => some (m, 8 * k + 29)
  | _, 0 => some (0, 8 * k + 18)
  | _, 1 => some (2 * k + 8, 5)
  | _, m + 2 => some (m, 8 * k + 35)

theorem next_reach (m n m' n' : Nat) (h : next m n = some (m', n')) : Reach (P m n) (P m' n') := by
  unfold next at h
  split at h
  · cases h
  · have hn : n = 3 * ((n - 3) / 3) + 3 + (n - 3) % 3 := by omega
    have hr : (n - 3) % 3 < 3 := Nat.mod_lt _ (by omega)
    generalize (n - 3) / 3 = k at h hn
    generalize (n - 3) % 3 = r at h hn hr
    subst hn
    match r, m, hr with
    | 0, 0, _ => simp at h; obtain ⟨rfl, rfl⟩ := h; exact phase_r0_zero k
    | 0, m + 1, _ => simp at h; obtain ⟨rfl, rfl⟩ := h; exact phase_r0 m k
    | 1, 0, _ => simp at h; obtain ⟨rfl, rfl⟩ := h; exact phase_r1_zero k
    | 1, 1, _ => simp at h
    | 1, m + 2, _ => simp at h; obtain ⟨rfl, rfl⟩ := h; exact phase_r1 m k
    | 2, 0, _ => simp at h; obtain ⟨rfl, rfl⟩ := h; exact phase_r2_zero k
    | 2, 1, _ => simp at h; obtain ⟨rfl, rfl⟩ := h; exact phase_r2_one k
    | 2, m + 2, _ => simp at h; obtain ⟨rfl, rfl⟩ := h; exact phase_r2 m k

/-- Blank tape reaches the first phase start `P 14 5`. -/
theorem init_P : steps 1098 init = some (P 14 5) := init_run

/-- The orbit of `(14, 5)`: `orbit i` is the `i`-th phase start, `none` once the map has stopped. -/
def orbit : Nat → Option (Nat × Nat)
  | 0 => some (14, 5)
  | i + 1 => (orbit i).bind fun x => next x.1 x.2

theorem orbit_reach : ∀ i m n, orbit i = some (m, n) → ∃ t, i ≤ t ∧ steps t init = some (P m n) := by
  intro i
  induction i with
  | zero => intro m n h; simp [orbit] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨1098, by omega, init_P⟩
  | succ i ih =>
    intro m' n' h
    simp only [orbit] at h
    cases ho : orbit i with
    | none => rw [ho] at h; cases h
    | some x =>
      rw [ho] at h
      obtain ⟨t, hti, ht⟩ := ih x.1 x.2 ho
      obtain ⟨u, hu, hu'⟩ := next_reach x.1 x.2 m' n' h
      exact ⟨t + u, by omega, steps_seq trans ht hu'⟩

/-- If the orbit never stops, the machine never halts from blank tape. -/
theorem not_halts_of_orbit (h : ∀ i, orbit i ≠ none) : ¬ HaltsFromBlank := by
  rintro ⟨N, c, hN, hc⟩
  have hi := h (N + 1)
  obtain ⟨⟨m, n⟩, hmn⟩ := Option.ne_none_iff_exists'.mp hi
  obtain ⟨t, ht, h'⟩ := orbit_reach (N + 1) m n hmn
  rw [show t = N + ((t - N - 1) + 1) by omega] at h'
  have hx := h'.symm.trans (steps_halt trans hN hc (t - N - 1))
  cases hx

/-- The orbit stays at `n ≥ 3` (every value of `next` has `n ≥ 5`), so it stops exactly at a point `(1, n)` with
`n % 3 = 1`. -/
theorem next_none (m n : Nat) (hn : 3 ≤ n) (h : next m n = none) : m = 1 ∧ n % 3 = 1 := by
  unfold next at h
  split at h
  · omega
  · have hr : (n - 3) % 3 < 3 := Nat.mod_lt _ (by omega)
    revert h
    generalize hrr : (n - 3) % 3 = r
    match r, m, hr with
    | 0, 0, _ => simp
    | 0, _ + 1, _ => simp
    | 1, 0, _ => simp
    | 1, 1, _ => intro _; omega
    | 1, _ + 2, _ => simp
    | 2, 0, _ => simp
    | 2, 1, _ => simp
    | 2, _ + 2, _ => simp
    | _ + 3, _, hr => exact absurd hr (by omega)

theorem next_ge (m n m' n' : Nat) (h : next m n = some (m', n')) : 5 ≤ n' := by
  unfold next at h
  split at h
  · cases h
  · revert h
    match (n - 3) % 3, m with
    | 0, 0 => intro h; simp at h; omega
    | 0, _ + 1 => intro h; simp at h; omega
    | 1, 0 => intro h; simp at h; omega
    | 1, 1 => simp
    | 1, _ + 2 => intro h; simp at h; omega
    | _ + 2, 0 => intro h; simp at h; omega
    | _ + 2, 1 => intro h; simp at h; omega
    | _ + 2, _ + 2 => intro h; simp at h; omega

/-- **The reduction.**  The machine halts from blank tape if and only if the orbit of `(14, 5)` under `next`
reaches a point `(1, n)` with `n % 3 = 1`. -/
theorem halts_iff : HaltsFromBlank ↔ ∃ i n, orbit i = some (1, n) ∧ n % 3 = 1 := by
  constructor
  · intro hh
    refine Classical.byContradiction fun hno => ?_
    apply not_halts_of_orbit _ hh
    intro i
    induction i with
    | zero => simp [orbit]
    | succ i ih =>
      obtain ⟨⟨m, n⟩, hmn⟩ := Option.ne_none_iff_exists'.mp ih
      have hn : 3 ≤ n := by
        cases i with
        | zero => simp [orbit] at hmn; omega
        | succ j =>
          simp only [orbit] at hmn
          cases hj : orbit j with
          | none => rw [hj] at hmn; cases hmn
          | some y => rw [hj] at hmn; have := next_ge y.1 y.2 m n hmn; omega
      simp only [orbit, hmn, Option.bind_some]
      intro hnone
      obtain ⟨rfl, hr⟩ := next_none m n hn hnone
      exact hno ⟨i, n, hmn, hr⟩
  · rintro ⟨i, n, hi, hr⟩
    obtain ⟨t, _, ht⟩ := orbit_reach i 1 n hi
    have hn : 4 ≤ n := by
      cases i with
      | zero => simp [orbit] at hi
      | succ j =>
        simp only [orbit] at hi
        cases hj : orbit j with
        | none => rw [hj] at hi; cases hi
        | some y => rw [hj] at hi; have := next_ge y.1 y.2 1 n hi; omega
    obtain ⟨u, c, hu, hc⟩ := halts_P1 ((n - 4) / 3)
    rw [show 3 * ((n - 4) / 3) + 4 = n by omega] at hu
    exact ⟨t + u, c, steps_seq trans ht hu, hc⟩

end H166535
