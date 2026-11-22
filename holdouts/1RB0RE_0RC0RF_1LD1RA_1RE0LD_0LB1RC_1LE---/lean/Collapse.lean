import Subround

/-!
# 1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---: sub-rounds, the collapse to a single block, and the rebuild

At the moments the head is in C on a 0 just right of a block of 1s the configurations of the run are mostly

    1^(3q) 0 1^(3 x_k + 2) 0 ... 0 1^(3 x_1 + 2) 0 1^l  C>  0^(u_1 + 1) 1 0^(u_2) 1 0^(u_3) 1 ... 0^inf

written `enc q D l us`, with the digits `D = [x_1, ..., x_k]` of the interior listed nearest the head first and
`us` the gaps of the zone (the first one without the head's cell).  The three rules of `Subround.lean` give:

* `subround`: while `D` is not empty, a sub-round is `W` on the interior (drop the nearest digit `a`, add 1 to the
  next one or 3 cells to the first block, put `a` zeros in front) and `gstep` on the counter (`l, us`):
  `l ≥ 2` becomes a new gap `l - 2` and `l = 1`; `l = 1` removes the leading gaps of 3 (`n` of them), takes 4 from
  the next gap and sets `l = 4n + 5`, or, if that gap is 0, removes it too, takes 2 from the one after it and sets
  `l = 4n + 4`.  `gstep` is undefined (`none`) at the other *small* gaps (`Small`: 1, 2, or 0 before 0 or 1),
  which are not covered here.
* `T_W`: the digits are the binary expansion of the number of sub-rounds left before the interior is a single
  block, `T D`, which drops by exactly 1 under `W`.
* `collapse`: from `enc q D l us` the machine reaches the single block `3 (mass q D)` after exactly `T D`
  sub-rounds, with the counter advanced `T D` times, provided no small gap is met; `regular_total` shows that none
  is met when `l ≡ 1` and every gap `≡ 3 (mod 4)` (the regular counter, a binary counter).
* `rebuild`: from a single block `3 (k + 1)` with `l ≥ 5` the next sub-round gives `3 2^k`, `l = 5` and a new gap
  `l - 5`; so with no small gap in the next `2^k - 1` sub-rounds the single block comes back with the same size
  (`rebuild_cycle`).  With `l = 1` it gives `3 2^k`, `l = 4`, and the first gap loses 2 (`rebuild_one`).  The
  run's single blocks grow only through the small gaps, which are not covered here.
-/

namespace H4320

open TM

/-- Interior blocks, nearest the head first: digit `d` is a block of `3d + 2` ones with a 0 on its far side. -/
def digs : List Nat → Tape → Tape
  | [], X => X
  | d :: ds, X => cons true (cons true (rep d [true, true, true] (cons false (digs ds X))))

/-- The first block, `3q` ones, with blank tape behind it. -/
def base (q : Nat) : Tape := rep q [true, true, true] blank

/-- The zone after the head cell: gaps of `u` zeros, each followed by a 1. -/
def zr : List Nat → Tape
  | [] => blank
  | u :: us => rep u [false] (cons true (zr us))

/-- The configuration: first block `3q`, interior digits `D`, last block `l`, zone gaps `us`. -/
def enc (q : Nat) (D : List Nat) (l : Nat) (us : List Nat) : Config :=
  ⟨rep l [true] (cons false (digs D (base q))), cons false (zr us), .C⟩

/-- The list operation W, with the first block: `(q, D) ↦ (q', D')`. -/
def W (q : Nat) : List Nat → Nat × List Nat
  | [] => (q, [])
  | [a] => (q + 1, List.replicate a 0)
  | a :: d :: ds => (q, List.replicate a 0 ++ (d + 1) :: ds)

/-- The carry of the counter: remove the leading gaps of 3 (counted in `n`), take 4 from the next one; a gap of 0
there is removed too and 2 are taken from the gap after it. -/
def gpop : List Nat → Nat → Option (Nat × List Nat)
  | [], n => some (4 * n + 5, [])
  | 3 :: us, n => gpop us (n + 1)
  | (u + 4) :: us, n => some (4 * n + 5, u :: us)
  | [0], n => some (4 * n + 4, [])
  | 0 :: (w + 2) :: us, n => some (4 * n + 4, w :: us)
  | _ :: _, _ => none

/-- The small gaps `gpop` does not cover: 1, 2, and 0 followed by 0 or 1. -/
def Small : List Nat → Prop
  | 1 :: _ => True
  | 2 :: _ => True
  | 0 :: 0 :: _ => True
  | 0 :: 1 :: _ => True
  | _ => False

/-- One step of the counter on (last block, zone gaps); `none` at a small gap. -/
def gstep : Nat × List Nat → Option (Nat × List Nat)
  | (b + 2, us) => some (1, b :: us)
  | (1, us) => gpop us 0
  | (0, _) => none

/-- `N` steps of the counter. -/
def giter : Nat → Nat × List Nat → Option (Nat × List Nat)
  | 0, x => some x
  | N + 1, x => (gstep x).bind (giter N)

/-- The number of sub-rounds before the interior is a single block. -/
def T : List Nat → Nat
  | [] => 0
  | x :: r => 2 ^ x * (1 + 2 * T r)

/-- The first block plus the digits plus their number: `W` keeps it. -/
def mass (q : Nat) (D : List Nat) : Nat := q + (D.map (· + 1)).sum

/-! ## Tape lemmas -/

theorem zr_threes (n : Nat) (us : List Nat) :
    zr (List.replicate n 3 ++ us) = rep n [false, false, false, true] (zr us) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append, rep_succ, ← ih]
    rfl

theorem digs_zeros (a : Nat) (Y : List Nat) (X : Tape) :
    digs (List.replicate a 0 ++ Y) X = rep a [true, true, false] (digs Y X) := by
  induction a with
  | zero => rfl
  | succ a ih =>
    rw [List.replicate_succ, List.cons_append, rep_succ, ← ih]
    rfl

theorem rep4 (n : Nat) (X : Tape) : rep n [true, true, true, true] X = rep (4 * n) [true] X := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [rep_succ, ih, show 4 * (n + 1) = 4 + 4 * n by omega, rep_add]
    rfl

theorem ones_zero (n : Nat) (X : Tape) :
    cons true (cons true (rep n [true, true, true, true] (cons true (cons true X)))) =
      rep (4 * n + 4) [true] X := by
  rw [rep4, show 4 * n + 4 = 2 + (4 * n + 2) by omega, rep_add, rep_add]
  rfl

theorem ones_long (n : Nat) (X : Tape) :
    cons true (cons true (cons true (rep n [true, true, true, true] (cons true (cons true X))))) =
      rep (4 * n + 5) [true] X := by
  rw [rep4, show 4 * n + 5 = 3 + (4 * n + 2) by omega, rep_add, rep_add]
  rfl

/-- What `W` does to the tape left of the last block. -/
theorem wleft (q a : Nat) (ds : List Nat) :
    rep a [true, true, false] (cons true (cons true (cons true (digs ds (base q))))) =
      digs (W q (a :: ds)).2 (base (W q (a :: ds)).1) := by
  cases ds with
  | nil => simp only [W]; rw [← List.append_nil (List.replicate a 0), digs_zeros]; rfl
  | cons d ds => simp only [W]; rw [digs_zeros]; rfl

/-- The shape of a zone seen by `gpop`: gaps of 3, then the end, a gap of at least 4, a gap of 0 at the end or
before a gap of at least 2, or a small gap. -/
theorem zone_cases (us : List Nat) :
    (∃ n, us = List.replicate n 3) ∨ (∃ n u rest, us = List.replicate n 3 ++ (u + 4) :: rest) ∨
      (∃ n, us = List.replicate n 3 ++ [0]) ∨ (∃ n w rest, us = List.replicate n 3 ++ 0 :: (w + 2) :: rest) ∨
      (∃ n rest, Small rest ∧ us = List.replicate n 3 ++ rest) := by
  induction us with
  | nil => exact Or.inl ⟨0, rfl⟩
  | cons v us ih =>
    by_cases h3 : v = 3
    · subst h3
      rcases ih with ⟨n, rfl⟩ | ⟨n, u, rest, rfl⟩ | ⟨n, rfl⟩ | ⟨n, w, rest, rfl⟩ | ⟨n, rest, hs, rfl⟩
      · exact Or.inl ⟨n + 1, rfl⟩
      · exact Or.inr (Or.inl ⟨n + 1, u, rest, rfl⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨n + 1, rfl⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n + 1, w, rest, rfl⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨n + 1, rest, hs, rfl⟩)))
    · match v, h3 with
      | 0, _ =>
        match us with
        | [] => exact Or.inr (Or.inr (Or.inl ⟨0, rfl⟩))
        | 0 :: us' => exact Or.inr (Or.inr (Or.inr (Or.inr ⟨0, 0 :: 0 :: us', trivial, rfl⟩)))
        | 1 :: us' => exact Or.inr (Or.inr (Or.inr (Or.inr ⟨0, 0 :: 1 :: us', trivial, rfl⟩)))
        | (w + 2) :: us' => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨0, w, us', rfl⟩)))
      | 1, _ => exact Or.inr (Or.inr (Or.inr (Or.inr ⟨0, 1 :: us, trivial, rfl⟩)))
      | 2, _ => exact Or.inr (Or.inr (Or.inr (Or.inr ⟨0, 2 :: us, trivial, rfl⟩)))
      | u + 4, _ => exact Or.inr (Or.inl ⟨0, u, us, rfl⟩)

theorem gpop_threes (n k : Nat) : gpop (List.replicate n 3) k = some (4 * (n + k) + 5, []) := by
  induction n generalizing k with
  | zero => simp [gpop]
  | succ n ih => rw [List.replicate_succ, gpop, ih]; congr 2; omega

theorem gpop_carry (n k u : Nat) (rest : List Nat) :
    gpop (List.replicate n 3 ++ (u + 4) :: rest) k = some (4 * (n + k) + 5, u :: rest) := by
  induction n generalizing k with
  | zero => simp [gpop]
  | succ n ih => rw [List.replicate_succ, List.cons_append, gpop, ih]; congr 2; omega

theorem gpop_zero_end (n k : Nat) : gpop (List.replicate n 3 ++ [0]) k = some (4 * (n + k) + 4, []) := by
  induction n generalizing k with
  | zero => simp [gpop]
  | succ n ih => rw [List.replicate_succ, List.cons_append, gpop, ih]; congr 2; omega

theorem gpop_zero_carry (n k w : Nat) (rest : List Nat) :
    gpop (List.replicate n 3 ++ 0 :: (w + 2) :: rest) k = some (4 * (n + k) + 4, w :: rest) := by
  induction n generalizing k with
  | zero => simp [gpop]
  | succ n ih => rw [List.replicate_succ, List.cons_append, gpop, ih]; congr 2; omega

theorem gpop_small (n k : Nat) (rest : List Nat) (hs : Small rest) :
    gpop (List.replicate n 3 ++ rest) k = none := by
  induction n generalizing k with
  | zero =>
    simp only [List.replicate_zero, List.nil_append]
    match rest, hs with
    | 1 :: _, _ => rfl
    | 2 :: _, _ => rfl
    | 0 :: 0 :: _, _ => rfl
    | 0 :: 1 :: _, _ => rfl
  | succ n ih => rw [List.replicate_succ, List.cons_append, gpop, ih]

theorem blank4 : blank = cons false (cons false (cons false (cons false blank))) := by
  simp only [cons_false_blank]

/-! ## One sub-round -/

/-- One sub-round with a non-empty interior is `W` on the interior and `gstep` on the counter, for every size. -/
theorem subround (q a : Nat) (ds : List Nat) (l : Nat) (us : List Nat) (x : Nat × List Nat)
    (hx : gstep (l, us) = some x) :
    ∃ n, steps n (enc q (a :: ds) l us) = some (enc (W q (a :: ds)).1 (W q (a :: ds)).2 x.1 x.2) := by
  have hl := wleft q a ds
  match l, hx with
  | b + 2, hx =>
    simp only [gstep, Option.some.injEq] at hx
    subst hx
    have h := glong a b (digs ds (base q)) (zr us)
    rw [hl, show rep (b + 1) [false] (cons true (zr us)) = cons false (zr (b :: us)) by rw [rep_succ]; rfl] at h
    exact ⟨_, h⟩
  | 1, hx =>
    simp only [gstep] at hx
    rcases zone_cases us with ⟨n, rfl⟩ | ⟨n, u, rest, rfl⟩ | ⟨n, rfl⟩ | ⟨n, w, rest, rfl⟩ | ⟨n, rest, hs, rfl⟩
    · rw [gpop_threes, Option.some.injEq] at hx
      subst hx
      have h := gshort a n (digs ds (base q)) blank
      rw [ones_long, hl, ← blank4] at h
      simp only [enc, Nat.add_zero]
      rw [← List.append_nil (List.replicate n 3), zr_threes]
      exact ⟨_, h⟩
    · rw [gpop_carry, Option.some.injEq] at hx
      subst hx
      have h := gshort a n (digs ds (base q)) (zr (u :: rest))
      rw [ones_long, hl] at h
      simp only [enc, Nat.add_zero]
      rw [zr_threes]
      exact ⟨_, h⟩
    · rw [gpop_zero_end, Option.some.injEq] at hx
      subst hx
      have h := gzero a n (digs ds (base q)) blank
      rw [ones_zero, hl] at h
      have e : zr [0] = cons true (cons false (cons false blank)) := by simp only [zr, rep_zero, cons_false_blank]
      simp only [enc, Nat.add_zero]
      rw [zr_threes, e]
      exact ⟨_, h⟩
    · rw [gpop_zero_carry, Option.some.injEq] at hx
      subst hx
      have h := gzero a n (digs ds (base q)) (zr (w :: rest))
      rw [ones_zero, hl] at h
      simp only [enc, Nat.add_zero]
      rw [zr_threes]
      exact ⟨_, h⟩
    · rw [gpop_small _ _ _ hs] at hx
      cases hx

/-! ## The collapse time -/

theorem T_zeros (a : Nat) (Y : List Nat) : T (List.replicate a 0 ++ Y) + 1 = 2 ^ a * (T Y + 1) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [List.replicate_succ, List.cons_append, T, Nat.pow_zero, Nat.one_mul, Nat.pow_succ]
    rw [show 1 + 2 * T (List.replicate a 0 ++ Y) + 1 = 2 * (T (List.replicate a 0 ++ Y) + 1) by omega, ih]
    rw [Nat.mul_comm (2 ^ a) 2, Nat.mul_assoc]

/-- `W` takes exactly one sub-round off the time left. -/
theorem T_W (q a : Nat) (ds : List Nat) : T (W q (a :: ds)).2 + 1 = T (a :: ds) := by
  cases ds with
  | nil => simp only [W]; rw [← List.append_nil (List.replicate a 0), T_zeros]; simp [T]
  | cons d ds =>
    simp only [W]; rw [T_zeros]; simp only [T]
    congr 1
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ d) 2, Nat.mul_assoc]; omega

theorem mass_W (q a : Nat) (ds : List Nat) : mass (W q (a :: ds)).1 (W q (a :: ds)).2 = mass q (a :: ds) := by
  have hz : ∀ Y : List Nat, ((List.replicate a 0 ++ Y).map (· + 1)).sum = a + (Y.map (· + 1)).sum := by
    intro Y
    induction a with
    | zero => simp
    | succ a ih => rw [List.replicate_succ, List.cons_append, List.map_cons, List.sum_cons, ih]; omega
  cases ds with
  | nil => simp only [W, mass]; rw [← List.append_nil (List.replicate a 0), hz]; simp; omega
  | cons d ds => simp only [W, mass]; rw [hz]; simp; omega

theorem T_pos (x : Nat) (r : List Nat) : 0 < T (x :: r) := by
  simp only [T]; exact Nat.mul_pos (Nat.two_pow_pos x) (by omega)

/-- **Between rebuilds.**  From `enc q D l us` the machine reaches the single block `3 (mass q D)` after exactly
`T D` sub-rounds, the counter advanced `T D` times, if the counter meets no small gap on the way. -/
theorem collapse (N : Nat) : ∀ (q : Nat) (D : List Nat) (x y : Nat × List Nat), T D = N → giter N x = some y →
    ∃ n, steps n (enc q D x.1 x.2) = some (enc (mass q D) [] y.1 y.2) := by
  induction N with
  | zero =>
    intro q D x y hT hy
    simp only [giter, Option.some.injEq] at hy
    subst hy
    cases D with
    | nil => exact ⟨0, by simp [mass]⟩
    | cons a r => exact absurd hT (Nat.ne_of_gt (T_pos a r))
  | succ N ih =>
    intro q D x y hT hy
    cases D with
    | nil => simp [T] at hT
    | cons a ds =>
      simp only [giter] at hy
      cases hx : gstep x with
      | none => rw [hx] at hy; cases hy
      | some x' =>
        rw [hx, Option.bind_some] at hy
        obtain ⟨n₁, h₁⟩ := subround q a ds x.1 x.2 x' hx
        have hT' : T (W q (a :: ds)).2 = N := by have := T_W q a ds; omega
        obtain ⟨n₂, h₂⟩ := ih _ _ _ _ hT' hy
        rw [mass_W] at h₂
        exact ⟨n₁ + n₂, steps_seq trans h₁ h₂⟩

/-- `N` steps of `W`. -/
def Witer : Nat → Nat × List Nat → Nat × List Nat
  | 0, x => x
  | N + 1, (q, D) => Witer N (W q D)

/-- `N` sub-rounds, for `N` up to the collapse time, if the counter meets no small gap on the way. -/
theorem advance (N : Nat) : ∀ (q : Nat) (D : List Nat) (x y : Nat × List Nat), N ≤ T D → giter N x = some y →
    ∃ n, steps n (enc q D x.1 x.2) = some (enc (Witer N (q, D)).1 (Witer N (q, D)).2 y.1 y.2) := by
  induction N with
  | zero =>
    intro q D x y _ hy
    simp only [giter, Option.some.injEq] at hy
    subst hy
    exact ⟨0, rfl⟩
  | succ N ih =>
    intro q D x y hT hy
    cases D with
    | nil => simp [T] at hT
    | cons a ds =>
      simp only [giter] at hy
      cases hx : gstep x with
      | none => rw [hx] at hy; cases hy
      | some x' =>
        rw [hx, Option.bind_some] at hy
        obtain ⟨n₁, h₁⟩ := subround q a ds x.1 x.2 x' hx
        have hT' : N ≤ T (W q (a :: ds)).2 := by have := T_W q a ds; omega
        obtain ⟨n₂, h₂⟩ := ih _ _ _ _ hT' hy
        exact ⟨n₁ + n₂, steps_seq trans h₁ h₂⟩

/-! ## The regular counter never meets a small gap -/

/-- Regular counter: last block `≡ 1` and every gap `≡ 3 (mod 4)` (all segments multiples of 4). -/
def Reg (x : Nat × List Nat) : Prop := x.1 % 4 = 1 ∧ ∀ u ∈ x.2, u % 4 = 3

theorem gpop_reg (us : List Nat) (k : Nat) (h : ∀ u ∈ us, u % 4 = 3) :
    ∃ y, gpop us k = some y ∧ Reg y := by
  induction us generalizing k with
  | nil => exact ⟨_, rfl, by show (4 * k + 5) % 4 = 1; omega, by simp⟩
  | cons u us ih =>
    have hu : u % 4 = 3 := h u (by simp)
    have hus : ∀ v ∈ us, v % 4 = 3 := fun v hv => h v (by simp [hv])
    by_cases h3 : u = 3
    · subst h3; simp only [gpop]; exact ih (k + 1) hus
    · obtain ⟨w, rfl⟩ : ∃ w, u = w + 4 := ⟨u - 4, by omega⟩
      refine ⟨_, rfl, ?_, ?_⟩
      · show (4 * k + 5) % 4 = 1; omega
      · intro v hv
        simp only [List.mem_cons] at hv
        rcases hv with rfl | hv
        · omega
        · exact hus v hv

theorem regular_step (x : Nat × List Nat) (h : Reg x) : ∃ y, gstep x = some y ∧ Reg y := by
  obtain ⟨l, us⟩ := x
  obtain ⟨hl, hus⟩ := h
  simp only at hl hus
  match l, hl with
  | 1, _ => exact gpop_reg us 0 hus
  | b + 2, hl =>
    refine ⟨_, rfl, ?_, ?_⟩
    · show 1 % 4 = 1; rfl
    · intro v hv
      simp only [List.mem_cons] at hv
      rcases hv with rfl | hv
      · omega
      · exact hus v hv

theorem regular_total (N : Nat) : ∀ x, Reg x → ∃ y, giter N x = some y ∧ Reg y := by
  induction N with
  | zero => intro x hx; exact ⟨x, rfl, hx⟩
  | succ N ih =>
    intro x hx
    obtain ⟨x', h₁, h₂⟩ := regular_step x hx
    obtain ⟨y, h₃, h₄⟩ := ih x' h₂
    exact ⟨y, by simp only [giter, h₁, Option.bind_some, h₃], h₄⟩

/-- With a regular counter the collapse always happens. -/
theorem collapse_regular (q : Nat) (D : List Nat) (x : Nat × List Nat) (hx : Reg x) :
    ∃ y n, Reg y ∧ steps n (enc q D x.1 x.2) = some (enc (mass q D) [] y.1 y.2) := by
  obtain ⟨y, h₁, h₂⟩ := regular_total (T D) x hx
  obtain ⟨n, h⟩ := collapse (T D) q D x y rfl h₁
  exact ⟨y, n, h₂, h⟩

/-! ## The rebuild -/

theorem rebuild_tail (k : Nat) :
    rep (k + 1) [false, true, true] (cons true blank) = cons false (digs (List.replicate k 0) (base 1)) := by
  rw [← List.append_nil (List.replicate k 0), digs_zeros]
  rw [show rep (k + 1) [false, true, true] (cons true blank) = rep k [false, true, true] (app [false] (base 1)) by
    rw [← rep_app_comm]; rfl]
  rw [← rep_rotate k [false] [true, true, false] [false, true, true] rfl]
  rfl

theorem rebuild_left (k : Nat) :
    cons true (cons true (cons true (cons true (cons true (rep (k + 1) [false, true, true] (cons true blank)))))) =
      rep 5 [true] (cons false (digs (List.replicate k 0) (base 1))) := by
  rw [rebuild_tail]; rfl

/-- **The rebuild sub-round.**  A single block `3 (k + 1)` with last block `b + 5` becomes `3 2^k` with last block 5
and a new gap `b` in front of the zone. -/
theorem rebuild (k b : Nat) (us : List Nat) :
    ∃ n, steps n (enc (k + 1) [] (b + 5) us) = some (enc 1 (List.replicate k 0) 5 (b :: us)) := by
  have h := single b k (zr us)
  rw [rebuild_left, show rep (b + 1) [false] (cons true (zr us)) = cons false (zr (b :: us)) by rw [rep_succ]; rfl] at h
  exact ⟨_, h⟩

/-- The rebuild sub-round with last block 1: `3 2^k`, last block 4, and the first gap loses 2. -/
theorem rebuild_one (k u : Nat) (us : List Nat) :
    ∃ n, steps n (enc (k + 1) [] 1 ((u + 2) :: us)) = some (enc 1 (List.replicate k 0) 4 (u :: us)) := by
  have h := singleone k (zr (u :: us))
  rw [rebuild_tail] at h
  exact ⟨_, h⟩

/-- The same at the end of the zone (blank tape after the last block). -/
theorem rebuild_one_blank (k : Nat) :
    ∃ n, steps n (enc (k + 1) [] 1 []) = some (enc 1 (List.replicate k 0) 4 []) := by
  have h := singleone k blank
  have e : cons false (cons false (cons false blank)) = cons false blank := by
    rw [cons_false_blank, cons_false_blank, cons_false_blank]
  rw [rebuild_tail, e] at h
  exact ⟨_, h⟩

theorem T_replicate (k : Nat) : T (List.replicate k 0) + 1 = 2 ^ k := by
  have := T_zeros k []
  simp [T] at this
  simpa using this

theorem mass_replicate (k : Nat) : mass 1 (List.replicate k 0) = k + 1 := by
  simp only [mass]
  induction k with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, List.map_cons, List.sum_cons]; omega

/-- **A rebuild cycle.**  From a single block `3 (k + 1)` with last block `b + 5`, if the counter meets no small gap
in the `2^k - 1` sub-rounds of the collapse, the single block comes back with the same size `3 (k + 1)` after
`2^k` sub-rounds. -/
theorem rebuild_cycle (k b : Nat) (us : List Nat) (y : Nat × List Nat)
    (hy : giter (2 ^ k - 1) (5, b :: us) = some y) :
    ∃ n, steps n (enc (k + 1) [] (b + 5) us) = some (enc (k + 1) [] y.1 y.2) := by
  obtain ⟨n₁, h₁⟩ := rebuild k b us
  have hT : T (List.replicate k 0) = 2 ^ k - 1 := by have := T_replicate k; omega
  obtain ⟨n₂, h₂⟩ := collapse _ 1 (List.replicate k 0) (5, b :: us) y hT hy
  rw [mass_replicate] at h₂
  exact ⟨n₁ + n₂, steps_seq trans h₁ h₂⟩

end H4320
