import Counter

/-!
# The counter counts: from any value to all ones

`next_sound` (Counter.lean) proves one increment.  Here: from phase R with any valid digits `ds` (m units, X first)
the machine reaches phase R with all `m` units at their maximum (`top true m`), after exactly
`capP true m - 1 - val true ds` increments, the wall having grown by that much; any tape `L` may lie left of the
digits.  The proof is by induction on `m`: the low `m` units count up to all ones, a carry raises the top unit by one
and clears the others (`carry`), and so on until the top unit is full (`up`).

Everything here is checked by Lean's kernel.
-/

namespace H136111

open TM

/-- How many values a unit holds: an `X` unit (`b = true`) 2, a `Y` unit 4. -/
def cap (b : Bool) : Nat := if b then 2 else 4

/-- The digits are in range, the first one of type `b`. -/
def Valid : Bool → List Nat → Prop
  | _, [] => True
  | b, d :: r => d < cap b ∧ Valid (!b) r

/-- The value of the digits (nearest the wall = lowest). -/
def val : Bool → List Nat → Nat
  | _, [] => 0
  | b, d :: r => d + cap b * val (!b) r

/-- The number of values of `m` units starting with type `b`. -/
def capP : Bool → Nat → Nat
  | _, 0 => 1
  | b, m + 1 => cap b * capP (!b) m

/-- All `m` units at their maximum. -/
def top : Bool → Nat → List Nat
  | _, 0 => []
  | b, m + 1 => (cap b - 1) :: top (!b) m

/-- All `m` units at zero. -/
def bot : Bool → Nat → List Nat
  | _, 0 => []
  | _, m + 1 => 0 :: bot true m

/-- The type of the unit after `m` units, the first of type `b`. -/
def par (b : Bool) (m : Nat) : Bool := if m % 2 = 0 then b else !b

theorem par_succ (b : Bool) (m : Nat) : par (!b) m = par b (m + 1) := by
  unfold par
  cases b <;> by_cases h : m % 2 = 0 <;> simp [h] <;> omega

theorem enc_append : ∀ (xs ys : List Nat) (b : Bool) (L : Tape),
    enc b (xs ++ ys) L = enc b xs (enc (par b xs.length) ys L)
  | [], ys, b, L => by simp [enc, par]
  | x :: xs, ys, true, L => by
    simp only [List.cons_append, enc, List.length_cons]
    rw [enc_append xs ys false L, ← par_succ]; rfl
  | x :: xs, ys, false, L => by
    simp only [List.cons_append, enc, List.length_cons]
    rw [enc_append xs ys true L, ← par_succ]; rfl

theorem R_append (xs ys : List Nat) (n : Nat) (L : Tape) :
    R (xs ++ ys) n L = R xs n (enc (par true xs.length) ys L) := by
  simp only [R, enc_append]

theorem R_snoc {xs : List Nat} {m : Nat} (hl : xs.length = m) (ys : List Nat) (n : Nat) (L : Tape) :
    R (xs ++ ys) n L = R xs n (enc (par true m) ys L) := by
  rw [R_append, hl]

theorem par_odd (j : Nat) : par true (2 * j + 1) = false := by
  unfold par; have : (2 * j + 1) % 2 = 1 := by omega
  simp [this]

theorem par_even (j : Nat) : par true (2 * j) = true := by
  unfold par; have : (2 * j) % 2 = 0 := by omega
  simp [this]

theorem top_length : ∀ (b : Bool) (m : Nat), (top b m).length = m
  | _, 0 => rfl
  | b, m + 1 => by simp [top, top_length (!b) m]

theorem bot_length : ∀ (b : Bool) (m : Nat), (bot b m).length = m
  | _, 0 => rfl
  | _, m + 1 => by simp [bot, bot_length true m]

theorem bot_any : ∀ (b : Bool) (m : Nat), bot b m = bot true m
  | _, 0 => rfl
  | _, _ + 1 => rfl

theorem val_bot : ∀ (b : Bool) (m : Nat), val b (bot b m) = 0
  | _, 0 => rfl
  | b, m + 1 => by simp only [bot, val]; rw [← bot_any (!b) m, val_bot]; simp

theorem valid_bot : ∀ (b : Bool) (m : Nat), Valid b (bot b m)
  | _, 0 => trivial
  | b, m + 1 => by
    refine ⟨by cases b <;> simp [cap], ?_⟩
    rw [← bot_any (!b) m]; exact valid_bot (!b) m

theorem cap_pos (b : Bool) : 2 ≤ cap b := by cases b <;> simp [cap]

theorem capP_pos : ∀ (b : Bool) (m : Nat), 1 ≤ capP b m
  | _, 0 => Nat.le_refl 1
  | b, m + 1 => by
    simp only [capP]
    have h1 := capP_pos (!b) m
    have h2 := cap_pos b
    exact Nat.le_trans h1 (Nat.le_mul_of_pos_left _ (by omega))

theorem val_lt : ∀ (b : Bool) (ds : List Nat), Valid b ds → val b ds < capP b ds.length
  | _, [], _ => by simp [val, capP]
  | b, d :: r, ⟨hd, hr⟩ => by
    simp only [val, capP, List.length_cons]
    have ih := val_lt (!b) r hr
    -- d + cap b * v < cap b * c  since d < cap b and v + 1 ≤ c
    have h3 : cap b * (val (!b) r + 1) ≤ cap b * capP (!b) r.length := Nat.mul_le_mul_left _ ih
    rw [Nat.mul_add, Nat.mul_one] at h3
    omega

theorem val_append : ∀ (b : Bool) (xs : List Nat) (d : Nat),
    val b (xs ++ [d]) = val b xs + capP b xs.length * d
  | b, [], d => by simp [val, capP]
  | b, x :: xs, d => by
    simp only [List.cons_append, val, capP, List.length_cons]
    rw [val_append (!b) xs d, Nat.mul_add, Nat.mul_assoc]; omega

theorem capP_succ : ∀ (b : Bool) (m : Nat), capP b (m + 1) = capP b m * cap (par b m)
  | b, 0 => by simp [capP, par]
  | b, m + 1 => by
    rw [capP, capP_succ (!b) m, par_succ, capP, Nat.mul_assoc]

theorem valid_append : ∀ (b : Bool) (xs : List Nat) (d : Nat),
    Valid b (xs ++ [d]) → Valid b xs ∧ d < cap (par b xs.length)
  | b, [], d, h => by simp [Valid] at h; exact ⟨trivial, by simp [par]; exact h⟩
  | b, x :: xs, d, ⟨hx, hr⟩ => by
    have ih := valid_append (!b) xs d hr
    refine ⟨⟨hx, ih.1⟩, ?_⟩
    simp only [List.length_cons]; rw [← par_succ]; exact ih.2

theorem top_succ : ∀ (b : Bool) (m : Nat), top b (m + 1) = top b m ++ [cap (par b m) - 1]
  | b, 0 => by simp [top, par]
  | b, m + 1 => by
    rw [top, top_succ (!b) m, par_succ]; rfl

theorem bot_succ : ∀ (m : Nat), bot true (m + 1) = bot true m ++ [0]
  | 0 => rfl
  | m + 1 => by
    show 0 :: bot true (m + 1) = (0 :: bot true m) ++ [0]
    rw [bot_succ m]; rfl

/-! ## The carry -/

theorem scan_ones_lt : ∀ (j k v : Nat) (r : List Nat), v < 3 → scan k (ones j ++ v :: r) = some (.inl (k + j, v, r))
  | 0, k, v, r, h => by
    show scan k (v :: r) = _
    unfold scan; simp [h]
  | j + 1, k, v, r, h => by
    show scan k (3 :: 1 :: (ones j ++ v :: r)) = _
    unfold scan; simp only [Nat.lt_irrefl, if_false, if_true]
    rw [scan_ones_lt j (k + 1) v r h]; simp only [Option.some.injEq, Sum.inl.injEq, Prod.mk.injEq, and_true]; omega

theorem scan_ones_30 : ∀ (j k : Nat) (r : List Nat), scan k (ones j ++ 3 :: 0 :: r) = some (.inr (k + j, r))
  | 0, k, r => by
    show scan k (3 :: 0 :: r) = _
    unfold scan; simp
  | j + 1, k, r => by
    show scan k (3 :: 1 :: (ones j ++ 3 :: 0 :: r)) = _
    unfold scan; simp only [Nat.lt_irrefl, if_false, if_true]
    rw [scan_ones_30 j (k + 1) r]; simp only [Option.some.injEq, Sum.inr.injEq, Prod.mk.injEq, and_true]; omega

theorem top_cons (b : Bool) (m : Nat) : top b (m + 1) = (cap b - 1) :: top (!b) m := rfl

theorem top_odd : ∀ (j : Nat), top true (2 * j + 1) = 1 :: ones j
  | 0 => rfl
  | j + 1 => by
    rw [show 2 * (j + 1) + 1 = 2 * j + 1 + 1 + 1 by omega, top_cons, top_cons]
    simp only [Bool.not_true, Bool.not_false]
    rw [top_odd j]; rfl

theorem top_even (j : Nat) : top true (2 * j + 2) = 1 :: (ones j ++ [3]) := by
  rw [show 2 * j + 2 = 2 * j + 1 + 1 by omega, top_succ, top_odd, par_odd]
  simp [cap]

theorem bot_odd : ∀ (j : Nat), bot true (2 * j + 1) = 0 :: zeros j
  | 0 => rfl
  | j + 1 => by
    rw [show 2 * (j + 1) + 1 = 2 * j + 1 + 1 + 1 by omega]
    show 0 :: 0 :: bot true (2 * j + 1) = 0 :: zeros (j + 1)
    rw [bot_odd j]; rfl

theorem bot_even (j : Nat) : bot true (2 * j + 2) = 0 :: (zeros j ++ [0]) := by
  rw [show 2 * j + 2 = 2 * j + 1 + 1 by omega, bot_succ, bot_odd]; rfl

/-- A carry over all-ones low units raises the next unit by one. -/
theorem carry (m d n : Nat) (L : Tape) (hd : d + 1 < cap (par true m)) :
    ∃ c, 1 ≤ c ∧ steps c (R (top true m ++ [d]) n L) = some (R (bot true m ++ [d + 1]) (n + 1) L) := by
  obtain ⟨j, rfl | rfl⟩ : ∃ j, m = 2 * j ∨ m = 2 * j + 1 := ⟨m / 2, by omega⟩
  · cases j with
    | zero =>
      have hd0 : d = 0 := by rw [show 0 = 2 * 0 by rfl, par_even] at hd; simp [cap] at hd; omega
      subst hd0
      exact ⟨_, by omega, next_sound L ⟨[0], n⟩ ⟨[1], n + 1⟩ _ rfl⟩
    | succ j =>
      have hm : 2 * (j + 1) = 2 * j + 2 := by omega
      have hd0 : d = 0 := by
        rw [par_even] at hd; simp [cap] at hd; omega
      subst hd0
      rw [hm, top_even, bot_even]
      refine ⟨60 * j + 48 * n + 182, by omega, ?_⟩
      have h := next_sound L ⟨1 :: (ones j ++ [3, 0]), n⟩ ⟨0 :: (zeros j ++ [0, 1]), n + 1⟩
        (60 * j + 48 * n + 182) (by
          show (match scan 0 (ones j ++ [3, 0]) with
            | some (.inl (j, v, r')) =>
              some ((⟨0 :: zeros j ++ (v + 1) :: r', n + 1⟩ : MS), 60 * j + 48 * n + (if v = 1 then 162 else 154))
            | some (.inr (j, r')) => some (⟨0 :: zeros j ++ 0 :: 1 :: r', n + 1⟩, 60 * j + 48 * n + 182)
            | none => none) = _
          rw [scan_ones_30 j 0 []]; simp)
      simpa [List.append_assoc] using h
  · have hd3 : d < 3 := by
      simp [par, cap] at hd; omega
    rw [top_odd, bot_odd]
    have h := next_sound L ⟨1 :: (ones j ++ [d]), n⟩ ⟨0 :: (zeros j ++ [d + 1]), n + 1⟩
      (60 * j + 48 * n + (if d = 1 then 162 else 154)) (by
        show (match scan 0 (ones j ++ [d]) with
            | some (.inl (j, v, r')) =>
              some ((⟨0 :: zeros j ++ (v + 1) :: r', n + 1⟩ : MS), 60 * j + 48 * n + (if v = 1 then 162 else 154))
            | some (.inr (j, r')) => some (⟨0 :: zeros j ++ 0 :: 1 :: r', n + 1⟩, 60 * j + 48 * n + 182)
            | none => none) = _
        rw [scan_ones_lt j 0 d [] hd3]; simp)
    have h154 : 154 ≤ (if d = 1 then 162 else 154) := by split <;> omega
    exact ⟨60 * j + 48 * n + (if d = 1 then 162 else 154), by omega, by simpa using h⟩

/-! ## Counting up -/

/-- **Counting**: from phase R with valid digits `ds` (`m` units) the machine reaches phase R with all units at their
maximum, after `capP true m - 1 - val true ds` increments (each one step or more), for every tape `L`. -/
theorem up : ∀ (m : Nat) (ds : List Nat), ds.length = m → Valid true ds → ∀ (n : Nat) (L : Tape),
    ∃ t, capP true m - 1 - val true ds ≤ t ∧
      steps t (R ds n L) = some (R (top true m) (n + (capP true m - 1 - val true ds)) L)
  | 0, ds, hl, _, n, L => by
    have : ds = [] := List.eq_nil_of_length_eq_zero hl
    subst this
    exact ⟨0, by simp [capP, val], by simp [capP, val, top]⟩
  | m + 1, ds, hl, hv, n, L => by
    -- ds = low ++ [d]
    obtain ⟨low, d, rfl⟩ : ∃ low d, ds = low ++ [d] := by
      have hne : ds ≠ [] := by intro h; subst h; simp at hl
      exact ⟨ds.dropLast, ds.getLast hne, (List.dropLast_concat_getLast hne).symm⟩
    have hlow : low.length = m := by simpa using hl
    obtain ⟨hvl, hd⟩ := valid_append true low d hv
    rw [hlow] at hd
    have hcap := capP_succ true m
    have hva := val_append true low d
    rw [hlow] at hva
    have hvlt := val_lt true low hvl
    rw [hlow] at hvlt
    -- the top digit goes from d to its maximum, k carries
    have loop : ∀ (k e n' : Nat), e + k + 1 = cap (par true m) →
        ∃ t, k * capP true m ≤ t ∧
          steps t (R (top true m ++ [e]) n' L) = some (R (top true m ++ [cap (par true m) - 1]) (n' + k * capP true m) L) := by
      intro k
      induction k with
      | zero => intro e n' he; have : e = cap (par true m) - 1 := by omega
                subst this; exact ⟨0, by simp, by simp⟩
      | succ k ih =>
        intro e n' he
        obtain ⟨c, hc1, hc⟩ := carry m e n' L (by omega)
        have hbot := up m (bot true m) (bot_length true m) (valid_bot true m) (n' + 1)
          (enc (par true m) [e + 1] L)
        obtain ⟨t2, ht2, h2⟩ := hbot
        rw [val_bot] at ht2 h2
        rw [← R_snoc (bot_length true m), ← R_snoc (top_length true m)] at h2
        obtain ⟨t3, ht3, h3⟩ := ih (e + 1) (n' + 1 + (capP true m - 1 - 0)) (by omega)
        refine ⟨c + (t2 + t3), ?_, steps_seq trans hc (steps_seq trans h2 (by
          have e1 : n' + 1 + (capP true m - 1 - 0) + k * capP true m = n' + (k + 1) * capP true m := by
            have := capP_pos true m
            rw [Nat.succ_mul]; omega
          rw [e1] at h3; exact h3))⟩
        have := capP_pos true m
        rw [Nat.succ_mul]; omega
    obtain ⟨t1, ht1, h1⟩ := up m low hlow hvl n (enc (par true m) [d] L)
    rw [← R_snoc hlow, ← R_snoc (top_length true m)] at h1
    obtain ⟨t2, ht2, h2⟩ := loop (cap (par true m) - 1 - d) d (n + (capP true m - 1 - val true low)) (by omega)
    rw [top_succ]
    have key : capP true (m + 1) - 1 - val true (low ++ [d]) =
        (capP true m - 1 - val true low) + (cap (par true m) - 1 - d) * capP true m := by
      rw [hcap, hva]
      have hk : cap (par true m) = (cap (par true m) - 1 - d) + d + 1 := by omega
      generalize cap (par true m) - 1 - d = k at hk ⊢
      rw [hk, Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.mul_comm (capP true m) k]
      omega
    refine ⟨t1 + t2, by rw [key]; omega, ?_⟩
    rw [key, ← Nat.add_assoc]
    exact steps_seq trans h1 h2

end H136111
