import Word

/-! # The pass in deficit form

`visc` (`lean/Word.lean`) carries a count `n` of visits along the word.  Here the count is written as
`n = 2 ^ e - c`: `e` (the *level*) goes up by one at every doubler and down by one at every digit block, and the
*deficit* `c` is a small number:

* a `0` at a block start becomes `1` and takes one visit: `c + 1`;
* a digit block `1?0` becomes `b 0 0` with `b = 1` exactly when `c` is even, and passes on `c / 2` (rounded down);
* a doubler `1010` passes on `2 c`;
* the pass stops when `c = 2 ^ e` (no visit left).

At level `0` (count `1`) a digit block becomes `0 0 0` and passes the single visit on.  `visd_eq` proves that this is
exactly `visc`, so `roundW` and `run` are this computation started from level `0`, deficit `0` (`roundW_visd`).

So the cells a round writes are parities of the deficit, and the round ends where the deficit catches up with
`2 ^ e`, which only happens where the level is small, at the word end.  A count that is an exact power of two
(`c = 0`) leaves every digit block it crosses unchanged (`visd_digit_exact`); only the zeros at block starts change
the deficit. -/

namespace H28035

open TM

/-- `visd f e c w`: the pass of `visc` with the count written as `2 ^ e - c`. -/
def visd : Nat → Nat → Nat → List Bool → Res
  | 0, _, _, _ => .stuck
  | f + 1, e, c, w =>
    if c = 2 ^ e then .ok w else
    match w with
    | false :: s => visd f e (c + 1) (true :: s)
    | true :: false :: false :: s =>
      match (if e = 0 then visd f 0 0 s else visd f (e - 1) (c / 2) s) with
      | .ok s' => .ok ((if e = 0 then false else bit (c + 1)) :: false :: false :: s')
      | r => r
    | true :: true :: false :: s =>
      match (if e = 0 then visd f 0 0 s else visd f (e - 1) (c / 2) s) with
      | .ok s' => .ok ((if e = 0 then false else bit (c + 1)) :: false :: false :: s')
      | r => r
    | true :: false :: true :: false :: s =>
      match visd f (e + 1) (2 * c) s with
      | .ok s' => .ok (true :: false :: true :: false :: s')
      | r => r
    | true :: false :: true :: true :: s => visd f e (c + 1) (false :: false :: false :: true :: s)
    | true :: true :: true :: true :: _ => .halt
    | true :: true :: true :: false :: true :: s => visd f e (c + 1) (true :: false :: true :: false :: true :: s)
    | true :: true :: true :: false :: false :: _ => .stuck
    | w => visd f e c (w ++ [false])

/-- The digit rule in deficit form: `n + 1 = 2 ^ e - c` visits to a digit block write `bit n` and pass on
`1 + n / 2`; that is `2 ^ (e - 1) - c / 2` with parity bit `bit (c + 1)` when `e ≥ 1`, and `1` with bit `0` when
`e = 0`. -/
theorem digit_arith {e c n : Nat} (hn : 2 ^ e - c = n + 1) :
    (if e = 0 then 0 else 2 ^ (e - 1) - c / 2) = 1 + n / 2 - (if e = 0 then 1 else 0) ∧
    (if e = 0 then 0 else c / 2) ≤ (if e = 0 then 2 ^ 0 else 2 ^ (e - 1)) ∧
    (if e = 0 then false else bit (c + 1)) = bit n := by
  rcases Nat.eq_zero_or_pos e with he | he
  · subst he; simp at hn ⊢; have : c = 0 := by omega
    subst this; have : n = 0 := by omega
    subst this; simp [bit]
  · have hk : 2 ^ e = 2 * 2 ^ (e - 1) := by
      rw [← Nat.pow_succ']; congr 1; omega
    have he' : e ≠ 0 := by omega
    simp only [he', ite_false]
    refine ⟨by omega, by omega, ?_⟩
    simp only [bit]
    have : (c + 1) % 2 = n % 2 := by omega
    rw [this]

/-- `visd` is `visc`: the pass with the count `2 ^ e - c`. -/
theorem visd_eq : ∀ (f e c : Nat) (w : List Bool), c ≤ 2 ^ e → visd f e c w = visc f (2 ^ e - c) w
  | 0, e, c, w, _ => by simp [visd, visc]
  | f + 1, e, c, w, hc => by
    by_cases h0 : c = 2 ^ e
    · subst h0
      have h1 : visd (f + 1) e (2 ^ e) w = .ok w := by
        show (if 2 ^ e = 2 ^ e then Res.ok w else _) = _
        simp only [↓reduceIte]
      rw [h1, Nat.sub_self]; rfl
    · obtain ⟨n, hn⟩ : ∃ n, 2 ^ e - c = n + 1 := ⟨2 ^ e - c - 1, by omega⟩
      have hlt : c + 1 ≤ 2 ^ e := by omega
      have hn1 : 2 ^ e - (c + 1) = n := by omega
      have hd : 2 ^ (e + 1) - 2 * c = 2 * (n + 1) := by rw [Nat.pow_succ]; omega
      have hd2 : 2 * c ≤ 2 ^ (e + 1) := by rw [Nat.pow_succ]; omega
      have da3 := (digit_arith hn).2.2
      have hdig : ∀ s, (if e = 0 then visd f 0 0 s else visd f (e - 1) (c / 2) s) = visc f (1 + n / 2) s := by
        intro s
        have da1 := (digit_arith hn).1
        have da2 := (digit_arith hn).2.1
        rcases Nat.eq_zero_or_pos e with he | he
        · subst he
          have : n = 0 := by simp at hn; omega
          subst this
          simp only [↓reduceIte]; rw [visd_eq f 0 0 s (by simp)]
        · have he' : e ≠ 0 := by omega
          simp only [he', ite_false] at da1 da2 ⊢
          have h2 : 2 ^ (e - 1) - c / 2 = 1 + n / 2 := by omega
          rw [visd_eq f (e - 1) (c / 2) s da2, h2]
      rw [hn]
      have hv : ∀ w', visd f e c w' = visc f (n + 1) w' := fun w' => by rw [visd_eq f e c w' hc, hn]
      match w with
      | false :: s =>
        show (if c = 2 ^ e then Res.ok _ else visd f e (c + 1) (true :: s)) = visc f n (true :: s)
        simp only [h0, ↓reduceIte]; rw [visd_eq f e (c + 1) _ hlt, hn1]
      | true :: false :: false :: s =>
        show (if c = 2 ^ e then Res.ok _ else
            match (if e = 0 then visd f 0 0 s else visd f (e - 1) (c / 2) s) with
            | .ok s' => .ok ((if e = 0 then false else bit (c + 1)) :: false :: false :: s')
            | r => r) =
          (match visc f (1 + n / 2) s with
            | .ok s' => .ok (bit n :: false :: false :: s')
            | r => r)
        simp only [h0, ↓reduceIte]; rw [hdig, da3]
      | true :: true :: false :: s =>
        show (if c = 2 ^ e then Res.ok _ else
            match (if e = 0 then visd f 0 0 s else visd f (e - 1) (c / 2) s) with
            | .ok s' => .ok ((if e = 0 then false else bit (c + 1)) :: false :: false :: s')
            | r => r) =
          (match visc f (1 + n / 2) s with
            | .ok s' => .ok (bit n :: false :: false :: s')
            | r => r)
        simp only [h0, ↓reduceIte]; rw [hdig, da3]
      | true :: false :: true :: false :: s =>
        show (if c = 2 ^ e then Res.ok _ else
            match visd f (e + 1) (2 * c) s with
            | .ok s' => .ok (true :: false :: true :: false :: s')
            | r => r) =
          (match visc f (2 * (n + 1)) s with
            | .ok s' => .ok (true :: false :: true :: false :: s')
            | r => r)
        simp only [h0, ↓reduceIte]; rw [visd_eq f (e + 1) (2 * c) _ hd2, hd]
      | true :: false :: true :: true :: s =>
        show (if c = 2 ^ e then Res.ok _ else visd f e (c + 1) (false :: false :: false :: true :: s)) =
          visc f n (false :: false :: false :: true :: s)
        simp only [h0, ↓reduceIte]; rw [visd_eq f e (c + 1) _ hlt, hn1]
      | true :: true :: true :: true :: s =>
        show (if c = 2 ^ e then Res.ok _ else Res.halt) = Res.halt
        simp only [h0, ↓reduceIte]
      | true :: true :: true :: false :: true :: s =>
        show (if c = 2 ^ e then Res.ok _ else visd f e (c + 1) (true :: false :: true :: false :: true :: s)) =
          visc f n (true :: false :: true :: false :: true :: s)
        simp only [h0, ↓reduceIte]; rw [visd_eq f e (c + 1) _ hlt, hn1]
      | true :: true :: true :: false :: false :: s =>
        show (if c = 2 ^ e then Res.ok _ else Res.stuck) = Res.stuck
        simp only [h0, ↓reduceIte]
      | [] =>
        show (if c = 2 ^ e then Res.ok _ else visd f e c ([] ++ [false])) = visc f (n + 1) ([] ++ [false])
        simp only [h0, ↓reduceIte]; rw [hv]
      | [true] =>
        show (if c = 2 ^ e then Res.ok _ else visd f e c ([true] ++ [false])) = visc f (n + 1) ([true] ++ [false])
        simp only [h0, ↓reduceIte]; rw [hv]
      | [true, false] =>
        show (if c = 2 ^ e then Res.ok _ else visd f e c ([true, false] ++ [false])) =
          visc f (n + 1) ([true, false] ++ [false])
        simp only [h0, ↓reduceIte]; rw [hv]
      | [true, true] =>
        show (if c = 2 ^ e then Res.ok _ else visd f e c ([true, true] ++ [false])) =
          visc f (n + 1) ([true, true] ++ [false])
        simp only [h0, ↓reduceIte]; rw [hv]
      | [true, false, true] =>
        show (if c = 2 ^ e then Res.ok _ else visd f e c ([true, false, true] ++ [false])) =
          visc f (n + 1) ([true, false, true] ++ [false])
        simp only [h0, ↓reduceIte]; rw [hv]
      | [true, true, true] =>
        show (if c = 2 ^ e then Res.ok _ else visd f e c ([true, true, true] ++ [false])) =
          visc f (n + 1) ([true, true, true] ++ [false])
        simp only [h0, ↓reduceIte]; rw [hv]
      | [true, true, true, false] =>
        show (if c = 2 ^ e then Res.ok _ else visd f e c ([true, true, true, false] ++ [false])) =
          visc f (n + 1) ([true, true, true, false] ++ [false])
        simp only [h0, ↓reduceIte]; rw [hv]

/-- A round is the deficit pass from level `0`, deficit `0` (count `1`). -/
theorem roundW_visd (f : Nat) (w : List Bool) : roundW f w = visd f 0 0 (true :: false :: w) := by
  rw [visd_eq f 0 0 _ (by simp)]; rfl

/-- An exact power of two (deficit `0`, level at least 1) leaves a digit block `1 0 0` as it is and passes an exact
power of two on. -/
theorem visd_digit_exact (f e : Nat) (s : List Bool) (he : 1 ≤ e) :
    visd (f + 1) e 0 (true :: false :: false :: s) =
      match visd f (e - 1) 0 s with
      | .ok s' => .ok (true :: false :: false :: s')
      | r => r := by
  have h0 : (0 : Nat) ≠ 2 ^ e := by have := Nat.one_le_two_pow (n := e); omega
  have he' : e ≠ 0 := by omega
  simp [visd, h0, he', bit]

/-! ## Two rounds over the same digit blocks

The *remaining count* `n` (visits still to deliver) changes by `n ↦ n - 1` at a `0` at a block start, `n ↦ ⌈n/2⌉`
at a digit block and `n ↦ 2 n` at a doubler; the round stops on the `0` where `n` reaches `0`.

Take two consecutive rounds and a stretch where every block of the later round starts on the last cell (a `0`) of a
digit block of the earlier one. The earlier round enters such a block with `m` visits (`z = 1` if the block starts
with `0`, which takes one visit first); the later one enters with `n`, takes one visit on the `0` and halves. -/

/-- The gap `δ = n - 2 m` between the two rounds becomes `⌊δ / 2⌋ + z - (m - z) % 2` one block later. -/
theorem offset2_gap (m n z : Nat) (hzm : z ≤ m) :
    ((n / 2 : Nat) : Int) - 2 * (((m - z + 1) / 2 : Nat) : Int)
      = ((n : Int) - 2 * m) / 2 + z - (((m - z) % 2 : Nat) : Int) := by
  omega

/-- So a gap in `[-3, 2]` stays there, and a gap outside moves toward it. -/
theorem offset2_gap_bound (m n z : Nat) (hz : z ≤ 1) (hzm : z ≤ m)
    (h : -3 ≤ (n : Int) - 2 * m ∧ (n : Int) - 2 * m ≤ 2) :
    -3 ≤ ((n / 2 : Nat) : Int) - 2 * (((m - z + 1) / 2 : Nat) : Int) ∧
    ((n / 2 : Nat) : Int) - 2 * (((m - z + 1) / 2 : Nat) : Int) ≤ 2 := by
  omega

/-- A round that ends with two such blocks and then stops on the next `0` entered the first of them with 4 to 7
visits: each block takes one visit and halves, and the stop needs exactly one visit left. The danger (3 visits in the
last block) is 6 or 7. -/
theorem junk_after_digit_count (n : Nat) (h : n / 2 / 2 = 1) : 4 ≤ n ∧ n ≤ 7 := by
  omega

end H28035
