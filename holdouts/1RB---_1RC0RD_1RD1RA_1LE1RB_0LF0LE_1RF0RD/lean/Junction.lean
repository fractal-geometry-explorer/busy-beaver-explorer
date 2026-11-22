import Bits

/-!
# Counters with a junction: the counts after an overflow

After an overflow the right side of the tape is a counter `low` in groups `0 0 d` (lowest digit nearest the head),
then a *junction*, then a second counter `H` whose groups are shifted against those of `low`:

* `jt true H`  (a *K junction*): the first group of `H` lost its two 0s, `h ctr(H')` for `H = h :: H'`;
* `jt false H` (a *J junction*): the first group of `H` lost one 0, `0 h ctr(H')`.

A count works as in `Count.lean` while `low` has a 0.  When `low` is all ones the carry runs into the junction:

* `carry0`: the next digit of `H` is 0 (either junction): `low` becomes `0^l 1`, one digit longer, and that digit
  leaves `H` (`jt` keeps its kind).
* `carryJ1`: J junction, next digit 1, then `1^s 0`: the head crosses those digits in state A (one cell out of
  phase), `low` becomes `0^(l+s+1) 1` and `s + 2` digits leave `H`.
* `absorb_even`, `absorb_odd`: K junction, next digit 1.  B reads a 1, writes 0, and the run turns there: the
  block of ones it wrote is shifted right, and the cells of `low` and of the junction become `3l/2 + 1` (l even) or
  `(3l+3)/2` (l odd) new low bits of the left string (`0^(3l/2)` then a 1 in place of the old scratch 0, or
  `1 0^((3l-1)/2)` then that 1).  The digit leaves `H`, and the right side is `jt false H'` (l even) or `jt true H'`
  (l odd) with `low` empty.  The left string beyond its scratch bit is never touched.
* `turn_count`: the end of every carry: D turns on a 0 after `n+1` written ones, E erases them, and the left
  string is incremented as in a normal count.
-/

namespace H140108

open TM

/-- The tape right of a junction: `jt true (h :: H) = h ctr(H)`, `jt false (h :: H) = 0 h ctr(H)`. -/
def jt : Bool → List Bool → Tape
  | _, [] => blank
  | true, h :: H => cons h (ctr H blank)
  | false, h :: H => cons false (cons h (ctr H blank))

theorem jt_nil_pad (k : Bool) : jt k [false] = jt k [] := by
  cases k
  · show cons false (cons false blank) = blank
    rw [cons_false_blank, cons_false_blank]
  · show cons false blank = blank
    rw [cons_false_blank]

/-- `ctr H blank` is `0 (jt false H)`. -/
theorem ctr_jt (H : List Bool) : ctr H blank = cons false (jt false H) := by
  cases H with
  | nil => show blank = cons false blank; rw [cons_false_blank]
  | cons h H => rfl

/-- `jt false H` is `0 (jt true H)`. -/
theorem jt_false_true (H : List Bool) : jt false H = cons false (jt true H) := by
  cases H with
  | nil => show blank = cons false blank; rw [cons_false_blank]
  | cons h H => rfl

/-- **The end of a carry.**  D turns on a 0 after `n + 1` ones it wrote; E erases them and the left string is
incremented as in a count: the ones become 0s and the turning cell a 1. -/
theorem turn_count (n : Nat) (b1 : Bool) (hi : List Bool) (hh : false ∈ hi) (L Z : Tape) :
    Reach ⟨rep (n + 1) [true] (enc (false :: b1 :: hi) L), cons false Z, .D⟩
      ⟨enc (false :: b1 :: inc hi) L, rep (n + 1) [false] (cons true Z), .B⟩ := by
  have h1 : steps 1 ⟨rep (n + 1) [true] (enc (false :: b1 :: hi) L), cons false Z, .D⟩
      = some ⟨rep n [true] (enc (false :: b1 :: hi) L), cons true (cons true Z), .E⟩ := rfl
  refine Reach.trans' (reach_of h1) ?_
  have e : rep n [true] (enc (false :: b1 :: hi) L) = rep (n + 1) [true] (cons false (enc (b1 :: hi) L)) := by
    show rep n [true] (cons true (cons false (enc (b1 :: hi) L))) = _
    rw [rep_one_comm]; rfl
  rw [e]
  refine Reach.trans' (reach_of (erase (n + 1) (enc (b1 :: hi) L) (cons true Z))) ?_
  obtain ⟨r, hrest, e3, e4⟩ := inc_split hi hh
  rw [e4, e3]
  cases b1 with
  | false =>
    have h := walk_false r hrest L (rep (n + 1) [false] (cons true Z))
    rw [show List.replicate (r + 2) false ++ true :: hrest
        = false :: false :: (List.replicate r false ++ true :: hrest) by simp [List.replicate_succ]] at h
    exact h
  | true => exact walk_true r hrest L _

/-- `turn_count` with the left string as a number. -/
theorem turn_count_nat (n w v : Nat) (hv : v + 2 < 2 ^ (w + 1)) (L Z : Tape) :
    Reach ⟨rep (n + 1) [true] (enc (false :: bitsOf (w + 1) v) L), cons false Z, .D⟩
      ⟨enc (false :: bitsOf (w + 1) (v + 2)) L, rep (n + 1) [false] (cons true Z), .B⟩ := by
  rw [pow_succ'] at hv
  have e1 : (v + 2) % 2 = v % 2 := by omega
  have e2 : (v + 2) / 2 = v / 2 + 1 := by omega
  rw [bitsOf_succ, bitsOf_succ, e1, e2, ← bitsOf_inc w (v / 2) (by omega)]
  exact turn_count n _ _ (false_mem_bitsOf w (v / 2) (by omega)) L Z

/-- B crosses a counter of ones, writing `1 1 1` on each group. -/
theorem brun (l : Nat) (X R : Tape) :
    Reach ⟨X, ctr (List.replicate l true) R, .B⟩ ⟨rep (3 * l) [true] X, R, .B⟩ := by
  have h := carry l [] X R
  rw [List.append_nil] at h
  exact h

/-- The counter `0^l 1` followed by `T` is `0^(3l+2) 1 T`. -/
theorem ctr_low (l : Nat) (T : Tape) :
    ctr (List.replicate l false ++ [true]) T = rep (3 * l + 2) [false] (cons true T) := by
  rw [ctr_zeros, rep_three]
  show rep (3 * l) [false] (cons false (cons false (cons true T))) = _
  rw [rep_one_comm, rep_one_comm]; rfl

/-- **Carry into a 0 digit.**  `low` all ones, the next digit of `H` 0 (either junction): `low` becomes `0^l 1`. -/
theorem carry0 (k : Bool) (l w v : Nat) (hv : v + 2 < 2 ^ (w + 1)) (H : List Bool) (L : Tape) :
    Reach ⟨enc (false :: bitsOf (w + 1) v) L, ctr (List.replicate l true) (jt k (false :: H)), .B⟩
      ⟨enc (false :: bitsOf (w + 1) (v + 2)) L, ctr (List.replicate l false ++ [true]) (jt k H), .B⟩ := by
  refine Reach.trans' (brun l _ _) ?_
  rw [ctr_low]
  -- pad `H` so that it has a first digit
  have hp : ∃ h H', jt k H = jt k (h :: H') ∧ ctr H blank = ctr (h :: H') blank := by
    cases H with
    | nil => exact ⟨false, [], (jt_nil_pad k).symm, (ctr_blank []).symm⟩
    | cons h H' => exact ⟨h, H', rfl, rfl⟩
  obtain ⟨h, H', e1, e2⟩ := hp
  rw [e1]
  cases k with
  | true =>
    show Reach ⟨_, cons false (ctr H blank), .B⟩ _
    rw [e2]
    have h1 : steps 2 ⟨rep (3 * l) [true] (enc (false :: bitsOf (w + 1) v) L),
        cons false (cons false (cons false (cons h (ctr H' blank)))), .B⟩
        = some ⟨rep (3 * l + 1 + 1) [true] (enc (false :: bitsOf (w + 1) v) L),
          cons false (cons h (ctr H' blank)), .D⟩ := rfl
    refine Reach.trans' (reach_of h1) ?_
    exact turn_count_nat (3 * l + 1) w v hv L _
  | false =>
    show Reach ⟨_, cons false (cons false (ctr H blank)), .B⟩ _
    rw [e2]
    have h1 : steps 2 ⟨rep (3 * l) [true] (enc (false :: bitsOf (w + 1) v) L),
        cons false (cons false (cons false (cons false (cons h (ctr H' blank))))), .B⟩
        = some ⟨rep (3 * l + 1 + 1) [true] (enc (false :: bitsOf (w + 1) v) L),
          cons false (cons false (cons h (ctr H' blank))), .D⟩ := rfl
    refine Reach.trans' (reach_of h1) ?_
    exact turn_count_nat (3 * l + 1) w v hv L _

/-- **Carry through a J junction into `1 1^s 0`.**  The head crosses the digits in state A; `low` becomes
`0^(l+s+1) 1` and `s + 2` digits leave `H`. -/
theorem carryJ1 (l s w v : Nat) (hv : v + 2 < 2 ^ (w + 1)) (H : List Bool) (L : Tape) :
    Reach ⟨enc (false :: bitsOf (w + 1) v) L,
        ctr (List.replicate l true) (jt false (true :: (List.replicate s true ++ false :: H))), .B⟩
      ⟨enc (false :: bitsOf (w + 1) (v + 2)) L, ctr (List.replicate (l + s + 1) false ++ [true]) (jt false H), .B⟩ := by
  refine Reach.trans' (brun l _ _) ?_
  generalize hX : enc (false :: bitsOf (w + 1) v) L = X
  show Reach ⟨rep (3 * l) [true] X, cons false (cons true (ctr (List.replicate s true ++ false :: H) blank)), .B⟩ _
  have h1 : steps 2 ⟨rep (3 * l) [true] X, cons false (cons true (ctr (List.replicate s true ++ false :: H) blank)), .B⟩
      = some ⟨rep (3 * l + 2) [true] X, ctr (List.replicate s true ++ false :: H) blank, .A⟩ := rfl
  refine Reach.trans' (reach_of h1) ?_
  generalize hY : rep (3 * l + 2) [true] X = Y
  have hA : Reach ⟨Y, ctr (List.replicate s true ++ false :: H) blank, .A⟩ ⟨rep (3 * s) [true] Y, ctr (false :: H) blank, .A⟩ := by
    rw [ctr_ones, ← rep_three]
    have c0 : ∀ L R : Tape, steps 3 ⟨app [] L, app [false, false, true] R, .A⟩
        = some ⟨app [] (app [true, true, true] L), R, .A⟩ := fun _ _ => rfl
    exact reach_of (cross_r trans c0 s Y _)
  refine Reach.trans' hA ?_
  generalize hY' : rep (3 * s) [true] Y = Y'
  have e0 : ctr (false :: H) blank = cons false (cons false (cons false (cons false (jt false H)))) := by
    show cons false (cons false (cons false (ctr H blank))) = _
    rw [ctr_jt]
  rw [e0]
  have h2 : steps 3 ⟨Y', cons false (cons false (cons false (cons false (jt false H)))), .A⟩
      = some ⟨rep 3 [true] Y', cons false (jt false H), .D⟩ := rfl
  refine Reach.trans' (reach_of h2) ?_
  rw [← hY', ← hY, ← rep_add, ← rep_add, ← hX, ctr_low,
    show 3 + 3 * s + (3 * l + 2) = (3 * l + 3 * s + 4) + 1 by omega,
    show 3 * (l + s + 1) + 2 = (3 * l + 3 * s + 4) + 1 by omega]
  exact turn_count_nat (3 * l + 3 * s + 4) w v hv L _

theorem rep1 (n : Nat) (b : Bool) (s : Tape) : rep (n + 1) [b] s = cons b (rep n [b] s) := rfl

/-- The shared start of an absorption: B runs over the ones of `low` and reads the 1 of the K junction, writes 0,
D turns, the ones (with the scratch 1) are shifted right, F fills and turns, D is left on `2l` ones. -/
theorem absorb_start (l : Nat) (bs H : List Bool) (L : Tape) :
    Reach ⟨enc (false :: bs) L, ctr (List.replicate l true) (jt true (true :: H)), .B⟩
      ⟨cons false (cons true (cons true (enc bs L))), rep (3 * l + 1) [true] (jt false H), .D⟩ := by
  refine Reach.trans' (brun l _ _) ?_
  generalize hY : enc bs L = Y
  generalize hR : jt false H = R
  have e : jt true (true :: H) = cons true (cons false R) := by
    rw [← hR]; show cons true (ctr H blank) = _; rw [ctr_jt]
  rw [e]
  show Reach ⟨rep (3 * l) [true] (cons true (cons false (enc bs L))), _, .B⟩ _
  rw [hY]
  have h1 : steps 2 ⟨rep (3 * l) [true] (cons true (cons false Y)), cons true (cons false R), .B⟩
      = some ⟨rep (3 * l) [true] (cons true (cons false Y)), cons false (cons true R), .E⟩ := rfl
  refine Reach.trans' (reach_of h1) ?_
  rw [rep_one_comm, ← rep1]
  refine Reach.trans' (reach_of (shift (3 * l + 1) (cons false Y) (cons true R))) ?_
  have h2 : steps 4 ⟨cons false Y, cons false (rep (3 * l + 1) [true] (cons true R)), .E⟩
      = some ⟨cons false (cons true (cons true Y)), rep (3 * l) [true] (cons true R), .D⟩ := rfl
  refine Reach.trans' (reach_of h2) ?_
  rw [rep_one_comm, ← rep1]
  exact Reach.refl' _

theorem rot01 (n : Nat) (S : Tape) : rep n [false, true] (cons false S) = cons false (rep n [true, false] S) :=
  (rep_rotate n [false] [true, false] [false, true] rfl S).symm

/-- **Absorption, `low` of even length `2n`.**  The `6n + 2` cells of `low` and the junction become the bits
`0^(3n)` and a 1 in place of the scratch 0; the right side is `jt false H`. -/
theorem absorb_even (n : Nat) (bs H : List Bool) (L : Tape) :
    Reach ⟨enc (false :: bs) L, ctr (List.replicate (2 * n) true) (jt true (true :: H)), .B⟩
      ⟨enc (false :: (List.replicate (3 * n) false ++ true :: bs)) L, jt false H, .B⟩ := by
  refine Reach.trans' (absorb_start (2 * n) bs H L) ?_
  generalize hY : enc bs L = Y
  generalize hR : jt false H = R
  rw [show 3 * (2 * n) + 1 = 2 * (3 * n) + 1 by omega, rep_succ, show app [true] (rep (2 * (3 * n)) [true] R)
    = rep (2 * (3 * n)) [true] (cons true R) from (rep_one_comm true _ R).symm, ← rep_two]
  refine Reach.trans' (reach_of (pairs (3 * n) _ _)) ?_
  have h1 : steps 1 ⟨rep (3 * n) [false, true] (cons false (cons true (cons true Y))), cons true R, .D⟩
      = some ⟨cons true (rep (3 * n) [false, true] (cons false (cons true (cons true Y)))), R, .B⟩ := rfl
  refine Reach.trans' (reach_of h1) ?_
  rw [rot01]
  show Reach _ ⟨cons true (cons false (enc (List.replicate (3 * n) false ++ true :: bs) L)), R, .B⟩
  rw [enc_falses]
  show Reach _ ⟨cons true (cons false (rep (3 * n) [true, false] (cons true (cons true (enc bs L))))), R, .B⟩
  rw [hY]
  exact Reach.refl' _

/-- **Absorption, `low` of odd length `2n + 1`.**  The cells become the bits `1 0^(3n+1)` and a 1 in place of the
scratch 0; the right side is `jt true H`. -/
theorem absorb_odd (n : Nat) (bs H : List Bool) (L : Tape) :
    Reach ⟨enc (false :: bs) L, ctr (List.replicate (2 * n + 1) true) (jt true (true :: H)), .B⟩
      ⟨enc (false :: (true :: List.replicate (3 * n + 1) false ++ true :: bs)) L, jt true H, .B⟩ := by
  refine Reach.trans' (absorb_start (2 * n + 1) bs H L) ?_
  generalize hY : enc bs L = Y
  rw [jt_false_true]
  generalize hR : jt true H = R
  rw [show 3 * (2 * n + 1) + 1 = 2 * (3 * n + 2) by omega, ← rep_two]
  refine Reach.trans' (reach_of (pairs (3 * n + 2) _ _)) ?_
  have h1 : steps 9 ⟨rep (3 * n + 2) [false, true] (cons false (cons true (cons true Y))), cons false R, .D⟩
      = some ⟨cons true (cons false (cons true (cons true (cons true
          (rep (3 * n) [false, true] (cons false (cons true (cons true Y)))))))), R, .B⟩ := rfl
  refine Reach.trans' (reach_of h1) ?_
  rw [rot01]
  show Reach _ ⟨cons true (cons false (cons true (cons true
    (enc (List.replicate (3 * n + 1) false ++ true :: bs) L)))), R, .B⟩
  rw [enc_falses]
  show Reach _ ⟨cons true (cons false (cons true (cons true (cons true (cons false
    (rep (3 * n) [true, false] (cons true (cons true (enc bs L))))))))), R, .B⟩
  rw [hY]
  exact Reach.refl' _

end H140108
