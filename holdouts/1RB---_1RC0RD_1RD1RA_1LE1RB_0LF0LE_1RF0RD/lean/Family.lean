import Start

/-!
# The halting family halts, for every size

`fam_halts m`: from the post-event configuration `PN m (m+2) (2^(m+1) + 1)` the machine halts.  This is where the
phase map gets stuck (`Fam`).  The run, with the rules of `Count.lean`, `Overflow.lean` and `Junction.lean`:

* `2^m - 1` counts make the string all ones; the overflowing count (`overflow_true`) resets it and leaves a K
  junction with the counter `0 0^(m+1) 1` behind it;
* the junction machine carries through the zeros (`carry0`, then counts to full), `m + 1` times, until the left
  string is `0 1^(m+1)` and the counter `1^(m+1)` with `0 1` behind the junction;
* the next carry makes the left string overflow again: the walk of `overflow_false` (`overflow_walk`) leaves the
  string `1 0^(m+2)` and the counter `0^(m+1)` followed by `0 1 1` instead of a junction;
* `2^(m+1) - 1` counts fill the counter, and the carry reads `0 1 1`: B0 → C, C1 → A, A1 halts.
-/

namespace H140108

open TM

/-- The walk of an overflowing left increment with `b1 = 0`, for any tape `Z` right of the three 0s. -/
theorem overflow_walk (m : Nat) (Z : Tape) :
    Reach ⟨enc (false :: List.replicate m true) L0, cons false (cons false (cons false Z)), .E⟩
      ⟨enc (false :: true :: List.replicate (m + 1) false) L0, Z, .B⟩ := by
  have e : enc (false :: List.replicate m true) L0 = cons true (cons false (rep (2 * m + 2) [true] blank)) := by
    show cons true (cons false (enc (List.replicate m true) L0)) = _
    rw [enc_trues_L0]
  rw [e]
  have h1 : steps 11 ⟨cons true (cons false (rep (2 * m + 2) [true] blank)), cons false (cons false (cons false Z)), .E⟩
      = some ⟨cons true (rep (2 * m + 2) [true] blank), cons false (cons true (cons true (cons false Z))), .E⟩ := rfl
  refine Reach.trans' (reach_of h1) ?_
  rw [← rep1, show (blank : Tape) = cons false blank from (cons_false_blank).symm]
  refine Reach.trans' (reach_of (shift (2 * m + 2 + 1) (cons false blank) (cons true (cons true (cons false Z))))) ?_
  have h2 : steps 4 ⟨cons false blank, cons false (rep (2 * m + 2 + 1) [true] (cons true (cons true (cons false Z)))), .E⟩
      = some ⟨cons false (cons true (cons true blank)),
          rep (2 * m + 2) [true] (cons true (cons true (cons false Z))), .D⟩ := rfl
  refine Reach.trans' (reach_of h2) ?_
  rw [rep_one_comm, rep_one_comm, ← rep1, ← rep1, show 2 * m + 2 + 1 + 1 = 2 * (m + 2) by omega, ← rep_two]
  refine Reach.trans' (reach_of (pairs (m + 2) _ _)) ?_
  rw [rep_succ, show app [false, true] (rep (m + 1) [false, true] (cons false (cons true (cons true blank))))
      = cons false (cons true (rep (m + 1) [false, true] (cons false (cons true (cons true blank))))) from rfl,
    rot01]
  have h3 : ∀ Q : Tape, steps 9 ⟨cons false (cons true (cons false Q)), cons false Z, .D⟩
      = some ⟨cons true (cons false (cons true (cons true Q))), Z, .B⟩ := fun _ => rfl
  refine Reach.trans' (reach_of (h3 _)) ?_
  have e5 : enc (false :: true :: List.replicate (m + 1) false) L0
      = cons true (cons false (cons true (cons true (rep (m + 1) [true, false] L0)))) := by
    show cons true (cons false (cons true (cons true (enc (List.replicate (m + 1) false) L0)))) = _
    rw [← List.append_nil (List.replicate (m + 1) false), enc_falses]; rfl
  rw [e5]
  exact Reach.refl' _

/-- The machine halts from `c`. -/
def HaltsFrom (c : Cfg St) : Prop := ∃ c', Reach c c' ∧ TM.step trans c' = none

theorem HaltsFrom.of_reach {a b : Cfg St} (h : Reach a b) (hb : HaltsFrom b) : HaltsFrom a := by
  obtain ⟨c, hc, hs⟩ := hb
  exact ⟨c, Reach.trans' h hc, hs⟩

theorem rep_succ_in (n : Nat) (b : Bool) (s : Tape) : rep (n + 1) [b] s = rep n [b] (cons b s) := by
  rw [rep1, rep_one_comm]

/-- The end of the family: the left string `0 1^(m+1)` overflows at the next carry, and the machine halts. -/
theorem fam_end (m : Nat) :
    HaltsFrom ⟨enc (false :: bitsOf (m + 2) (2 ^ (m + 2) - 2)) L0,
      ctr (bitsOf (m + 1) (2 ^ (m + 1) - 1)) (jt true [false, true]), .B⟩ := by
  have eb : bitsOf (m + 2) (2 ^ (m + 2) - 2) = false :: List.replicate (m + 1) true := by
    have h := bitsOf_top (m + 1) false
    simpa using h
  rw [eb, bitsOf_full]
  refine HaltsFrom.of_reach (brun (m + 1) _ _) ?_
  generalize hX : enc (false :: false :: List.replicate (m + 1) true) L0 = X
  have h1 : steps 3 ⟨rep (3 * (m + 1)) [true] X, jt true [false, true], .B⟩
      = some ⟨rep (3 * (m + 1) + 1) [true] X, cons true (cons true (cons true blank)), .E⟩ := by
    show steps 3 ⟨rep (3 * (m + 1)) [true] X, cons false (cons false (cons false (cons true blank))), .B⟩ = _
    rfl
  refine HaltsFrom.of_reach (reach_of h1) ?_
  have e : rep (3 * (m + 1) + 1) [true] X
      = rep (3 * (m + 1) + 2) [true] (cons false (enc (false :: List.replicate (m + 1) true) L0)) := by
    rw [← hX]
    show rep (3 * (m + 1) + 1) [true] (cons true (cons false (enc (false :: List.replicate (m + 1) true) L0))) = _
    rw [rep_one_comm]; rfl
  rw [e]
  refine HaltsFrom.of_reach (reach_of (erase (3 * (m + 1) + 2) _ _)) ?_
  rw [rep1]
  refine HaltsFrom.of_reach (overflow_walk (m + 1) _) ?_
  have eb1 : bitsOf (m + 3) 1 = true :: List.replicate (m + 2) false := by
    rw [bitsOf_succ, show (1 : Nat) / 2 = 0 from rfl, bitsOf_zero]; rfl
  generalize hT : cons false (cons true (cons true blank)) = T
  have eR : rep (3 * (m + 1) + 1) [false] (cons true (cons true blank)) = ctr (bitsOf (m + 1) 0) T := by
    rw [bitsOf_zero, rep_succ_in, hT, ← List.append_nil (List.replicate (m + 1) false), ctr_zeros, rep_three]; rfl
  rw [eR, ← eb1]
  have hp := pow_pos' (m + 1)
  have h4 : 2 ^ (m + 2 + 1) = 2 * (2 * 2 ^ (m + 1)) := by rw [pow_succ', pow_succ']
  have hcm := count_many (m + 2) 1 (m + 1) 0 L0 T (2 ^ (m + 1) - 1) (by omega) (by omega)
  refine HaltsFrom.of_reach hcm ?_
  rw [Nat.zero_add, bitsOf_full]
  refine HaltsFrom.of_reach (brun (m + 1) _ _) ?_
  rw [← hT]
  refine ⟨_, reach_of (show steps 2 ⟨rep (3 * (m + 1)) [true] (enc (false :: bitsOf (m + 2 + 1) (1 + 2 * (2 ^ (m + 1) - 1))) L0),
      cons false (cons true (cons true blank)), .B⟩ = some ⟨cons true (cons true (rep (3 * (m + 1)) [true]
        (enc (false :: bitsOf (m + 2 + 1) (1 + 2 * (2 ^ (m + 1) - 1))) L0))), cons true blank, .A⟩ from rfl), rfl⟩

/-- The junction machine of the family after `l` carries: the left string `2^(l+1) - 2`, `low = 1^l`. -/
def fst (m l : Nat) : Cfg St :=
  ⟨enc (false :: bitsOf (m + 2) (2 ^ (l + 1) - 2)) L0,
    ctr (bitsOf l (2 ^ l - 1)) (jt true (List.replicate (m + 2 - l) false ++ [true])), .B⟩

theorem fam_loop (m : Nat) : ∀ j l, 1 ≤ l → l + j = m + 1 → Reach (fst m l) (fst m (m + 1))
  | 0, l, _, h => by rw [show l = m + 1 by omega]; exact Reach.refl' _
  | j + 1, l, hl, h => by
    refine Reach.trans' ?_ (fam_loop m j (l + 1) (by omega) (by omega))
    unfold fst
    rw [bitsOf_full, show m + 2 - l = (m + 1 - l) + 1 by omega, List.replicate_succ, List.cons_append]
    have hp := pow_pos' l
    have h1 : 2 ^ (l + 1) = 2 * 2 ^ l := pow_succ' l
    have h2 : 2 ^ (l + 2) = 2 * 2 ^ (l + 1) := pow_succ' (l + 1)
    have h3 : 2 ^ (l + 2) ≤ 2 ^ (m + 2) := Nat.pow_le_pow_right (by omega) (by omega)
    have hm2 : 2 ^ (m + 2) = 2 * (2 * 2 ^ m) := by rw [pow_succ', pow_succ']
    have hm1 : 2 ^ (m + 1) = 2 * 2 ^ m := pow_succ' m
    have hm1' : 2 ^ (m + 1 + 1) = 2 * (2 * 2 ^ m) := by rw [pow_succ', pow_succ']
    refine Reach.trans' (carry0 true l (m + 1) (2 ^ (l + 1) - 2) (by omega) _ L0) ?_
    rw [← bitsOf_pow]
    have hc := count_many (m + 1) (2 ^ (l + 1) - 2 + 2) (l + 1) (2 ^ l) L0
      (jt true (List.replicate (m + 1 - l) false ++ [true])) (2 ^ l - 1) (by omega) (by omega)
    rw [show 2 ^ (l + 1) - 2 + 2 + 2 * (2 ^ l - 1) = 2 ^ (l + 1 + 1) - 2 by omega,
      show 2 ^ l + (2 ^ l - 1) = 2 ^ (l + 1) - 1 by omega] at hc
    rw [show m + 2 - (l + 1) = m + 1 - l by omega]
    exact hc

/-- **The halting family halts**, for every `m`. -/
theorem fam_halts (m : Nat) : HaltsFrom (PN m (m + 2) (2 ^ (m + 1) + 1)) := by
  have hp := pow_pos' m
  have h1 : 2 ^ (m + 1) = 2 * 2 ^ m := pow_succ' m
  have h2 : 2 ^ (m + 2) = 2 * 2 ^ (m + 1) := pow_succ' (m + 1)
  unfold PN P
  rw [ctr_P_pad]
  have hc := count_many (m + 1) (2 ^ (m + 1) + 1) (m + 2) (2 ^ m) L0 blank (2 ^ m - 1) (by omega) (by omega)
  refine HaltsFrom.of_reach hc ?_
  have et : bitsOf (m + 1 + 1) (2 ^ (m + 1) + 1 + 2 * (2 ^ m - 1)) = true :: List.replicate (m + 1) true := by
    rw [← bitsOf_top (m + 1) true]; congr 1; simp; omega
  rw [et, show 2 ^ m + (2 ^ m - 1) = 2 ^ (m + 1) - 1 by omega]
  have hds : false ∈ bitsOf (m + 2) (2 ^ (m + 1) - 1) := false_mem_bitsOf _ _ (by omega)
  refine HaltsFrom.of_reach (overflow_true (m + 1) _ hds) ?_
  rw [bitsOf_inc _ _ (by omega), show 2 ^ (m + 1) - 1 + 1 = 2 ^ (m + 1) by omega, bitsOf_pow,
    ← bitsOf_zero (m + 1 + 1)]
  have hk := carry0 true 0 (m + 1) 0 (by omega) (List.replicate (m + 1) false ++ [true]) L0
  simp only [List.replicate_zero, List.nil_append] at hk
  refine HaltsFrom.of_reach hk ?_
  have e1 : fst m 1 = ⟨enc (false :: bitsOf (m + 1 + 1) (0 + 2)) L0,
      ctr [true] (jt true (List.replicate (m + 1) false ++ [true])), .B⟩ := by
    unfold fst; rfl
  rw [← e1]
  refine HaltsFrom.of_reach (fam_loop m m 1 (by omega) (by omega)) ?_
  unfold fst
  rw [show m + 2 - (m + 1) = 1 by omega]
  exact fam_end m

end H140108
