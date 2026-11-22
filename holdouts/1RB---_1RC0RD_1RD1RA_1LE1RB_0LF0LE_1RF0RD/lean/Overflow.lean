import Junction

/-!
# The overflowing count

In the run the tape left of the bit string is `1 1` and blank (`L0`).  A count whose left increment carries out of
the top bit (`b1 :: 1^m`, all of `hi` ones) walks into that blank: the whole block of ones is shifted right, F
writes two new 1s on the blank, and D comes back over the block.  The bit string is reset and the counter
(incremented as in every count) is left one cell out of phase with the head:

* `overflow_true` (`b1 = 1`): the string becomes `0^(m+1)` (same length) and the right side `0 ctr(inc ds)`,
  that is `jt true (false :: inc ds)`;
* `overflow_false` (`b1 = 0`): the string becomes `1 0^(m+1)` (one bit longer) and the right side
  `jt false (inc ds)`.
-/

namespace H140108

open TM

/-- The tape left of the bit string in the run: `1 1`, then blank. -/
abbrev L0 : Tape := cons true (cons true blank)

theorem enc_trues_L0 (m : Nat) : enc (List.replicate m true) L0 = rep (2 * m + 2) [true] blank := by
  rw [← List.append_nil (List.replicate m true), enc_trues, rep_two]
  show rep (2 * m) [true] (cons true (cons true blank)) = _
  rw [rep_one_comm, rep_one_comm]; rfl

theorem enc_zeros (k : Nat) (T : Tape) :
    enc (false :: List.replicate k false) T = cons true (cons false (rep k [true, false] T)) := by
  show cons true (cons false (enc (List.replicate k false) T)) = _
  rw [← List.append_nil (List.replicate k false), enc_falses]; rfl

theorem overflow_true (m : Nat) (ds : List Bool) (hd : false ∈ ds) :
    Reach ⟨enc (false :: true :: List.replicate m true) L0, ctr ds blank, .B⟩
      ⟨enc (false :: List.replicate (m + 1) false) L0, jt true (false :: inc ds), .B⟩ := by
  obtain ⟨t, ds', e1, e2⟩ := inc_split ds hd
  rw [e2, e1]
  refine Reach.trans' (carry t (false :: ds') _ blank) ?_
  refine Reach.trans' (erase_phase t true (List.replicate m true) ds' L0 blank) ?_
  generalize hZ : ctr (List.replicate t false ++ true :: ds') blank = Z
  have e : enc (true :: List.replicate m true) L0 = rep (2 * m + 4) [true] (cons false blank) := by
    show enc (List.replicate (m + 1) true) L0 = _
    rw [enc_trues_L0, cons_false_blank, show 2 * (m + 1) + 2 = 2 * m + 4 by omega]
  rw [e]
  refine Reach.trans' (reach_of (shift (2 * m + 4) (cons false blank) (cons false Z))) ?_
  have h1 : steps 4 ⟨cons false blank, cons false (rep (2 * m + 4) [true] (cons false Z)), .E⟩
      = some ⟨cons false (cons true (cons true blank)), rep (2 * m + 3) [true] (cons false Z), .D⟩ := by
    show steps 4 ⟨cons false blank, cons false (cons true (rep (2 * m + 3) [true] (cons false Z))), .E⟩ = _
    rfl
  refine Reach.trans' (reach_of h1) ?_
  rw [rep1, ← rep_one_comm, show 2 * m + 2 = 2 * (m + 1) by omega, ← rep_two]
  refine Reach.trans' (reach_of (pairs (m + 1) _ _)) ?_
  have h2 : steps 1 ⟨rep (m + 1) [false, true] (cons false L0), cons true (cons false Z), .D⟩
      = some ⟨cons true (rep (m + 1) [false, true] (cons false L0)), cons false Z, .B⟩ := rfl
  refine Reach.trans' (reach_of h2) ?_
  rw [rot01, ← hZ, enc_zeros]
  exact Reach.refl' _

theorem overflow_false (m : Nat) (ds : List Bool) (hd : false ∈ ds) :
    Reach ⟨enc (false :: false :: List.replicate m true) L0, ctr ds blank, .B⟩
      ⟨enc (false :: true :: List.replicate (m + 1) false) L0, jt false (inc ds), .B⟩ := by
  obtain ⟨t, ds', e1, e2⟩ := inc_split ds hd
  rw [e2, e1]
  refine Reach.trans' (carry t (false :: ds') _ blank) ?_
  refine Reach.trans' (erase_phase t false (List.replicate m true) ds' L0 blank) ?_
  rw [ctr_jt]
  generalize hZ : jt false (List.replicate t false ++ true :: ds') = Z
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
  rw [← hZ]
  have e5 : enc (false :: true :: List.replicate (m + 1) false) L0
      = cons true (cons false (cons true (cons true (rep (m + 1) [true, false] L0)))) := by
    show cons true (cons false (cons true (cons true (enc (List.replicate (m + 1) false) L0)))) = _
    rw [← List.append_nil (List.replicate (m + 1) false), enc_falses]; rfl
  rw [e5]
  exact Reach.refl' _

end H140108
