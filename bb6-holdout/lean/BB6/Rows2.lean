import BB6.Rows

/-!
# Rows of the round recurrence, continued: the gap meets a wall, or runs off the end

* gap meets wall `0 0` across stripe `(10)^k`: WALLBOUNCE^k then one MEET rule, by what the shift finds next —
  a marker, a wall, a block, blank tape, or the end marker;
* gap with nothing to its right: WALLBOUNCE^k then GAP→blank end.

With the written tape `L 1 0 0 E>0 (10)^k 0 (10)^j X`, the wall is the `0` after the stripe together with the
stripe's last `0`, and `(10)^j X` is what lies beyond it.  Each theorem states the exact step count.
-/

namespace BB6

theorem cons_false_blank : cons false blank = blank := by
  funext n; cases n <;> rfl

/-- After k wall bounces from a gap preceded by a stripe cell `1`, the tape reads `L (10)^k 1 0 0 E>0 0 R'`. -/
theorem wallbounces (k : Nat) (L R' : Tape) :
    steps (wallbounceSteps k 0) ⟨cons false (cons false (cons true L)), cons false (rep k [true, false] (cons false R')), .E⟩
      = some ⟨cons false (cons false (cons true (rep k [false, true] L))), cons false (cons false R'), .E⟩ := by
  have h := wallbounce_iter k 0 (cons true L) R'
  have e : 0 + k = k := by omega
  rw [e, rep_zero, rep_head k true false L] at h
  exact h

/-- Gap meets wall, and the shift finds a marker: `L (10)^(k+j) 1 0 1 0 1 0 0 E>0 0 R`. -/
theorem gap_wall_marker (k j : Nat) (L R : Tape) :
    steps (wallbounceSteps k 0 + (2 * j + 8))
        ⟨cons false (cons false (cons true L)),
         cons false (rep k [true, false] (cons false (rep j [true, false] (cons true (cons true (cons false R)))))), .E⟩
      = some ⟨cons false (cons false (cons true (cons false (cons true (cons false (cons true (rep j [false, true] (rep k [false, true] L)))))))),
              cons false R, .E⟩ :=
  steps_seq (wallbounces k L _) (meet_to_marker j (rep k [false, true] L) R)

/-- Gap meets wall, and the shift finds a wall: it becomes a block, and a packet heads left. -/
theorem gap_wall_wall (k j : Nat) (L R : Tape) :
    steps (wallbounceSteps k 0 + (6 * j + 13))
        ⟨cons false (cons false (cons true L)),
         cons false (rep k [true, false] (cons false (rep j [true, false] (cons false (cons true R))))), .E⟩
      = some ⟨rep k [false, true] L,
              cons true (cons true (rep j [true, false] (cons true (cons false (cons true (cons true (cons true R))))))), .A⟩ :=
  steps_seq (wallbounces k L _) (meet_to_wall j (rep k [false, true] L) R)

/-- Gap meets wall, and the shift finds a block: it becomes a wall two cells further right, and a packet heads left. -/
theorem gap_wall_block (k j : Nat) (L R : Tape) :
    steps (wallbounceSteps k 0 + (6 * j + 19))
        ⟨cons false (cons false (cons true L)),
         cons false (rep k [true, false] (cons false (rep j [true, false] (cons true (cons true (cons true (cons false R))))))), .E⟩
      = some ⟨rep k [false, true] L,
              cons true (cons true (rep j [true, false] (cons true (cons false (cons true (cons false (cons true (cons false (cons false R))))))))), .A⟩ :=
  steps_seq (wallbounces k L _) (meet_to_block j (rep k [false, true] L) R)

/-- Gap meets wall, and the shift reaches blank tape: an end marker forms, and a packet heads left. -/
theorem gap_wall_blank (k j : Nat) (L : Tape) :
    steps (wallbounceSteps k 0 + (6 * j + 13))
        ⟨cons false (cons false (cons true L)), cons false (rep k [true, false] (cons false (rep j [true, false] blank))), .E⟩
      = some ⟨rep k [false, true] L, cons true (cons true (rep j [true, false] (cons true (cons false (cons true (cons true blank)))))), .A⟩ :=
  steps_seq (wallbounces k L _) (meet_to_blank j (rep k [false, true] L))

/-- Gap meets wall, and the shift uses up the end marker: a new end marker forms 3 cells further right. -/
theorem gap_wall_endmarker (k j : Nat) (L : Tape) :
    steps (wallbounceSteps k 0 + (6 * j + 29))
        ⟨cons false (cons false (cons true L)),
         cons false (rep k [true, false] (cons false (rep j [true, false] (cons true (cons true blank))))), .E⟩
      = some ⟨rep k [false, true] L,
              cons true (cons true (rep j [true, false] (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons true blank)))))))))), .A⟩ :=
  steps_seq (wallbounces k L _) (meet_to_endmarker j (rep k [false, true] L))

/-- Gap with nothing to its right: k wall bounces off the blank end, then the end gains a marker 3 cells further
right and a packet heads left. -/
theorem gap_blank_end (k : Nat) (L : Tape) :
    steps (wallbounceSteps k 0 + 13) ⟨cons false (cons false (cons true L)), cons false (rep k [true, false] blank), .E⟩
      = some ⟨rep k [false, true] L, cons true (cons true (cons true (cons false (cons true (cons true blank))))), .A⟩ := by
  have h₁ := wallbounces k L blank
  rw [cons_false_blank] at h₁
  exact steps_seq h₁ (gap_to_blankend (rep k [false, true] L))

end BB6
