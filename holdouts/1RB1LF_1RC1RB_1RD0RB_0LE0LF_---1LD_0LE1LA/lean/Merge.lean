import Rules

/-!
# 1RB1LF_1RC1RB_1RD0RB_0LE0LF_---1LD_0LE1LA: a merge, iterated, and the halt it ends in when the left block is short

A merge is the zigzag of `zig` (`Rules.lean`) run until one of the two blocks of pairs `01` next to the growing block of
ones is used up.  `zig_iter`: `j` zigzags take `j` pairs from each side and add `4j` ones.  `left_merge_halts`: at the
left end of the tape (`0^∞ 1 1 1 (01)^a`), if the block on the right has at least `a + 2` pairs, the machine halts.
So the run from blank tape halts if a merge at the left end ever meets a right block that is not shorter than the left
one by at least 2 (in the run so far the left block is always about three times longer, see the README).
-/

namespace H60424

open TM

/-- The tape around a merge: `L (01)^a A> 0 1 (11)^n 0 (01)^k R` (the left tape is written nearest cell first). -/
def mcfg (a n k : Nat) (L R : Tape) : Config :=
  ⟨rep a [true, false] L, cons false (cons true (rep n [true, true] (cons false (rep k [false, true] R)))), .A⟩

theorem ones_shift (n : Nat) (X : Tape) :
    cons true (cons true (cons true (cons true (rep n [true, true] (cons true X))))) =
      cons true (rep (n + 2) [true, true] X) := by
  have h : rep n [true, true] (cons true X) = cons true (rep n [true, true] X) :=
    (rep_rotate n [true] [true, true] [true, true] rfl X).symm
  rw [h]; rfl

/-- One zigzag in the `mcfg` form. -/
theorem zig' (a n k : Nat) (L R : Tape) :
    steps (4 * n + 10) (mcfg (a + 1) n (k + 1) L R) = some (mcfg a (n + 2) k L R) := by
  have h := zig a k n L R
  unfold mcfg
  rw [h, ones_shift]

/-- `j` zigzags. -/
theorem zig_iter (j : Nat) : ∀ a n k L R, ∃ t, steps t (mcfg (a + j) n (k + j) L R) = some (mcfg a (n + 2 * j) k L R) := by
  induction j with
  | zero => intro a n k L R; exact ⟨0, by simp⟩
  | succ j ih =>
    intro a n k L R
    obtain ⟨t, ht⟩ := ih a (n + 2) k L R
    have e1 : a + (j + 1) = (a + j) + 1 := by omega
    have e2 : k + (j + 1) = (k + j) + 1 := by omega
    have e3 : n + 2 + 2 * j = n + 2 * (j + 1) := by omega
    refine ⟨4 * n + 10 + t, ?_⟩
    rw [e1, e2]
    rw [e3] at ht
    exact steps_seq trans (zig' (a + j) n (k + j) L R) ht

/-- A merge at the left end with a left block of `a` pairs and a right block of `a + k + 2` pairs halts. -/
theorem left_merge_halts (a n k : Nat) (R : Tape) :
    TM.Halts trans (mcfg a n (a + k + 2) (cons true (cons true (cons true blank))) R) := by
  obtain ⟨t, ht⟩ := zig_iter a 0 n (k + 2) (cons true (cons true (cons true blank))) R
  have e : (0 + a) = a := by omega
  have e2 : k + 2 + a = a + k + 2 := by omega
  rw [e, e2] at ht
  have hz := zig_halt k (n + 2 * a) R
  have hz' : steps (8 * (n + 2 * a) + 34) (mcfg 0 (n + 2 * a) (k + 2) (cons true (cons true (cons true blank))) R) =
      some ⟨blank, cons false (cons false (cons true (cons true (cons true (cons true (cons true (cons true (cons true
        (cons true (rep (n + 2 * a) [true, true] (cons true (cons true (cons false (rep k [false, true] R)))))))))))))),
        .E⟩ := by
    unfold mcfg; simpa using hz
  exact ⟨_, _, steps_seq trans ht hz', rfl⟩

end H60424
