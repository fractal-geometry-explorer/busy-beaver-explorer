import Macro

/-!
# 1RB0RF_0LC1RE_---1LD_1LE0LB_0RF0LD_1RD1RA: the common start of the even branch

For even e = 2i + 4 the run from `C e` first packs the 01-run into 0111 words (`even_pack`) and then *halves*
it: each 0111 on the left becomes one 10 on each side of a marker `1100` (`half0`, `half1`, `half`, by induction
`halving`).  Proved here: `C (2i+4)` reaches

    Y i = 0^∞ E> 1 1 0 (10)^i 1 1 0 0 (10)^(i+4) 0^∞

(`even_start`).  What follows depends on the parity of i (the next pass packs the 10s in pairs), which is where the
cases e ≡ 0 (mod 4) and e ≡ 2 (mod 4) part; those continuations are not proved.
-/

namespace H55875

open TM

/-- `1 1 0 (10)^u 1 1 0 0 (10)^(u+4) 0^∞`, the tape right of the head during the halving. -/
def Y (u : Nat) : Tape :=
  cons true (cons true (cons false (rep u [true, false] (cons true (cons true (cons false (cons false
    (rep (u + 4) [true, false] blank))))))))

/-- One halving round: `L 0111 E> Y u` reaches `L E> Y (u+1)`. -/
theorem half_Y (u : Nat) (L : Tape) : ∃ t,
    steps t ⟨cons false (cons true (cons true (cons true L))), Y u, .E⟩ = some ⟨L, Y (u + 1), .E⟩ := by
  cases u with
  | zero => exact ⟨_, half1 L⟩
  | succ v =>
    have h := half v L
    rw [← rot10] at h
    exact ⟨_, h⟩

/-- `a` halving rounds. -/
theorem halving (a : Nat) : ∀ (u : Nat) (L : Tape), ∃ t,
    steps t ⟨rep a [false, true, true, true] L, Y u, .E⟩ = some ⟨L, Y (u + a), .E⟩ := by
  induction a with
  | zero => intro u L; exact ⟨0, rfl⟩
  | succ a ih =>
    intro u L
    obtain ⟨t1, h1⟩ := half_Y u (rep a [false, true, true, true] L)
    obtain ⟨t2, h2⟩ := ih (u + 1) L
    rw [show u + 1 + a = u + (a + 1) by omega] at h2
    exact ⟨_, steps_seq trans h1 h2⟩

/-- **The even branch, first part**: `C (2i+4)` reaches `0^∞ E> Y i`. -/
theorem even_start (i : Nat) : ∃ t, steps t (C (2 * i + 4)) = some ⟨blank, Y i, .E⟩ := by
  have h1 := enter (2 * i + 4)
  have e1 : cons true (cons false (cons true (cons false (rep (2 * i + 4) [true, false] (cons true blank))))) =
      cons true (rep (i + 2) [false, true, false, true] (cons false (cons true (cons false (cons true blank))))) := by
    rw [rot10, show cons false (cons true (cons false (cons true blank))) = app [false, true, false, true] blank
      from rfl, rep_app_comm, rep_ftft, show 2 * (i + 2 + 1) = (2 * i + 4) + 2 by omega]
    rfl
  rw [e1, cons_false_blank] at h1
  have h2 := even_pack (i + 1)
  have h3 := half0 (rep i [false, true, true, true] blank)
  obtain ⟨t4, h4⟩ := halving i 0 blank
  rw [Nat.zero_add] at h4
  exact ⟨_, steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 h4))⟩

end H55875
