import Rules

/-!
# 1RB1LC_1LA---_1LD0LA_1RE0LE_0RF1RE_1LB1RD: a phase of rounds, by induction

`cfg P q L` is the right end of the tape `L 1 0 1^P 0 (1010)^q 1^5 E> 0^inf`, that is (P, Q) with Q = 2q.  One round
(`round` of `Rules.lean`) takes two ones from the block of P ones and adds two words `10`; `rounds` chains k of them.
-/

namespace H147121

open TM

/-- `L 1 0 1^P 0 (1010)^q 1^5 E> 0^inf` -/
def cfg (P q : Nat) (L : Tape) : Config :=
  ⟨rep 5 [true] (rep q [false, true, false, true] (cons false (rep P [true] (cons false (cons true L))))), blank, .E⟩

theorem round' (p q : Nat) (L : Tape) : steps (28 * q + 64) (cfg (p + 7) (q + 1) L) = some (cfg (p + 5) (q + 2) L) := by
  have h := round p q L
  exact h

/-- k rounds: (P + 2k, Q) -> (P, Q + 2k), for P >= 5 and even Q >= 2. -/
theorem rounds (k : Nat) : ∀ p q L, ∃ n, steps n (cfg (p + 5 + 2 * k) (q + 1) L) = some (cfg (p + 5) (q + 1 + k) L) := by
  induction k with
  | zero => intro p q L; exact ⟨0, rfl⟩
  | succ k ih =>
    intro p q L
    obtain ⟨n, hn⟩ := ih p (q + 1) L
    have e1 : p + 5 + 2 * (k + 1) = (p + 2 * k) + 7 := by omega
    have e2 : (p + 2 * k) + 5 = p + 5 + 2 * k := by omega
    have e3 : q + 1 + 1 + k = q + 1 + (k + 1) := by omega
    rw [e3] at hn
    rw [e1]
    have h1 := round' (p + 2 * k) q L
    rw [e2] at h1
    exact ⟨_, steps_seq trans h1 hn⟩

end H147121
