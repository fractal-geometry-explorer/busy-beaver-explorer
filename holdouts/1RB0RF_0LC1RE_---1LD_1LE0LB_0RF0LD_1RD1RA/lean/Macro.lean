import Rules

/-!
# 1RB0RF_0LC1RE_---1LD_1LE0LB_0RF0LD_1RD1RA: the odd branch of the phase map

Hand-written; the rules it uses (`enter`, `pack`, `round`, `finish`) are proved in `Rules.lean`.

`C e` is the configuration `0^∞ 1 E> 0 (01)^e 0^∞`, and `P a b` is `0^∞ 111 (0111)^a 01 E> 0 (01)^b 0^∞`.
For odd `e = 2i + 1`: `C e → P i 2` (enter, then pack), `P (a+1) b → P a (b+3)` (round), `P 0 b → C (b+3)`
(finish), so `C (2i+1) → C (3i+5)`, that is `e ↦ (3e + 7)/2`. Even `e` takes another route, not covered here.
-/

namespace H55875

open TM

/-- `0^∞ 1 E> 0 (01)^e 0^∞`. -/
def C (e : Nat) : Config := ⟨cons true blank, cons false (rep e [false, true] blank), .E⟩

/-- `0^∞ 111 (0111)^a 01 E> 0 (01)^b 0^∞`. -/
def P (a b : Nat) : Config :=
  ⟨cons true (cons false (rep a [true, true, true, false] (cons true (cons true (cons true blank))))),
    cons false (rep b [false, true] blank), .E⟩

theorem rot10 (b : Nat) (R : Tape) : rep b [true, false] (cons true R) = cons true (rep b [false, true] R) :=
  (rep_rotate b [true] [false, true] [true, false] rfl R).symm

theorem rot111 (i : Nat) (R : Tape) :
    cons true (cons true (cons true (rep i [false, true, true, true] R))) =
      rep i [true, true, true, false] (cons true (cons true (cons true R))) :=
  rep_rotate i [true, true, true] [false, true, true, true] [true, true, true, false] rfl R

theorem tail3 (b : Nat) (R : Tape) :
    cons false (cons false (cons true (cons false (cons true (cons false (rep b [true, false] (cons true R))))))) =
      cons false (rep (b + 3) [false, true] R) := by
  rw [rot10]; rfl

theorem rep_ftft (i : Nat) (R : Tape) : rep i [false, true, false, true] R = rep (2 * i) [false, true] R := by
  induction i with
  | zero => rfl
  | succ i ih => rw [show 2 * (i + 1) = 2 * i + 1 + 1 by omega, rep_succ, ih]; rfl

theorem round_P (a b : Nat) : steps (6 * b + 10) (P (a + 1) b) = some (P a (b + 3)) := by
  have h := round b (rep a [true, true, true, false] (cons true (cons true (cons true blank))))
  rw [tail3] at h
  exact h

theorem rounds (a : Nat) : ∀ b, ∃ n, steps n (P a b) = some (P 0 (b + 3 * a)) := by
  induction a with
  | zero => intro b; exact ⟨0, rfl⟩
  | succ a ih =>
    intro b
    obtain ⟨n, hn⟩ := ih (b + 3)
    rw [show b + 3 + 3 * a = b + 3 * (a + 1) by omega] at hn
    exact ⟨_, steps_seq trans (round_P a b) hn⟩

theorem finish_P (b : Nat) : steps (6 * b + 10) (P 0 b) = some (C (b + 3)) := by
  have h := finish b
  rw [tail3] at h
  exact h

theorem enter_pack (i : Nat) : ∃ n, steps n (C (2 * i + 1)) = some (P i 2) := by
  have h1 := enter (2 * i + 1)
  have h2 := pack i
  have e1 : cons true (cons false (cons true (cons false (rep (2 * i + 1) [true, false] (cons true blank))))) =
      cons true (rep i [false, true, false, true] (cons false (cons true (cons false (cons true
        (cons false (cons true blank))))))) := by
    rw [rot10, rep_ftft, show (cons false (cons true (cons false (cons true (cons false (cons true blank)))))) =
      rep 3 [false, true] blank from rfl, ← rep_add]
    rfl
  rw [e1, cons_false_blank] at h1
  rw [rot111] at h2
  exact ⟨_, steps_seq trans h1 h2⟩

/-- The odd branch: `C (2i+1) → C (3i+5)`, i.e. `e ↦ (3e+7)/2` for odd `e`. -/
theorem odd_step (i : Nat) : ∃ n, steps n (C (2 * i + 1)) = some (C (3 * i + 5)) := by
  obtain ⟨n1, h1⟩ := enter_pack i
  obtain ⟨n2, h2⟩ := rounds i 2
  rw [show 2 + 3 * i = 3 * i + 2 by omega] at h2
  have h3 := finish_P (3 * i + 2)
  exact ⟨_, steps_seq trans (steps_seq trans h1 h2) h3⟩

end H55875
