import Rules

/-!
# 1RB0RF_1RC1RF_1LD0LE_---1LC_1RA1LE_1LC1RB: the odd pass

`P n` is the configuration `0^inf 1^n B> 0^inf`: the tape is one block of `n` ones and the head, in state B, stands
on the blank cell just right of it.  From blank tape the machine reaches `P 4` after 9 steps, and the whole run is a
sequence of such configurations.  Here: for odd `n = 2k + 3`, `P n` leads to `P (3k + 7)`, i.e. `n ↦ (3n + 5)/2`.
(The even case is the halving bouncer described in the README; it is checked by simulation, not here.)
-/

namespace H144815

open TM

/-- `c` reaches `c'` in some number of steps. -/
def Reaches (c c' : Config) : Prop := ∃ n, steps n c = some c'

theorem Reaches.trans {a b c : Config} (h₁ : Reaches a b) (h₂ : Reaches b c) : Reaches a c := by
  obtain ⟨n, hn⟩ := h₁
  obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, steps_seq H144815.trans hn hm⟩

/-- `0^inf 1^n B> 0^inf`. -/
def P (n : Nat) : Config := ⟨rep n [true] blank, blank, .B⟩

/-- `0^inf 1^a 0 (11)^b 1 1 C> 0^inf`: the right-hand zigzag with `b` rounds to go. -/
def Cz (b a : Nat) : Config :=
  ⟨cons true (cons true (rep b [true, true] (cons false (rep a [true] blank)))), blank, .C⟩

theorem rep_one_two (k : Nat) (s : Tape) : rep (2 * k) [true] s = rep k [true, true] s := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega]
    simp only [rep_succ, ih, app]

theorem blank_P4 : steps 9 init = some (P 4) := rfl

theorem c_rounds (b : Nat) : ∀ a, Reaches (Cz b a) (Cz 0 (a + 3 * b)) := by
  induction b with
  | zero => intro a; exact ⟨0, rfl⟩
  | succ b ih =>
    intro a
    have h := c_round a b
    have e1 : Cz (b + 1) a = ⟨cons true (cons true (cons true (cons true (rep b [true, true]
        (cons false (rep a [true] blank)))))), blank, .C⟩ := rfl
    have e2 : Cz b (a + 3) = ⟨cons true (cons true (rep b [true, true] (cons false (cons true (cons true
        (cons true (rep a [true] blank))))))), blank, .C⟩ := rfl
    have h' : Reaches (Cz (b + 1) a) (Cz b (a + 3)) := ⟨_, by rw [e1, e2]; exact h⟩
    have := ih (a + 3)
    rw [show a + 3 + 3 * b = a + 3 * (b + 1) by omega] at this
    exact h'.trans this

/-- The odd pass: `P (2k+3)` reaches `P (3k+7)`, that is `n ↦ (3n+5)/2` on odd `n ≥ 3`. -/
theorem odd_pass (k : Nat) : Reaches (P (2 * k + 3)) (P (3 * k + 7)) := by
  have e0 : P (2 * k + 3) = ⟨rep (k + 1) [true, true] (cons true blank), blank, .B⟩ := by
    simp only [P, show 2 * k + 3 = 2 * (k + 1) + 1 by omega, rep_add, rep_one_two]; rfl
  have h1 : Reaches (P (2 * k + 3)) (Cz k 3) := ⟨_, by rw [e0]; exact odd_start k⟩
  have h3 : Reaches (Cz 0 (3 + 3 * k)) (P (3 * k + 7)) := by
    refine ⟨7, ?_⟩
    have e : P (3 * k + 7) = ⟨cons true (cons true (cons true (cons true (rep (3 + 3 * k) [true] blank)))),
        blank, .B⟩ := by
      simp only [P, show 3 * k + 7 = (3 + 3 * k) + 1 + 1 + 1 + 1 by omega, rep_succ, app]
    rw [e]
    exact c_end (3 + 3 * k)
  exact (h1.trans (c_rounds k 3)).trans h3

end H144815
