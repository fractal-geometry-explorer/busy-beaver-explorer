import Top
import Level2Leaves

/-!
# The second level of 1RB0RE_1LC0RA_1RF0RD_---1LE_0LB1LE_1LE1RC: an inner reset inside an outer block of pairs

When the doubling rounds of a top-level reset run out, the leftover 1s stay on the left and the rest of the tape is an
**outer block** of pairs `(10)^C`, with a new bouncer to its right. Its empty tanks are

* `Kc C y L` = `L (10)^C 0 (10)^y 1 B>`              (an inner empty tank, B on the blank cell right of the tape)

and an inner reset runs **inner rounds** through

* `Gc C u k c L` = `L (10)^C 1^u 0 A> 0 (10)^k 1^c`   (blank tape on the right).

Proved here, for all parameters and every tape `L` on the left (leaf rules from `Level2Leaves.lean`):

* `g_entry`: `Kc (C+2) y → Gc C 0 0 (2y+7)`: the tank becomes 2y+7 ones and two outer pairs are used;
* `g_step`: `Gc C (u+2) k (c+3) → Gc C u (k+2) (c+1)`; `g_end`: `Gc (C+1) 0 k (c+5) → Gc C (2k+6) 0 (c+1)`: one inner
  round uses one outer pair and doubles its block, k → 2k+6 (6, 18, 42, 90, ...);
* `g_term`: `Gc (C+1) u k 1 → Pc u (k+1)`: the rounds run out with a single 1 on the right and a new inner bouncer
  starts, whose sweeps (`p_sweeps`) bring it to the next empty tank `Kc (C+1) (k+1+u)`;
* **`inner_reset`**: `innerMap C y = some (C', y')` → `Kc C y L` reaches `Kc C' y' L`: the inner reset map, as a Lean
  function. It is `none` only when the outer block is too short (an outer event) or a round starts with exactly
  three 1s on the right (`Gc _ 0 _ 3`, a case with further nesting, not covered here).
* `top_end`: the end of a top-level reset, `1^p B> 1 0 (10)^(i+2) 1 1` on blank tape, reaches the first inner tank
  `Kc i 7 (1^p 0)`: this is how the second level starts.
-/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace H127123

open TM

/-- `L (10)^C 0 (10)^y 1 B>`, an inner empty tank. -/
def Kc (C y : Nat) (L : Tape) : Config := ⟨cons true (rep y [false, true] (cons false (rep C [false, true] L))), blank, .B⟩
/-- `L (10)^C 1^u 0 A> 0 (10)^k 1^c`, inside an inner round (blank tape on the right). -/
def Gc (C u k c : Nat) (L : Tape) : Config :=
  ⟨cons false (rep u [true] (rep C [false, true] L)), cons false (rep k [true, false] (rep c [true] blank)), .A⟩
/-- The context of the inner bouncer: `L (10)^C 1`. -/
def Oc (C : Nat) (L : Tape) : Tape := cons true (rep C [false, true] L)

theorem odd_ones (y : Nat) (X : Tape) :
    cons true (cons true (cons true (cons true (cons true (cons true (rep y [true, true] (cons true X)))))))
      = rep (2 * y + 7) [true] X := by
  rw [n_pair, n_1cons]; rfl

theorem g_entry (C y : Nat) (L : Tape) : Reaches (Kc (C + 2) y L) (Gc C 0 0 (2 * y + 7) L) := by
  have h := l2_entry y (rep C [false, true] L)
  rw [odd_ones] at h
  exact Reaches.of h

theorem g_step (C u k c : Nat) (L : Tape) : Reaches (Gc C (u + 2) k (c + 3) L) (Gc C u (k + 2) (c + 1) L) := by
  have h := l2_step k (rep u [true] (rep C [false, true] L)) (rep c [true] blank)
  rw [j_mid] at h
  exact Reaches.of h

theorem g_end (C k c : Nat) (L : Tape) : Reaches (Gc (C + 1) 0 k (c + 5) L) (Gc C (2 * k + 6) 0 (c + 1) L) := by
  have h := l2_end k (rep C [false, true] L) (rep c [true] blank)
  have e : cons true (cons true (rep k [true, true] (cons true (cons true (cons true (cons true
      (rep C [false, true] L))))))) = rep (2 * k + 6) [true] (rep C [false, true] L) := by
    rw [n_pair]
    show rep 2 [true] (rep (2 * k) [true] (rep 4 [true] _)) = _
    rw [← rep_add, ← rep_add, show 2 + 2 * k + 4 = 2 * k + 6 by omega]
  rw [e] at h
  exact Reaches.of h

theorem g_term (C u k : Nat) (L : Tape) : Reaches (Gc (C + 1) u k 1 L) (Pc u (k + 1) (Oc C L)) := by
  have h := l2_term k (rep u [true] (rep (C + 1) [false, true] L))
  exact Reaches.of h

theorem pc_zero (C y : Nat) (L : Tape) : Pc 0 y (Oc C L) = Kc (C + 1) y L := rfl

/-! ## The inner rounds and the inner reset map -/

/-- The inner rounds from `Gc C u k c`: the next inner empty tank `(C', y')`, or `none` where no rule here applies. -/
def run2 : Nat → Nat → Nat → Nat → Option (Nat × Nat)
  | C + 1, u, k, 1 => if u % 2 = 0 then some (C + 1, k + 1 + u) else none
  | C, u + 2, k, c + 3 => run2 C u (k + 2) (c + 1)
  | C + 1, 0, k, c + 5 => run2 C (2 * k + 6) 0 (c + 1)
  | _, _, _, _ => none

/-- **The inner reset map**: the next inner empty tank after `Kc C y`. -/
def innerMap : Nat → Nat → Option (Nat × Nat)
  | C + 2, y => run2 C 0 0 (2 * y + 7)
  | _, _ => none

theorem run2_sem (L : Tape) : ∀ C u k c C' y', run2 C u k c = some (C', y') → Reaches (Gc C u k c L) (Kc C' y' L)
  | C + 1, u, k, 1, C', y', h => by
    simp only [run2] at h
    split at h
    · next hu =>
      cases h
      obtain ⟨b, rfl⟩ : ∃ b, u = 2 * b := ⟨u / 2, by omega⟩
      have h2 := p_sweeps b (Oc C L) 0 (k + 1)
      rw [Nat.zero_add, pc_zero] at h2
      exact (g_term C (2 * b) k L).tr (by rw [show k + 1 + 2 * b = k + 1 + 2 * b from rfl]; exact h2)
    · cases h
  | C, u + 2, k, c + 3, C', y', h => by
    have h' : run2 C u (k + 2) (c + 1) = some (C', y') := by
      cases C <;> (simp only [run2] at h ⊢; exact h)
    exact (g_step C u k c L).tr (run2_sem L C u (k + 2) (c + 1) C' y' h')
  | C + 1, 0, k, c + 5, C', y', h => by
    have h' : run2 C (2 * k + 6) 0 (c + 1) = some (C', y') := by simpa only [run2] using h
    exact (g_end C k c L).tr (run2_sem L C (2 * k + 6) 0 (c + 1) C' y' h')
  | 0, 0, _, _, _, _, h => by simp [run2] at h
  | _ + 1, 0, _, 0, _, _, h => by simp [run2] at h
  | _ + 1, 0, _, 2, _, _, h => by simp [run2] at h
  | _ + 1, 0, _, 3, _, _, h => by simp [run2] at h
  | _ + 1, 0, _, 4, _, _, h => by simp [run2] at h
  | 0, 1, _, _, _, _, h => by simp [run2] at h
  | _ + 1, 1, _, 0, _, _, h => by simp [run2] at h
  | _ + 1, 1, _, 2, _, _, h => by simp [run2] at h
  | _ + 1, 1, _, _ + 3, _, _, h => by simp [run2] at h
  | 0, _ + 2, _, 0, _, _, h => by simp [run2] at h
  | 0, _ + 2, _, 1, _, _, h => by simp [run2] at h
  | 0, _ + 2, _, 2, _, _, h => by simp [run2] at h
  | _ + 1, _ + 2, _, 0, _, _, h => by simp [run2] at h
  | _ + 1, _ + 2, _, 2, _, _, h => by simp [run2] at h

/-- **The inner reset, for all parameters and any tape on the left**: `Kc C y L` reaches `Kc C' y' L` whenever
`innerMap C y = some (C', y')`. -/
theorem inner_reset (L : Tape) (C y C' y' : Nat) (h : innerMap C y = some (C', y')) : Reaches (Kc C y L) (Kc C' y' L) := by
  match C, h with
  | C + 2, h => exact (g_entry C y L).tr (run2_sem L C 0 0 (2 * y + 7) C' y' h)

/-! ## How the second level starts -/

/-- The end of a top-level round with 1s left on the left: `1^(p+1) B> 1 0 (10)^(i+2) 1 1` on blank tape reaches the
inner empty tank `1^(p+1) 0 (10)^i 0 (10)^7 1 B>`. -/
theorem top_end (p i : Nat) : Reaches (Jc (p + 1) (i + 2) 2 blank) (Kc i 7 (cons false (rep (p + 1) [true] blank))) :=
  Reaches.of (l2_start i (rep p [true] blank))

/-- **The end of a top-level reset.** A doubling round `Dc m c` on blank tape with too few 1s for a full round
(`c = 2j + 6`, `m = q + j + 1`) leaves `2q + 1` ones on the left as the outer stock and starts the second level at
the inner tank `Kc (2j) 7`, the outer block being `(10)^(2j)`. -/
theorem round_end (q j : Nat) :
    Reaches (Dc (q + j + 1) (2 * j + 6) blank) (Kc (2 * j) 7 (cons false (rep (2 * q + 1) [true] blank))) := by
  have h1 := d_start (q + j + 1) (2 * j + 2) blank
  rw [show 2 * j + 2 + 4 = 2 * j + 6 by omega, show 2 * (q + j + 1) + 1 = 2 * q + 1 + 2 * (j + 1) by omega,
    show 2 * j + 2 + 2 = 0 + 2 + 2 * (j + 1) by omega] at h1
  have h2 := j_iter (j + 1) blank (2 * q + 1) 0 0
  rw [show 0 + 2 * (j + 1) = 2 * j + 2 by omega] at h2
  exact (Reaches.of h1).tr (h2.tr (top_end (2 * q) (2 * j)))

/-! ## The two top-level tanks of the run

The run from blank tape empties its top-level tank at `y = 8187` and at `y = 16379` (README). From each, Lean
follows the whole reset: the doubling rounds, the end of the rounds, and four inner resets, up to the point where the
next inner reset would use up the outer block (`innerMap` is `none` there: an outer event, not covered here). -/

theorem inner4 (L : Tape) (C0 y0 C1 y1 C2 y2 C3 y3 C4 y4 : Nat) (h1 : innerMap C0 y0 = some (C1, y1))
    (h2 : innerMap C1 y1 = some (C2, y2)) (h3 : innerMap C2 y2 = some (C3, y3)) (h4 : innerMap C3 y3 = some (C4, y4)) :
    Reaches (Kc C0 y0 L) (Kc C4 y4 L) :=
  (inner_reset L _ _ _ _ h1).tr ((inner_reset L _ _ _ _ h2).tr ((inner_reset L _ _ _ _ h3).tr (inner_reset L _ _ _ _ h4)))

/-- From the tank `1 0 (10)^16379 1 B>` (blank tape on the left): 12 doubling rounds, the outer stock `1^32737`,
the outer block `(10)^24`, and inner tanks `y = 7, 19, 43, 91, 187` with outer blocks `24, 20, 15, 9, 2`. -/
theorem tank_16379 : Reaches (Pc 1 16379 blank) (Kc 2 187 (cons false (rep 32737 [true] blank))) := by
  have h1 := reset_rounds 12 16377 28 (by decide)
  rw [show rM 12 1 = 16368 + 12 + 1 by decide, show 28 + 2 = 2 * 12 + 6 by rfl] at h1
  have h2 := round_end 16368 12
  exact h1.tr (h2.tr (inner4 _ 24 7 20 19 15 43 9 91 2 187 (by decide) (by decide) (by decide) (by decide)))

/-- From the tank `1 0 (10)^8187 1 B>`: 11 rounds, the outer stock `1^16355`, inner tanks `y = 7, 19, 43, 91` with
outer blocks `22, 18, 13, 7`. (The next inner reset uses up the outer block; `innerMap 7 91 = none`.) -/
theorem tank_8187 : Reaches (Pc 1 8187 blank) (Kc 7 91 (cons false (rep 16355 [true] blank))) := by
  have h1 := reset_rounds 11 8185 26 (by decide)
  rw [show rM 11 1 = 8177 + 11 + 1 by decide, show 26 + 2 = 2 * 11 + 6 by rfl] at h1
  have h2 := round_end 8177 11
  exact h1.tr (h2.tr ((inner_reset _ 22 7 18 19 (by decide)).tr ((inner_reset _ 18 19 13 43 (by decide)).tr
    (inner_reset _ 13 43 7 91 (by decide)))))

end H127123
