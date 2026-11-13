import Rules

/-!
# The rounds on block lengths, and the map

A *round start* is the tape `1^x1 0 1^x2 0 ... 0 1^xk` with blank tape on both sides and the head in state A on the
blank cell left of it (`K [x1, ..., xk]`).  `Rules.lean` proves, for all values of the variables, how the machine
goes from one round start to a later one; here they are restated on blocks (`Blk`: `ev n` is `1^(2n)`, `od n` is
`1^(2n+1)`), composed, and iterated:

* `loopN`: three blocks `(f, m, z)` with `f` even and `m` odd become `(f - 2t, m - 2t, z + 6t)`;
* `phase`: the loop runs until the first block is 2 or the middle one is 1, then the three blocks become two
  (or the machine halts);
* `round`: two blocks `(a, c)` (`a` even) go to two blocks `next a c` (`mapc`), or the machine halts.

The theorems are about every value of the counts; Lean's kernel checks them (no `native_decide`).
-/

namespace H35366

open TM

/-- A block of ones, by parity: `ev n` is `1^(2n)`, `od n` is `1^(2n+1)`. -/
inductive Blk where
  | ev (n : Nat)
  | od (n : Nat)

/-- The block in front of a tape. -/
def Blk.tape : Blk → Tape → Tape
  | .ev n, s => rep n [true, true] s
  | .od n, s => cons true (rep n [true, true] s)

/-- The length of the block. -/
def Blk.len : Blk → Nat
  | .ev n => 2 * n
  | .od n => 2 * n + 1

/-- `k` more pairs of ones. -/
def Blk.add : Blk → Nat → Blk
  | .ev n, k => .ev (n + k)
  | .od n, k => .od (n + k)

/-- Nine more ones. -/
def Blk.nine : Blk → Blk
  | .ev n => .od (n + 4)
  | .od n => .ev (n + 5)

theorem Blk.add_add (Z : Blk) (a b : Nat) : (Z.add a).add b = Z.add (a + b) := by
  cases Z <;> simp [Blk.add, Nat.add_assoc]

theorem Blk.add_zero (Z : Blk) : Z.add 0 = Z := by
  cases Z <;> rfl

/-- The blocks, separated by single 0s, then blank tape. -/
def enc : List Blk → Tape
  | [] => blank
  | [b] => b.tape blank
  | b :: b' :: bs => b.tape (cons false (enc (b' :: bs)))

/-- A round start. -/
def K (bs : List Blk) : Config := ⟨blank, cons false (enc bs), .A⟩

/-! ## The main loop -/

theorem loop1 (x y : Nat) (Z : Blk) :
    ∃ n, steps n (K [.ev (x + 2), .od (y + 1), Z]) = some (K [.ev (x + 1), .od y, Z.add 3]) := by
  cases Z with
  | ev z =>
    cases x with
    | zero => cases y with
      | zero => exact ⟨_, loop43_e z⟩
      | succ y => exact ⟨_, loop4_e y z⟩
    | succ x => cases y with
      | zero => exact ⟨_, loop3_e x z⟩
      | succ y => exact ⟨_, loop_e x y z⟩
  | od z =>
    cases x with
    | zero => cases y with
      | zero => exact ⟨_, loop43_o z⟩
      | succ y => exact ⟨_, loop4_o y z⟩
    | succ x => cases y with
      | zero => exact ⟨_, loop3_o x z⟩
      | succ y => exact ⟨_, loop_o x y z⟩

/-- `t` rounds of the main loop. -/
theorem loopN (t x y : Nat) (Z : Blk) :
    ∃ n, steps n (K [.ev (x + t + 1), .od (y + t), Z]) = some (K [.ev (x + 1), .od y, Z.add (3 * t)]) := by
  induction t generalizing Z with
  | zero => exact ⟨0, by rw [Blk.add_zero]; rfl⟩
  | succ t ih =>
    obtain ⟨n₁, h₁⟩ := loop1 (x + t) (y + t) Z
    obtain ⟨n₂, h₂⟩ := ih (Z.add 3)
    rw [Blk.add_add, show 3 + 3 * t = 3 * (t + 1) by omega] at h₂
    exact ⟨n₁ + n₂, steps_seq trans h₁ h₂⟩

/-! ## The end of the loop -/

/-- The middle block is down to 1 and the first is at least 6: it merges into the last block. -/
theorem end1 (x : Nat) (Z : Blk) :
    ∃ n, steps n (K [.ev (x + 3), .od 0, Z]) = some (K [.ev (x + 2), Z.nine]) := by
  cases Z with
  | ev z => cases x with
    | zero => exact ⟨_, end1_six_e z⟩
    | succ x => exact ⟨_, end1_e x z⟩
  | od z => cases x with
    | zero => exact ⟨_, end1_six_o z⟩
    | succ x => exact ⟨_, end1_o x z⟩

/-- The first block is down to 2: the middle block becomes the first. -/
theorem end2 (y : Nat) (Z : Blk) :
    ∃ n, steps n (K [.ev 1, .od (y + 1), Z]) = some (K [.ev (y + 2), Z.add 3]) := by
  cases Z with
  | ev z => cases y with
    | zero => exact ⟨_, end2_three_e z⟩
    | succ y => exact ⟨_, end2_e y z⟩
  | od z => cases y with
    | zero => exact ⟨_, end2_three_o z⟩
    | succ y => exact ⟨_, end2_o y z⟩

/-- The middle block is down to 1 and the first is 2 or 4: the machine halts. -/
theorem end_halt (x : Nat) (hx : x < 2) (Z : Blk) :
    ∃ n c, steps n (K [.ev (x + 1), .od 0, Z]) = some c ∧ step c = none := by
  have hx' : x = 0 ∨ x = 1 := by omega
  rcases hx' with rfl | rfl
  · cases Z with
    | ev z => exact ⟨_, _, halt2_e z, rfl⟩
    | od z => exact ⟨_, _, halt2_o z, rfl⟩
  · cases Z with
    | ev z => exact ⟨_, _, halt4_e z, rfl⟩
    | od z => exact ⟨_, _, halt4_o z, rfl⟩

/-! ## A whole phase: `(2F, 2M + 1, Z)` to two blocks -/

theorem phase_lt (F M : Nat) (h : M + 3 ≤ F) (Z : Blk) :
    ∃ n, steps n (K [.ev F, .od M, Z]) = some (K [.ev (F - M - 1), (Z.add (3 * M)).nine]) := by
  obtain ⟨n₁, h₁⟩ := loopN M (F - M - 1) 0 Z
  obtain ⟨n₂, h₂⟩ := end1 (F - M - 3) (Z.add (3 * M))
  rw [show F - M - 1 + M + 1 = F by omega, Nat.zero_add] at h₁
  rw [show F - M - 3 + 3 = F - M - 1 + 1 by omega, show F - M - 3 + 2 = F - M - 1 by omega] at h₂
  exact ⟨n₁ + n₂, steps_seq trans h₁ h₂⟩

theorem phase_halt (F M : Nat) (h₁ : M + 1 ≤ F) (h₂ : F ≤ M + 2) (Z : Blk) :
    ∃ n c, steps n (K [.ev F, .od M, Z]) = some c ∧ step c = none := by
  obtain ⟨n₁, h₁'⟩ := loopN M (F - M - 1) 0 Z
  obtain ⟨n₂, c, h₂', hc⟩ := end_halt (F - M - 1) (by omega) (Z.add (3 * M))
  rw [show F - M - 1 + M + 1 = F by omega, Nat.zero_add] at h₁'
  exact ⟨n₁ + n₂, c, steps_seq trans h₁' h₂', hc⟩

theorem phase_ge (F M : Nat) (h₁ : 1 ≤ F) (h₂ : F ≤ M) (Z : Blk) :
    ∃ n, steps n (K [.ev F, .od M, Z]) = some (K [.ev (M + 2 - F), Z.add (3 * F)]) := by
  obtain ⟨n₁, h₁'⟩ := loopN (F - 1) 0 (M - F + 1) Z
  obtain ⟨n₂, h₂'⟩ := end2 (M - F) (Z.add (3 * (F - 1)))
  rw [Nat.zero_add, show F - 1 + 1 = F by omega, show M - F + 1 + (F - 1) = M by omega] at h₁'
  rw [Blk.add_add, show 3 * (F - 1) + 3 = 3 * F by omega, show M - F + 2 = M + 2 - F by omega] at h₂'
  exact ⟨n₁ + n₂, steps_seq trans h₁' h₂'⟩

/-! ## The start of a round of two blocks -/

/-- Two even blocks `(2x + 6, 2y + 18)`: four rounds split off and shrink a block `9`, the fifth merges it,
leaving `(2x + 4, 2y + 3, 33)`. -/
theorem start_even (x y : Nat) :
    ∃ n, 0 < n ∧ steps n (K [.ev (x + 3), .ev (y + 9)]) = some (K [.ev (x + 2), .od (y + 1), .od 16]) := by
  have h0 : steps _ (K [.ev (x + 3), .ev (y + 9)]) = some (K [.ev (x + 3), .ev (y + 7), .od 4]) := e0 x (y + 5)
  have h1 : steps _ (K [.ev (x + 3), .ev (y + 7), .od 4]) = some (K [.ev (x + 3), .ev (y + 6), .od 3, .ev 3]) :=
    e9 x (y + 5)
  have h2 : steps _ (K [.ev (x + 3), .ev (y + 6), .od 3, .ev 3]) = some (K [.ev (x + 3), .ev (y + 5), .od 2, .ev 6]) :=
    e7 x (y + 4) 3
  have h3 : steps _ (K [.ev (x + 3), .ev (y + 5), .od 2, .ev 6]) = some (K [.ev (x + 3), .ev (y + 4), .od 1, .ev 9]) :=
    e5 x (y + 3) 6
  have h4 : steps _ (K [.ev (x + 3), .ev (y + 4), .od 1, .ev 9]) = some (K [.ev (x + 3), .ev (y + 3), .od 0, .ev 12]) :=
    e3 x (y + 2) 9
  have h5 : steps _ (K [.ev (x + 3), .ev (y + 3), .od 0, .ev 12]) = some (K [.ev (x + 2), .od (y + 1), .od 16]) :=
    e1 x y 12
  exact ⟨_, by omega, steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3
    (steps_seq trans h4 h5))))⟩

/-- An even block and an odd one `(2x + 6, 2y + 5)`: `(2x + 4, 2y + 3, 6)`. -/
theorem start_odd (x y : Nat) :
    ∃ n, 0 < n ∧ steps n (K [.ev (x + 3), .od (y + 2)]) = some (K [.ev (x + 2), .od (y + 1), .ev 3]) :=
  ⟨_, by omega, o0 x y⟩

/-- The same with a first block of 4. -/
theorem start_odd_four (y : Nat) :
    ∃ n, 0 < n ∧ steps n (K [.ev 2, .od (y + 2)]) = some (K [.ev 1, .od (y + 1), .ev 3]) :=
  ⟨_, by omega, o0_four y⟩

end H35366
