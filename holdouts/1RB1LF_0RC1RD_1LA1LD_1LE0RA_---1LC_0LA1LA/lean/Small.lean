import Rounds

/-!
# Rounds with short blocks

`Rounds.lean` covers two-block round starts `(a, c)` with `a ≥ 6` and an even `c ≥ 18` (or an odd `c ≥ 5`).  Here
are the remaining even cases: a right block `c` of 6 to 16 and a first block of 4.  With them the map `mapc` needs
no `.small` case on the round starts the orbit can reach (`a` even, `a ≥ 4`, `c ≥ 6`).  The rules are generated in
`Rules.lean` (`e0_three` ... `e1_two_four`, `halt4_one`).
-/

namespace H35366

open TM

theorem rot1 (n : Nat) (s : Tape) : cons true (rep n [true, true] s) = rep n [true, true] (cons true s) :=
  rep_rotate n [true] [true, true] [true, true] rfl s

theorem absorb2 (n : Nat) (s : Tape) : rep n [true, true] (cons true (cons true s)) = rep (n + 1) [true, true] s :=
  rep_app_comm n [true, true] s

theorem steps_eq {n : Nat} {c c' d d' : Config} (h : steps n c = some d) (e₁ : c' = c) (e : d = d') :
    steps n c' = some d' := by
  rw [e₁, h, e]

/-- Normal form of a configuration made of blocks of ones. -/
macro "tnorm" : tactic => `(tactic| (simp only [K, enc, Blk.tape, rep_add, rep_succ, app_cons, app_nil, rep_zero, rot1]))

/-- Chaining reachability with a positive step count. -/
theorem seqP {a b c : Config} (h₁ : ∃ n, 0 < n ∧ steps n a = some b) (h₂ : ∃ n, steps n b = some c) :
    ∃ n, 0 < n ∧ steps n a = some c := by
  obtain ⟨n₁, hn, h₁⟩ := h₁; obtain ⟨n₂, h₂⟩ := h₂
  exact ⟨n₁ + n₂, by omega, steps_seq trans h₁ h₂⟩

theorem seqE {a b c : Config} (h₁ : ∃ n, steps n a = some b) (h₂ : ∃ n, steps n b = some c) :
    ∃ n, steps n a = some c := by
  obtain ⟨n₁, h₁⟩ := h₁; obtain ⟨n₂, h₂⟩ := h₂
  exact ⟨n₁ + n₂, steps_seq trans h₁ h₂⟩

theorem posE {n : Nat} {a b : Config} (hn : 0 < n) (h : steps n a = some b) : ∃ n, 0 < n ∧ steps n a = some b :=
  ⟨n, hn, h⟩

/-! ## A first block of at least 6 (`x + 3` pairs) -/

/-- `(2x + 6, 6)` goes to `(2x + 12, 12)`. -/
theorem sm3 (x : Nat) : ∃ n, 0 < n ∧ steps n (K [.ev (x + 3), .ev 3]) = some (K [.ev (x + 6), .ev 6]) :=
  seqP (posE (by omega) (steps_eq (e0_three x) (by tnorm) (by tnorm) : steps _ _ = some (K [.ev (x + 3), .ev 1, .od 4])))
    ⟨_, steps_eq (e9_one x) (by tnorm) (by tnorm)⟩

/-- The first rounds of an even right block of at least 8: a block `9` is split off and shrunk. -/
theorem sm_pre (x y : Nat) : ∃ n, 0 < n ∧ steps n (K [.ev (x + 3), .ev (y + 4)]) =
    some (K [.ev (x + 3), .ev (y + 1), .od 3, .ev 3]) :=
  seqP (posE (by omega) (steps_eq (e0 x y) (by tnorm) (by tnorm) : steps _ _ = some (K [.ev (x + 3), .ev (y + 2), .od 4])))
    ⟨_, steps_eq (e9 x y) (by tnorm) (by tnorm)⟩

theorem sm4 (x : Nat) : ∃ n, 0 < n ∧ steps n (K [.ev (x + 3), .ev 4]) = some (K [.ev (x + 5), .ev 9]) :=
  seqP (sm_pre x 0) ⟨_, steps_eq (e7_one x 3) (by tnorm) (by tnorm)⟩

theorem sm5 (x : Nat) : ∃ n, 0 < n ∧ steps n (K [.ev (x + 3), .ev 5]) = some (K [.ev (x + 4), .ev 12]) :=
  seqP (seqP (sm_pre x 1)
    ⟨_, (steps_eq (e7 x 0 3) (by tnorm) (by tnorm) : steps _ _ = some (K [.ev (x + 3), .ev 1, .od 2, .ev 6]))⟩)
    ⟨_, steps_eq (e5_one x 6) (by tnorm) (by tnorm)⟩

theorem sm6_pre (x y : Nat) : ∃ n, 0 < n ∧ steps n (K [.ev (x + 3), .ev (y + 6)]) =
    some (K [.ev (x + 3), .ev (y + 1), .od 1, .ev 9]) :=
  seqP (seqP (sm_pre x (y + 2))
    ⟨_, (steps_eq (e7 x (y + 1) 3) (by tnorm) (by tnorm) : steps _ _ = some (K [.ev (x + 3), .ev (y + 2), .od 2, .ev 6]))⟩)
    ⟨_, steps_eq (e5 x y 6) (by tnorm) (by tnorm)⟩

theorem sm6 (x : Nat) : ∃ n, 0 < n ∧ steps n (K [.ev (x + 3), .ev 6]) = some (K [.ev (x + 3), .ev 15]) :=
  seqP (sm6_pre x 0) ⟨_, steps_eq (e3_one x 9) (by tnorm) (by tnorm)⟩

theorem sm7_pre (x y : Nat) : ∃ n, 0 < n ∧ steps n (K [.ev (x + 3), .ev (y + 7)]) =
    some (K [.ev (x + 3), .ev (y + 1), .od 0, .ev 12]) :=
  seqP (sm6_pre x (y + 1)) ⟨_, steps_eq (e3 x y 9) (by tnorm) (by tnorm)⟩

theorem sm7 (x : Nat) : ∃ n, 0 < n ∧ steps n (K [.ev (x + 4), .ev 7]) = some (K [.ev (x + 3), .ev 18]) :=
  seqP (sm7_pre (x + 1) 0) ⟨_, steps_eq (e1_one x 12) (by tnorm) (by tnorm)⟩

theorem sm7_six : ∃ n, 0 < n ∧ steps n (K [.ev 3, .ev 7]) = some (K [.ev 2, .ev 18]) :=
  seqP (sm7_pre 0 0) ⟨_, steps_eq (e1_one_six 12) (by tnorm) (by tnorm)⟩

theorem sm8 (x : Nat) : ∃ n, 0 < n ∧ steps n (K [.ev (x + 3), .ev 8]) = some (K [.ev (x + 2), .od 0, .od 16]) :=
  seqP (sm7_pre x 1) ⟨_, steps_eq (e1_two x 12) (by tnorm) (by tnorm)⟩

/-! ## A first block of 4 -/

theorem f3 : ∃ n, 0 < n ∧ steps n (K [.ev 2, .ev 3]) = some (K [.ev 5, .ev 6]) :=
  seqP (posE (by omega) (steps_eq e0_three_four (by tnorm) (by tnorm) : steps _ _ = some (K [.ev 2, .ev 1, .od 4])))
    ⟨_, steps_eq e9_one_four (by tnorm) (by tnorm)⟩

theorem f_pre (y : Nat) : ∃ n, 0 < n ∧ steps n (K [.ev 2, .ev (y + 4)]) = some (K [.ev 2, .ev (y + 1), .od 3, .ev 3]) :=
  seqP (posE (by omega) (steps_eq (e0_four y) (by tnorm) (by tnorm) : steps _ _ = some (K [.ev 2, .ev (y + 2), .od 4])))
    ⟨_, steps_eq (e9_four y) (by tnorm) (by tnorm)⟩

theorem f4 : ∃ n, 0 < n ∧ steps n (K [.ev 2, .ev 4]) = some (K [.ev 4, .ev 9]) :=
  seqP (f_pre 0) ⟨_, steps_eq (e7_one_four 3) (by tnorm) (by tnorm)⟩

theorem f5 : ∃ n, 0 < n ∧ steps n (K [.ev 2, .ev 5]) = some (K [.ev 3, .ev 12]) :=
  seqP (seqP (f_pre 1) ⟨_, (steps_eq (e7_four 0 3) (by tnorm) (by tnorm) : steps _ _ = some (K [.ev 2, .ev 1, .od 2, .ev 6]))⟩)
    ⟨_, steps_eq (e5_one_four 6) (by tnorm) (by tnorm)⟩

theorem f6_pre (y : Nat) : ∃ n, 0 < n ∧ steps n (K [.ev 2, .ev (y + 6)]) = some (K [.ev 2, .ev (y + 1), .od 1, .ev 9]) :=
  seqP (seqP (f_pre (y + 2))
    ⟨_, (steps_eq (e7_four (y + 1) 3) (by tnorm) (by tnorm) : steps _ _ = some (K [.ev 2, .ev (y + 2), .od 2, .ev 6]))⟩)
    ⟨_, steps_eq (e5_four y 6) (by tnorm) (by tnorm)⟩

theorem f6 : ∃ n, 0 < n ∧ steps n (K [.ev 2, .ev 6]) = some (K [.ev 2, .ev 15]) :=
  seqP (f6_pre 0) ⟨_, steps_eq (e3_one_four 9) (by tnorm) (by tnorm)⟩

theorem f7_pre (y : Nat) : ∃ n, 0 < n ∧ steps n (K [.ev 2, .ev (y + 7)]) = some (K [.ev 2, .ev (y + 1), .od 0, .ev 12]) :=
  seqP (f6_pre (y + 1)) ⟨_, steps_eq (e3_four y 9) (by tnorm) (by tnorm)⟩

theorem f7_halt : ∃ n c, steps n (K [.ev 2, .ev 7]) = some c ∧ step c = none := by
  obtain ⟨n₁, -, h₁⟩ := f7_pre 0
  exact ⟨_, _, steps_seq trans h₁ (steps_eq (halt4_one 12) (by tnorm) rfl), rfl⟩

theorem f8 : ∃ n, 0 < n ∧ steps n (K [.ev 2, .ev 8]) = some (K [.ev 1, .od 0, .od 16]) :=
  seqP (f7_pre 1) ⟨_, steps_eq (e1_two_four 12) (by tnorm) (by tnorm)⟩

theorem f9 (y : Nat) : ∃ n, 0 < n ∧ steps n (K [.ev 2, .ev (y + 9)]) = some (K [.ev 1, .od (y + 1), .od 16]) :=
  seqP (f7_pre (y + 2)) ⟨_, steps_eq (e1_four y 12) (by tnorm) (by tnorm)⟩

end H35366

namespace H35366

open TM

/-- Two even blocks `(2P, 2Q)`, `P ≥ 2`, `Q ≥ 8`: the start of the round, as `start_even` but for every such pair. -/
theorem start_even_all (P Q : Nat) (hP : 2 ≤ P) (hQ : 8 ≤ Q) :
    ∃ n, 0 < n ∧ steps n (K [.ev P, .ev Q]) = some (K [.ev (P - 1), .od (Q - 8), .od 16]) := by
  obtain ⟨y, rfl⟩ : ∃ y, Q = y + 8 := ⟨Q - 8, by omega⟩
  rw [show y + 8 - 8 = y by omega]
  by_cases h2 : P = 2
  · subst h2
    cases y with
    | zero => exact f8
    | succ y => rw [show y + 1 + 8 = y + 9 by omega]; exact f9 y
  · obtain ⟨x, rfl⟩ : ∃ x, P = x + 3 := ⟨P - 3, by omega⟩
    rw [show x + 3 - 1 = x + 2 by omega]
    cases y with
    | zero => exact sm8 x
    | succ y =>
      obtain ⟨n, hn, h⟩ := start_even x y
      rw [show y + 1 + 8 = y + 9 by omega]
      exact ⟨n, hn, h⟩

/-- Two even blocks with a right block of 6 to 14 go straight to the next round start (or halt: `(4, 14)`). -/
theorem short_even (P Q : Nat) (hP : 2 ≤ P) (hQ : 3 ≤ Q) (hQ' : Q ≤ 7) (hh : ¬ (P = 2 ∧ Q = 7)) :
    ∃ n, 0 < n ∧ steps n (K [.ev P, .ev Q]) = some (K [.ev (P + 6 - Q), .ev (3 * Q - 3)]) := by
  have hQ'' : Q = 3 ∨ Q = 4 ∨ Q = 5 ∨ Q = 6 ∨ Q = 7 := by omega
  by_cases h2 : P = 2
  · subst h2
    rcases hQ'' with rfl | rfl | rfl | rfl | rfl
    · exact f3
    · exact f4
    · exact f5
    · exact f6
    · exact absurd ⟨rfl, rfl⟩ hh
  · obtain ⟨x, rfl⟩ : ∃ x, P = x + 3 := ⟨P - 3, by omega⟩
    rcases hQ'' with rfl | rfl | rfl | rfl | rfl
    · rw [show x + 3 + 6 - 3 = x + 6 by omega]; exact sm3 x
    · rw [show x + 3 + 6 - 4 = x + 5 by omega]; exact sm4 x
    · rw [show x + 3 + 6 - 5 = x + 4 by omega]; exact sm5 x
    · rw [show x + 3 + 6 - 6 = x + 3 by omega]; exact sm6 x
    · cases x with
      | zero => exact sm7_six
      | succ x =>
        rw [show x + 1 + 3 + 6 - 7 = x + 3 by omega, show x + 1 + 3 = x + 4 by omega]; exact sm7 x

theorem short_even_halt : ∃ n c, steps n (K [.ev 2, .ev 7]) = some c ∧ step c = none := f7_halt

end H35366
