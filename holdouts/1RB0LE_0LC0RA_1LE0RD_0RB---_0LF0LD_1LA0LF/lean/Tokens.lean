/-! # Token rules and conserved value of the Z system

Machine: 1RB0LE_0LC0RA_1LE0RD_0RB---_0LF0LD_1LA0LF, read on the mirrored tape (see the README of this folder).

A *visit* of a state is a function on half tapes. For this machine four of them close up (found and checked
against direct simulation by `c/zvis.cpp`; that they are runs of the transition table is proved in `Link.lean`):

    A(0 S) = 1 S             A(1 S) = P(1 E(S))
    E(0 0 T) = 1 0 A(T)      E(1 0 T) = 1 0 E(T)      E(0 1 T) = P(0 F(1 T))      E(1 1 T): halt
    F(1 0 U) = 1 0 A(U)      F(1 1 U) = P(1 F(1 U))
    P(c 0 V) = 1 0 E(V)      P(c 1 V) = 0 0 V

This file takes those four equations as the definition (`BV`, half tapes are infinite: `ℕ → Bool`, blank = all 0)
and proves, in the kernel:

* `sound`: every token rule of the README (`TV`: the counter rules for `L = 1010`, `O = 000`, `I = 100`, the rules
  of the travelling defect `x = 10`, `1`, `z = 0`, and the re-readings at the blank end) is a computation of the four
  functions. No token rule uses the halting case `E(1 1 T)`.
* `conserve`: the value `v` (`v(L W) = v(W)/2`, `v(O W) = 2 v(W)`, `v(I W) = 1 + 2 v(W)`, with `F`, `G` for the defect)
  goes up by exactly 1 in every visit of A that the token rules derive, whatever the tape.
-/

namespace Z36869

/-! ## Bit level -/

abbrev Tape := Nat → Bool

def cons (b : Bool) (s : Tape) : Tape := fun i => match i with | 0 => b | i + 1 => s i

def zeros : Tape := fun _ => false

theorem zeros_eq : zeros = cons false zeros := by
  funext i; cases i <;> rfl

inductive BK | A | E | F | P

/-- The four visit functions as a relation: `BV k s r` means visit `k` on half tape `s` returns `r`. -/
inductive BV : BK → Tape → Tape → Prop
  | a0 (s) : BV .A (cons false s) (cons true s)
  | a1 {s e r} : BV .E s e → BV .P (cons true e) r → BV .A (cons true s) r
  | e00 {t a} : BV .A t a → BV .E (cons false (cons false t)) (cons true (cons false a))
  | e10 {t e} : BV .E t e → BV .E (cons true (cons false t)) (cons true (cons false e))
  | e01 {t f r} : BV .F (cons true t) f → BV .P (cons false f) r → BV .E (cons false (cons true t)) r
  | f10 {u a} : BV .A u a → BV .F (cons true (cons false u)) (cons true (cons false a))
  | f11 {u f r} : BV .F (cons true u) f → BV .P (cons true f) r → BV .F (cons true (cons true u)) r
  | p0 (c) {v e} : BV .E v e → BV .P (cons c (cons false v)) (cons true (cons false e))
  | p1 (c v) : BV .P (cons c (cons true v)) (cons false (cons false v))

/-! ## Tokens -/

/-- Words `L = 1010`, `O = 000`, `I = 100` and the defects `x = 10`, `one = 1`, `z = 0`. -/
inductive T | L | O | I | x | one | z
  deriving DecidableEq

def bits : T → List Bool
  | .L => [true, false, true, false]
  | .O => [false, false, false]
  | .I => [true, false, false]
  | .x => [true, false]
  | .one => [true]
  | .z => [false]

def pre : List Bool → Tape → Tape
  | [], s => s
  | b :: l, s => cons b (pre l s)

/-- A token list followed by blank tape. -/
def enc : List T → Tape
  | [] => zeros
  | t :: w => pre (bits t) (enc w)

inductive TK | A | Eh | E0

/-- The token rules (README, "The defect"). `Eh` is E without the `1 0` it writes first, `E0` is E after a 0. -/
inductive TV : TK → List T → List T → Prop
  -- counter rules
  | aL {w a b} : TV .A w a → TV .A a b → TV .A (.L :: w) (.L :: b)
  | aO (w) : TV .A (.O :: w) (.I :: w)
  | aI {w a} : TV .A w a → TV .A (.I :: w) (.O :: a)
  | aNil : TV .A [] [.I]
  -- defect rules for A
  | az (w) : TV .A (.z :: w) (.one :: w)
  | axO (w) : TV .A (.x :: .O :: w) (.O :: .x :: w)
  | axI {w e} : TV .Eh w e → TV .A (.x :: .I :: w) (.L :: .O :: e)
  | axL {w a b} : TV .A (.x :: w) a → TV .A a b → TV .A (.x :: .L :: w) (.L :: b)
  | a1 {w e} : TV .Eh w e → TV .A (.one :: w) (.O :: e)
  | axEnd {r} : TV .A [.I] r → TV .A [.x] r
  -- Eh
  | hL {w e} : TV .Eh w e → TV .Eh (.L :: w) (.L :: e)
  | hO (w) : TV .Eh (.O :: w) (.one :: w)
  | hI {w e} : TV .E0 w e → TV .Eh (.I :: w) e
  | hNil : TV .Eh [] [.I]
  -- E0
  | oO (w) : TV .E0 (.O :: w) (.L :: w)
  | oL {w a} : TV .A (.x :: w) a → TV .E0 (.L :: w) (.O :: a)
  | oI (w) : TV .E0 (.I :: w) (.O :: .one :: w)
  | oNil : TV .E0 [] [.L]

/-- What a token visit means on the bit level. -/
def Means : TK → List T → List T → Prop
  | .A, w, w' => BV .A (enc w) (enc w')
  | .Eh, w, w' => BV .E (enc w) (cons true (cons false (enc w')))
  | .E0, w, w' => BV .E (cons false (enc w)) (enc w')

theorem enc_x_nil : enc [.x] = enc [.I] := by
  show cons true (cons false zeros) = cons true (cons false (cons false zeros))
  simp only [← zeros_eq]

theorem enc_one_nil : enc [.one] = enc [.I] := by
  show cons true zeros = cons true (cons false (cons false zeros))
  simp only [← zeros_eq]

theorem a_blank : BV .A zeros (cons true zeros) := by
  have h := BV.a0 zeros; simp only [← zeros_eq] at h; exact h

theorem e_blank : BV .E zeros (cons true (cons false (cons true zeros))) := by
  have h := BV.e00 a_blank; simp only [← zeros_eq] at h; exact h

/-- Every token rule is a computation of the four visit functions. -/
theorem sound {k w w'} (h : TV k w w') : Means k w w' := by
  induction h with
  | aL _ _ ih1 ih2 => exact BV.a1 (BV.e01 (BV.f10 ih1) (BV.p1 _ _)) (BV.p0 _ (BV.e00 ih2))
  | aO w => exact BV.a0 _
  | aI _ ih => exact BV.a1 (BV.e00 ih) (BV.p1 _ _)
  | aNil =>
    show BV .A zeros (cons true (cons false (cons false zeros)))
    simp only [← zeros_eq]; exact a_blank
  | az w => exact BV.a0 _
  | axO w => exact BV.a1 (BV.e00 (BV.a0 _)) (BV.p1 _ _)
  | axI _ ih => exact BV.a1 (BV.e01 (BV.f10 (BV.a0 _)) (BV.p1 _ _)) (BV.p0 _ (BV.e00 (BV.a1 ih (BV.p1 _ _))))
  | axL _ _ ih1 ih2 => exact BV.a1 (BV.e01 (BV.f10 ih1) (BV.p1 _ _)) (BV.p0 _ (BV.e00 ih2))
  | a1 _ ih => exact BV.a1 ih (BV.p1 _ _)
  | axEnd _ ih => show BV .A (enc [.x]) _; rw [enc_x_nil]; exact ih
  | hL _ ih => exact BV.e10 (BV.e10 ih)
  | hO w => exact BV.e00 (BV.a0 _)
  | hI _ ih => exact BV.e10 ih
  | hNil =>
    show BV .E zeros (cons true (cons false (cons true (cons false (cons false zeros)))))
    simp only [← zeros_eq]; exact e_blank
  | oO w => exact BV.e00 (BV.a0 _)
  | oL _ ih => exact BV.e01 (BV.f10 ih) (BV.p1 _ _)
  | oI w => exact BV.e01 (BV.f10 (BV.a0 _)) (BV.p1 _ _)
  | oNil =>
    show BV .E (cons false zeros) (cons true (cons false (cons true (cons false zeros))))
    simp only [← zeros_eq]; exact e_blank

/-! ## The conserved value -/

mutual
/-- Value of a token tape: a digit counts `2^-b`, b = (number of L) - (number of digits) before it. -/
def v : List T → Rat
  | [] => 0
  | .L :: w => v w / 2
  | .O :: w => 2 * v w
  | .I :: w => 1 + 2 * v w
  | .x :: w => F w
  | .one :: w => G w
  | .z :: w => G w - 1
/-- Value of `x W`. -/
def F : List T → Rat
  | [] => 1
  | .O :: w => 2 * F w - 1
  | .L :: w => F w / 2
  | .I :: w => (G w - 1) / 2
  | _ :: _ => 0
/-- Value of `1 W`. -/
def G : List T → Rat
  | [] => 1
  | .O :: w => 2 * G w - 1
  | .L :: w => (G w - 1) / 2
  | [.I] => -1
  | .I :: .O :: w => v w - 1
  | .I :: .I :: w => 4 * G w - 1
  | .I :: .L :: w => 4 * F w + 3
  | _ :: _ => 0
end

/-- What each token visit does to the value: A adds 1; `Eh W` and `E0 W` have fixed values. -/
def Gain : TK → List T → List T → Prop
  | .A, w, w' => v w' = v w + 1
  | .Eh, w, w' => v w' = (G w + 1) / 2
  | .E0, w, w' => v w' = (G (.I :: w) + 1) / 2

/-- Every visit of A derived by the token rules adds exactly 1 to the value, on any token tape. -/
theorem conserve {k w w'} (h : TV k w w') : Gain k w w' := by
  induction h <;> simp only [Gain, v, F, G] at * <;> grind

/-- The round of the machine, `S' = 1 0 A(S)` = `x :: A(S)`, on token tapes. -/
theorem round_value {s a} (h : TV .A s a) : v (.x :: a) = F a ∧ v a = v s + 1 :=
  ⟨rfl, conserve h⟩

end Z36869
