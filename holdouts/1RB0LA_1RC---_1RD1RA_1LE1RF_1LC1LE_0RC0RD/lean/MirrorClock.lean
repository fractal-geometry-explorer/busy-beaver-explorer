import MirrorRules

/-!
# The clock of 1LB0RA_1LC---_1LD1LA_1RE1LF_1RC1RE_0LC0LD, the mirror image of 1RB0LA_1RC---_1RD1RA_1LE1RF_1LC1LE_0RC0RD

Written by `holdouts/1RB0LA_1RC---_1RD1RA_1LE1RF_1LC1LE_0RC0RD/py/counter.py lean`.

`J j W` is the tape `1^(5+4j) 0 W` right of the head, the head in state D on its first cell.  At every visit of the
left end in state F the tape is `F>0 1^(5+4j) 0 W`, one step after `D> J j W` one cell to the right.

A *P-step* `PStep W W' e` is one excursion of the head into the word: `L 1 E> W` reaches `L F> 1 W'` in `e` steps,
for every left tape `L` (the head stays in the word until it comes back).  `PChain m W W' E`: `m` P-steps in a row.

The block is a binary counter: digits `1000` (one) and `0000` (zero), least significant next to the word.
`cnt j`: from `Lc (0000)^j 1 1 1 1 E> W` the head makes 2^j excursions, adding one to the counter between two, and
comes back from the last one with the counter full, `Lc (1000)^j 1 1 1 F> 1 W'`, in `E + IC j` steps (induction on
`j`: the low `j` digits count through twice, with one increment `rule_inc` of the digit above in between).

**Theorem `tick`.**  For every `j`, if `W` reaches `W'` by `2^j` P-steps of total cost `E`, then

    L 0 0 0 0 D> 1^(5+4j) 0 W   reaches   L D> 1^(9+4j) 0 W'   in exactly  E + 51·2^j − 4  steps,

for every `L`: the sweep (`rule_sweep`), the counter (`cnt`), the finish (`rule_fin`).  So the block grows by 4
per tick while the word goes through `2^j` applications of one map P.
-/

namespace H44966M

open TM

/-- `1^(5+4j) 0 W`, read from the head. -/
def J (j : Nat) (W : Tape) : Tape :=
  cons true (cons true (cons true (cons true (cons true (rep j [true, true, true, true] (cons false W))))))

/-- One excursion into the word: `L 1 E> W` reaches `L F> 1 W'` in `e` steps, for every `L`. -/
def PStep (W W' : Tape) (e : Nat) : Prop :=
  ∀ L : Tape, steps e ⟨cons true L, W, .E⟩ = some ⟨L, cons true W', .F⟩

/-- `m` P-steps in a row, of total cost `E`. -/
inductive PChain : Nat → Tape → Tape → Nat → Prop
  | zero (W : Tape) : PChain 0 W W 0
  | succ {m : Nat} {W W1 W2 : Tape} {e E : Nat} : PStep W W1 e → PChain m W1 W2 E → PChain (m + 1) W W2 (e + E)

theorem PChain.split : ∀ (x y : Nat) {W W2 : Tape} {E : Nat}, PChain (x + y) W W2 E →
    ∃ W1 E1 E2, PChain x W W1 E1 ∧ PChain y W1 W2 E2 ∧ E = E1 + E2 := by
  intro x
  induction x with
  | zero => intro y W W2 E h; exact ⟨W, 0, E, .zero W, by simpa using h, by omega⟩
  | succ x ih =>
    intro y W W2 E h
    rw [show x + 1 + y = (x + y) + 1 by omega] at h
    cases h with
    | succ hs hc =>
      obtain ⟨W1, E1, E2, h1, h2, he⟩ := ih y hc
      exact ⟨W1, _ + E1, E2, .succ hs h1, h2, by omega⟩

/-- The steps of the increments of a count through `j` digits. -/
def IC : Nat → Nat
  | 0 => 0
  | j + 1 => 2 * IC j + (18 * j + 33)

theorem IC_eq (j : Nat) : IC j + 18 * j + 51 = 51 * 2 ^ j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [IC]
    rw [Nat.pow_succ]
    omega

theorem z4_cons (n : Nat) (X : Tape) :
    rep n [false, false, false, false] (cons false X) = cons false (rep n [false, false, false, false] X) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rep_succ, ih]; rfl

theorem o4_cons (n : Nat) (X : Tape) :
    rep n [true, true, true, true] (cons true X) = cons true (rep n [true, true, true, true] X) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rep_succ, ih]; rfl

/-- The statement of the counter through `j` digits. -/
def Cnt (j : Nat) : Prop :=
  ∀ (W W' : Tape) (E : Nat), PChain (2 ^ j) W W' E → ∀ Lc : Tape,
    steps (E + IC j) ⟨cons true (cons true (cons true (cons true (rep j [false, false, false, false] Lc)))), W, .E⟩ =
      some ⟨cons true (cons true (cons true (rep j [false, false, false, true] Lc))), cons true W', .F⟩

/-- **The counter**: 2^j excursions, with the increments in between, for every left context `Lc`. -/
theorem cnt (j : Nat) : Cnt j := by
  induction j with
  | zero =>
    intro W W' E h Lc
    cases h with
    | succ hs hz =>
      cases hz
      exact hs (cons true (cons true (cons true Lc)))
  | succ j ih =>
    intro W W' E h Lc
    rw [show 2 ^ (j + 1) = 2 ^ j + 2 ^ j by rw [Nat.pow_succ]; omega] at h
    obtain ⟨W1, E1, E2, h1, h2, he⟩ := PChain.split _ _ h
    -- the low j digits count through, below a 0 digit
    have s1 := ih W W1 E1 h1 (cons false (cons false (cons false (cons false Lc))))
    -- the increment that sets the digit j
    have s2 := rule_inc j Lc W1
    rw [← z4_cons] at s2
    -- the low j digits count through again, below a 1 digit
    have s3 := ih W1 W' E2 h2 (cons false (cons false (cons false (cons true Lc))))
    have := steps_seq trans s1 (steps_seq trans s2 s3)
    have e1 : rep j [false, false, false, false] (cons false (cons false (cons false (cons false Lc)))) =
        rep (j + 1) [false, false, false, false] Lc := rep_app_comm j _ Lc
    have e2 : rep j [false, false, false, true] (cons false (cons false (cons false (cons true Lc)))) =
        rep (j + 1) [false, false, false, true] Lc := rep_app_comm j _ Lc
    rw [e1, e2] at this
    refine steps_congr trans ?_ this
    simp only [IC]
    omega

/-- The statement of tick `j`. -/
def Tick (j : Nat) : Prop :=
  ∀ (W W' : Tape) (E : Nat), PChain (2 ^ j) W W' E → ∀ L : Tape,
    steps (E + 51 * 2 ^ j - 4) ⟨cons false (cons false (cons false (cons false L))), J j W, .D⟩ =
      some ⟨L, J (j + 1) W', .D⟩

/-- **The tick**, for every level `j`: `L 0^4 D> 1^(5+4j) 0 W` reaches `L D> 1^(9+4j) 0 W'` in
`E + 51·2^j − 4` steps whenever `2^j` P-steps of total cost `E` take `W` to `W'`. -/
theorem tick (j : Nat) : Tick j := by
  intro W W' E h L
  have s0 := rule_sweep j L W
  have s1 := cnt j W W' E h (cons false (cons false (cons false (cons true (cons true (cons false L))))))
  have s2 := rule_fin j L W'
  rw [o4_cons] at s2
  have e3 : cons true (cons true (cons true (cons true (cons true (cons true (cons true (cons true (cons true
      (rep j [true, true, true, true] (cons false W')))))))))) = J (j + 1) W' := by
    unfold J; rw [rep_succ]; rfl
  rw [e3] at s2
  have := steps_seq trans s0 (steps_seq trans s1 s2)
  refine steps_congr trans ?_ this
  have q := IC_eq j
  have p5 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  generalize 2 ^ j = q at *
  omega

/-- The tick at the left end of the tape (blank to the left); the visits of the left end in state F are one step
after these configurations. -/
theorem tick_left_end (j : Nat) (W W' : Tape) (E : Nat) (h : PChain (2 ^ j) W W' E) :
    steps (E + 51 * 2 ^ j - 4) ⟨blank, J j W, .D⟩ = some ⟨blank, J (j + 1) W', .D⟩ := by
  have := tick j W W' E h blank
  rwa [cons_false_blank, cons_false_blank, cons_false_blank, cons_false_blank] at this

end H44966M
