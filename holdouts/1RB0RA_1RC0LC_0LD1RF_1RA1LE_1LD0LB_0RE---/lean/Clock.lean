import Rules

/-!
# The clock of 1RB0RA_1RC0LC_0LD1RF_1RA1LE_1LD0LB_0RE---

`J j W` is the tape `1^(3+2j) 0 W` right of the head; the head is in state D on its first cell.  At every visit
of the left end in state E the tape is `E>0 1^(3+2j) 0 W`, one step after `D> J j W` one cell to the right.

A *P-step* `PStep W W' e` is one excursion of the head into the word: `L 0^3 1 B> W` reaches `L D> 1^3 0 W'`
in `e` steps, for every left tape `L`.  `PChain m W W' E`: `m` P-steps in a row, of total cost `E`.

**Theorem `tick`.**  For every level `j`, if `W` reaches `W'` by `2^j` P-steps of total cost `E`, then

    L 0 0 D> 1^(3+2j) 0 W   reaches   L D> 1^(3+2j+2) 0 W'   in exactly  E + 12·2^j − 2  steps,

for every `L`.  The tick is the sweep (`rule_sweep`: the block becomes 0s), one P-step, the ticks `0, ..., j−1`
(each eats two of the 0s the sweep left), and the merge (`rule_merge`).  Proved by strong induction on `j`; the word
`W` is arbitrary.  So the block grows by 2 per tick while the word goes through `2^j` applications of one map P.
-/

namespace H180313

open TM

/-- `1^(3+2j) 0 W`, read from the head. -/
def J (j : Nat) (W : Tape) : Tape := cons true (rep (2 * j) [true] (cons true (cons true (cons false W))))

/-- One excursion into the word: `L 0^3 1 B> W` reaches `L D> 1^3 0 W'` in `e` steps, for every `L`. -/
def PStep (W W' : Tape) (e : Nat) : Prop :=
  ∀ L : Tape, steps e ⟨cons true (cons false (cons false (cons false (L)))), W, .B⟩ = some ⟨L, J 0 W', .D⟩

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

theorem zeros_cons (n : Nat) (Y : Tape) : rep n [false] (cons false Y) = cons false (rep n [false] Y) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rep_succ, ih]; rfl

/-- The statement of tick `j`. -/
def Tick (j : Nat) : Prop :=
  ∀ (W W' : Tape) (E : Nat), PChain (2 ^ j) W W' E → ∀ L : Tape,
    steps (E + 12 * 2 ^ j - 2) ⟨cons false (cons false L), J j W, .D⟩ = some ⟨L, J (j + 1) W', .D⟩

/-- The number of P-steps of ticks `a, ..., a+m−1` (`2^(a+m) − 2^a`). -/
def NP : Nat → Nat → Nat
  | _, 0 => 0
  | a, m + 1 => 2 ^ a + NP (a + 1) m

/-- Their structural step count (`12·(2^(a+m) − 2^a) − 2m`). -/
def CS : Nat → Nat → Nat
  | _, 0 => 0
  | a, m + 1 => (12 * 2 ^ a - 2) + CS (a + 1) m

theorem NP_eq (m : Nat) : ∀ a, NP a m + 2 ^ a = 2 ^ (a + m) := by
  induction m with
  | zero => intro a; simp [NP]
  | succ m ih =>
    intro a
    have h := ih (a + 1)
    have p : 2 ^ (a + 1) = 2 * 2 ^ a := by rw [Nat.pow_succ]; omega
    simp only [NP]
    rw [show a + (m + 1) = a + 1 + m by omega, ← h]
    omega

theorem CS_eq (m : Nat) : ∀ a, CS a m + 2 * m + 12 * 2 ^ a = 12 * 2 ^ (a + m) := by
  induction m with
  | zero => intro a; simp [CS]
  | succ m ih =>
    intro a
    have h := ih (a + 1)
    have p : 2 ^ (a + 1) = 2 * 2 ^ a := by rw [Nat.pow_succ]; omega
    have p5 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
    simp only [CS]
    rw [show a + (m + 1) = a + 1 + m by omega, ← h]
    omega

/-- Ticks `a, ..., a+m−1` in a row eat `2m` zeros: `L 0^(2m) D> J a W` reaches `L D> J (a+m) W'`. -/
theorem chain (m : Nat) : ∀ (a : Nat), (∀ i, a ≤ i → i < a + m → Tick i) →
    ∀ (W W' : Tape) (E : Nat), PChain (NP a m) W W' E → ∀ L : Tape,
    steps (E + CS a m) ⟨rep (2 * m) [false] L, J a W, .D⟩ = some ⟨L, J (a + m) W', .D⟩ := by
  induction m with
  | zero =>
    intro a _ W W' E h L
    simp only [NP] at h
    cases h
    rfl
  | succ m ih =>
    intro a hT W W' E h L
    simp only [NP] at h
    obtain ⟨W1, E1, E2, h1, h2, he⟩ := PChain.split _ _ h
    have z : rep (2 * (m + 1)) [false] L = cons false (cons false (rep (2 * m) [false] L)) := by
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega]; rfl
    rw [z]
    have s1 := hT a (by omega) (by omega) W W1 E1 h1 (rep (2 * m) [false] L)
    have s2 := ih (a + 1) (fun i h1 h2 => hT i (by omega) (by omega)) W1 W' E2 h2 L
    rw [show a + 1 + m = a + (m + 1) by omega] at s2
    have := steps_seq trans s1 s2
    refine steps_congr trans ?_ this
    simp only [CS]
    have p5 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
    generalize 2 ^ a = q at *
    omega

/-- **The tick**, for every level `j`: `L 0 0 D> 1^(3+2j) 0 W` reaches `L D> 1^(3+2j+2) 0 W'` in
`E + 12·2^j − 2` steps whenever `2^j` P-steps of total cost `E` take `W` to `W'`. -/
theorem tick (j : Nat) : Tick j := by
  induction j using Nat.strongRecOn with
  | _ j ih =>
    intro W W' E h L
    have hn := NP_eq j 0
    have hc := CS_eq j 0
    simp only [Nat.pow_zero, Nat.zero_add] at hn hc
    rw [show 2 ^ j = 1 + NP 0 j by omega] at h
    obtain ⟨W1, E1, E2, h1, h2, he⟩ := PChain.split _ _ h
    cases h1 with
    | succ hs hz =>
      cases hz
      -- the sweep
      have s0 := rule_sweep j L W
      -- the P-step
      have s1 := hs (rep (2 * j) [false] (cons false (cons true L)))
      -- ticks 0 .. j-1
      have s2 := chain j 0 (fun i _ h2 => ih i (by omega)) W1 W' E2 h2 (cons false (cons true L))
      simp only [zeros_cons] at s0 s1 s2
      -- the merge
      have s3 := rule_merge L (rep (2 * (0 + j)) [true] (cons true (cons true (cons false W'))))
      have e3 : cons true (cons true (cons true (rep (2 * (0 + j)) [true] (cons true (cons true (cons false W')))))) = J (j + 1) W' := by
        unfold J; rw [show 2 * (j + 1) = 2 * (0 + j) + 1 + 1 by omega]; rfl
      rw [e3] at s3
      have := steps_seq trans s0 (steps_seq trans s1 (steps_seq trans s2 s3))
      refine steps_congr trans ?_ this
      have p5 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
      generalize 2 ^ j = q at *
      omega

/-- The tick at the left end of the tape (blank to the left); the visits of the left end in state E are one step
after these configurations. -/
theorem tick_left_end (j : Nat) (W W' : Tape) (E : Nat) (h : PChain (2 ^ j) W W' E) :
    steps (E + 12 * 2 ^ j - 2) ⟨blank, J j W, .D⟩ = some ⟨blank, J (j + 1) W', .D⟩ := by
  have := tick j W W' E h blank
  rwa [cons_false_blank, cons_false_blank] at this

end H180313
