import Machine

/-!
# 1RB0RE_1RC0RC_1LD---_0LB1LE_1RF0LD_1RA1RF simulates 1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF, slowed down

This machine (bbchallenge id 121862, "M" below) against its twin (id 75625, "T").  States A, E, F are the same in
both, and M's D is T's C on a 1.  They differ in how a leftward run over 1s is made:

* T: C reads 0, writes 1, and D walks left over the 1s, one step a cell, to the first 0, which it makes a 1.
* M: D reads 0, leaves it, and B carries that 0 left: three steps (B, C, D) move the hole one cell.  At the first 0
  the hole is filled.  During the walk M's tape is T's tape with a 0 in the cell right of the head.

`Sim` is that relation (four shapes), and `sim_step` says: one step of T is matched by one or three steps of M, and
`Sim` holds again, unless T is in state B with something other than `0 0` in front of it (`Break`).  B is the one
state the two machines use differently with no way to pair it up:

* T `B> 1` halts.  M does not: it writes 0 and goes on (`break_one`).
* T `B> 0 1` goes on.  M halts one step later, at `C> 1` (`break_zero_one`).
* On `B> 0 0` both make the same three steps.

So the halting transitions do **not** correspond: T halts on `A> 0 1`, M on `A> 0 0 1` or `A> 0 1 1`.

Proved here, with no assumption: from blank tape, after `n` steps of T there is a number `m` of steps of M,
`n <= m <= 3n`, with the two configurations in `Sim`, up to the first break (`sim_or_break`).  If a break never
happens, neither machine halts (`not_halts_of_noBreak`); if either halts, there was a break (`break_of_halts`).

Not proved: that the two halt or run on together.  "T never stands in B with a 1 in the two cells ahead" is the
statement that both run forever, the open question for both.  In 2·10^9 steps of T, it is in B 38 times, each time
at the right end of the written tape.
-/

namespace H121862

open TM

/-! The twin, 1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF (bbchallenge id 75625), with the table of its own folder's
`Machine.lean` (`H75625.trans`). -/

namespace Twin

inductive St where
  | A | B | C | D | E | F
  deriving DecidableEq, Repr

def trans : St → Bool → Option (Bool × Dir × St)
  | .A, false => some (true, .R, .B)
  | .A, true => some (false, .R, .E)
  | .B, false => some (false, .R, .C)
  | .B, true => none
  | .C, false => some (true, .L, .D)
  | .C, true => some (true, .L, .E)
  | .D, false => some (true, .L, .E)
  | .D, true => some (true, .L, .D)
  | .E, false => some (true, .R, .F)
  | .E, true => some (false, .L, .C)
  | .F, false => some (true, .R, .A)
  | .F, true => some (true, .R, .F)

def text : String := "1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF"

abbrev Config := TM.Cfg St
abbrev step := TM.step trans
abbrev steps := TM.steps trans
abbrev init : Config := TM.blankCfg .A
abbrev HaltsFromBlank : Prop := TM.Halts trans init

end Twin

/-- The pairs of states (this machine, twin) that stand on identical tapes. -/
def paired : St → Twin.St → Bool
  | .A, .A | .B, .B | .D, .C | .E, .E | .F, .F => true
  | _, _ => false

/-- The simulation relation between a configuration of this machine and one of the twin. -/
inductive Sim : Config → Twin.Config → Prop
  /-- Identical tapes and head position, paired states. -/
  | same (l r : Tape) (s : St) (t : Twin.St) : paired s t = true → Sim ⟨l, r, s⟩ ⟨l, r, t⟩
  /-- The walk left: the twin's D has a 1 behind it, this machine's B the hole. -/
  | walk (L R : Tape) (h : Bool) : Sim ⟨L, cons h (cons false R), .B⟩ ⟨L, cons h (cons true R), .D⟩
  /-- After `B> 0 0`, first step: the cell left behind is 1 here, 0 in the twin. -/
  | b1 (L R : Tape) : Sim ⟨cons true L, cons false R, .C⟩ ⟨cons false L, cons false R, .C⟩
  /-- After `B> 0 0`, second step: the same cell, now under the head. -/
  | b2 (L R : Tape) : Sim ⟨L, cons true R, .D⟩ ⟨L, cons false R, .D⟩

/-- The twin stands in B and the two cells ahead are not `0 0`. -/
def Break (d : Twin.Config) : Prop := d.st = .B ∧ (d.r 0 = true ∨ d.r 1 = true)

theorem cons_head_tail (s : Tape) : cons (s 0) (tail s) = s := by
  funext n; cases n <;> rfl

theorem sim_init : Sim init Twin.init := Sim.same _ _ _ _ rfl

/-- One step of the twin is one or three steps of this machine, unless the twin is at a break. -/
theorem sim_step {c : Config} {d : Twin.Config} (h : Sim c d) (hb : ¬ Break d) :
    ∃ d', Twin.step d = some d' ∧ ∃ c', (steps 1 c = some c' ∨ steps 3 c = some c') ∧ Sim c' d' := by
  cases h with
  | same l r s t hp =>
    cases s <;> cases t <;> simp [paired] at hp <;> cases hx : r 0
    -- A, A
    · exact ⟨⟨cons true l, tail r, .B⟩, by simp [Twin.step, TM.step, Twin.trans, hx], ⟨cons true l, tail r, .B⟩,
        .inl (by simp [steps, TM.steps, TM.step, trans, hx]), Sim.same _ _ _ _ rfl⟩
    · exact ⟨⟨cons false l, tail r, .E⟩, by simp [Twin.step, TM.step, Twin.trans, hx], ⟨cons false l, tail r, .E⟩,
        .inl (by simp [steps, TM.steps, TM.step, trans, hx]), Sim.same _ _ _ _ rfl⟩
    -- B, B
    · cases hy : r 1
      · have e : tail r = cons false (tail (tail r)) := by
          rw [← cons_head_tail (tail r)]; simp [tail, hy]
        refine ⟨⟨cons false l, cons false (tail (tail r)), .C⟩, ?_, ⟨cons true l, cons false (tail (tail r)), .C⟩,
          .inl ?_, Sim.b1 _ _⟩
        · simp [Twin.step, TM.step, Twin.trans, hx, ← e]
        · simp [steps, TM.steps, TM.step, trans, hx, ← e]
      · exact absurd ⟨rfl, .inr hy⟩ hb
    · exact absurd ⟨rfl, .inl hx⟩ hb
    -- D, C
    · exact ⟨⟨tail l, cons (l 0) (cons true (tail r)), .D⟩, by simp [Twin.step, TM.step, Twin.trans, hx], ⟨tail l, cons (l 0) (cons false (tail r)), .B⟩,
        .inl (by simp [steps, TM.steps, TM.step, trans, hx]), Sim.walk _ _ _⟩
    · exact ⟨⟨tail l, cons (l 0) (cons true (tail r)), .E⟩, by simp [Twin.step, TM.step, Twin.trans, hx], ⟨tail l, cons (l 0) (cons true (tail r)), .E⟩,
        .inl (by simp [steps, TM.steps, TM.step, trans, hx]), Sim.same _ _ _ _ rfl⟩
    -- E, E
    · exact ⟨⟨cons true l, tail r, .F⟩, by simp [Twin.step, TM.step, Twin.trans, hx], ⟨cons true l, tail r, .F⟩,
        .inl (by simp [steps, TM.steps, TM.step, trans, hx]), Sim.same _ _ _ _ rfl⟩
    · exact ⟨⟨tail l, cons (l 0) (cons false (tail r)), .C⟩, by simp [Twin.step, TM.step, Twin.trans, hx], ⟨tail l, cons (l 0) (cons false (tail r)), .D⟩,
        .inl (by simp [steps, TM.steps, TM.step, trans, hx]), Sim.same _ _ _ _ rfl⟩
    -- F, F
    · exact ⟨⟨cons true l, tail r, .A⟩, by simp [Twin.step, TM.step, Twin.trans, hx], ⟨cons true l, tail r, .A⟩,
        .inl (by simp [steps, TM.steps, TM.step, trans, hx]), Sim.same _ _ _ _ rfl⟩
    · exact ⟨⟨cons true l, tail r, .F⟩, by simp [Twin.step, TM.step, Twin.trans, hx], ⟨cons true l, tail r, .F⟩,
        .inl (by simp [steps, TM.steps, TM.step, trans, hx]), Sim.same _ _ _ _ rfl⟩
  | walk L R h =>
    cases h
    · exact ⟨⟨tail L, cons (L 0) (cons true (cons true R)), .E⟩, by simp [Twin.step, TM.step, Twin.trans], ⟨tail L, cons (L 0) (cons true (cons true R)), .E⟩,
        .inr (by simp [steps, TM.steps, TM.step, trans]), Sim.same _ _ _ _ rfl⟩
    · exact ⟨⟨tail L, cons (L 0) (cons true (cons true R)), .D⟩, by simp [Twin.step, TM.step, Twin.trans], ⟨tail L, cons (L 0) (cons false (cons true R)), .B⟩,
        .inr (by simp [steps, TM.steps, TM.step, trans]), Sim.walk _ _ _⟩
  | b1 L R =>
    exact ⟨⟨L, cons false (cons true R), .D⟩, by simp [Twin.step, TM.step, Twin.trans], ⟨L, cons true (cons true R), .D⟩,
        .inl (by simp [steps, TM.steps, TM.step, trans]), Sim.b2 _ _⟩
  | b2 L R =>
    exact ⟨⟨tail L, cons (L 0) (cons true R), .E⟩, by simp [Twin.step, TM.step, Twin.trans], ⟨tail L, cons (L 0) (cons true R), .E⟩,
        .inl (by simp [steps, TM.steps, TM.step, trans]), Sim.same _ _ _ _ rfl⟩

/-- At a break the two configurations are identical, both in B. -/
theorem sim_at_B {c : Config} {d : Twin.Config} (h : Sim c d) (hd : d.st = .B) : c = ⟨d.l, d.r, .B⟩ := by
  cases h with
  | same l r s t hp =>
    simp only at hd; subst hd
    cases s <;> simp [paired] at hp
    rfl
  | walk L R h => cases hd
  | b1 L R => cases hd
  | b2 L R => cases hd

/-- Break on `B> 1`: the twin halts, this machine does not. -/
theorem break_one {c : Config} {d : Twin.Config} (h : Sim c d) (hd : d.st = .B) (hx : d.r 0 = true) :
    Twin.step d = none ∧ ∃ c', step c = some c' := by
  rw [sim_at_B h hd]
  obtain ⟨l, r, t⟩ := d
  simp only at hd hx; subst hd
  simp [step, Twin.step, TM.step, trans, Twin.trans, hx]

/-- Break on `B> 0 1`: the twin goes on, this machine halts after one more step. -/
theorem break_zero_one {c : Config} {d : Twin.Config} (h : Sim c d) (hd : d.st = .B) (hx : d.r 0 = false)
    (hy : d.r 1 = true) :
    (∃ d', Twin.step d = some d') ∧ ∃ c', step c = some c' ∧ step c' = none := by
  rw [sim_at_B h hd]
  obtain ⟨l, r, t⟩ := d
  simp only at hd hx hy; subst hd
  have e : tail r 0 = true := hy
  simp [step, Twin.step, TM.step, trans, Twin.trans, hx, e]

/-- The two runs from blank tape: `n` steps of the twin, `m` of this machine, `n ≤ m ≤ 3n`. -/
def Run (n : Nat) (c : Config) (d : Twin.Config) : Prop :=
  Twin.steps n Twin.init = some d ∧ ∃ m, n ≤ m ∧ m ≤ 3 * n ∧ steps m init = some c

/-- **A slowed-down copy until the first break.**  After `n` steps of the twin from blank tape, this machine, after
between `n` and `3n` steps, is in a configuration that simulates the twin's; or that was so at a break at some
earlier step of the twin. -/
theorem sim_or_break (n : Nat) :
    (∃ c d, Run n c d ∧ Sim c d) ∨ (∃ k, k < n ∧ ∃ c d, Run k c d ∧ Sim c d ∧ Break d) := by
  induction n with
  | zero => exact .inl ⟨_, _, ⟨rfl, 0, Nat.le_refl _, Nat.le_refl _, rfl⟩, sim_init⟩
  | succ n ih =>
    rcases ih with ⟨c, d, ⟨hd, m, h₁, h₂, hc⟩, hs⟩ | ⟨k, hk, h⟩
    · by_cases hb : Break d
      · exact .inr ⟨n, Nat.lt_succ_self n, c, d, ⟨hd, m, h₁, h₂, hc⟩, hs, hb⟩
      · obtain ⟨d', hd', c', hc', hs'⟩ := sim_step hs hb
        refine .inl ⟨c', d', ⟨?_, ?_⟩, hs'⟩
        · exact steps_seq Twin.trans hd (by simp [TM.steps, hd'] : TM.steps Twin.trans 1 d = some d')
        · rcases hc' with hc' | hc'
          · exact ⟨m + 1, by omega, by omega, steps_seq trans hc hc'⟩
          · exact ⟨m + 3, by omega, by omega, steps_seq trans hc hc'⟩
    · exact .inr ⟨k, Nat.lt_succ_of_lt hk, h⟩

/-- No break at any step of the twin's run. -/
def NoBreak : Prop := ∀ n c d, Run n c d → Sim c d → ¬ Break d

/-- With no break, the simulation holds at every step of the twin. -/
theorem sim_of_noBreak (h : NoBreak) (n : Nat) : ∃ c d, Run n c d ∧ Sim c d := by
  rcases sim_or_break n with h' | ⟨k, _, c, d, hr, hs, hb⟩
  · exact h'
  · exact absurd hb (h k c d hr hs)

/-- With no break, neither machine halts. -/
theorem not_halts_of_noBreak (h : NoBreak) : ¬ HaltsFromBlank ∧ ¬ Twin.HaltsFromBlank := by
  constructor
  · exact not_halts_of_forall trans fun n => by
      obtain ⟨c, _, ⟨_, m, h₁, _, hc⟩, _⟩ := sim_of_noBreak h n
      have e : m = n + (m - n) := by omega
      rw [e] at hc
      exact steps_le trans hc
  · exact not_halts_of_forall Twin.trans fun n => by
      obtain ⟨_, d, ⟨hd, _⟩, _⟩ := sim_of_noBreak h n
      exact ⟨d, hd⟩

/-- With no break, the two machines have the same halting behaviour (neither halts). -/
theorem halts_iff_of_noBreak (h : NoBreak) : HaltsFromBlank ↔ Twin.HaltsFromBlank := by
  obtain ⟨h₁, h₂⟩ := not_halts_of_noBreak h
  exact ⟨fun x => absurd x h₁, fun x => absurd x h₂⟩

/-- If either machine halts, the twin's run reached a break, with this machine simulating it up to there. -/
theorem break_of_halts (h : HaltsFromBlank ∨ Twin.HaltsFromBlank) :
    ∃ n c d, Run n c d ∧ Sim c d ∧ Break d := by
  apply Classical.byContradiction
  intro hn
  have nb : NoBreak := fun n c d hr hs hb => hn ⟨n, c, d, hr, hs, hb⟩
  obtain ⟨h₁, h₂⟩ := not_halts_of_noBreak nb
  rcases h with h | h
  · exact h₁ h
  · exact h₂ h

end H121862
