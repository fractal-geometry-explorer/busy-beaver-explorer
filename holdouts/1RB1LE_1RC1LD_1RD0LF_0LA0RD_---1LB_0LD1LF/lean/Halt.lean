import Machine
import Blank

/-!
# 1RB1LE_1RC1LD_1RD0LF_0LA0RD_---1LB_0LD1LF: what a halt has to look like

The machine halts only on E0.  E is entered only by A1 = 1LE, A only by D0 = 0LA, and D moving left (F0 = 0LD or
B1 = 1LD) or moving right (C0 = 1RD, D1 = 0RD).  Moving right, D has a 1 (C0) or a 0 (D1) on its left, and C always
has a 1 on its left (it is entered only by B0 = 1RC), so the chain D0, A1, E0 can only start from D *moving left*
onto a 0 with the cells 1, 0 beyond it.  `halts_iff` states it: the machine halts from blank tape exactly when its run
reaches F reading 0, or B reading 1, with the three cells to the left of the head (nearest first) 0, 1, 0; the halt
follows four steps later.
-/

namespace H51101

open TM

/-- C is entered only by B0 = 1RC, so in state C the cell left of the head is a 1. -/
def InvC (c : Config) : Prop := c.st = .C → c.l 0 = true

theorem invC_step {c c' : Config} (hc : InvC c) (hs : step c = some c') : InvC c' := by
  obtain ⟨l, r, q⟩ := c
  unfold InvC at hc ⊢
  simp only at hc
  unfold step TM.step at hs
  simp only at hs
  cases q <;> cases h0 : r 0 <;> simp [trans, h0] at hs <;> subst hs <;> simp [cons]

theorem invC_steps : ∀ (n : Nat) {c c' : Config}, InvC c → steps n c = some c' → InvC c'
  | 0, c, c', hc, h => by simp [steps, TM.steps] at h; exact h ▸ hc
  | n + 1, c, c', hc, h => by
    cases hs : step c with
    | none => simp [steps, TM.steps, step] at h hs; rw [hs] at h; cases h
    | some d =>
      have := steps_succ_of_step trans n hs
      rw [show steps (n + 1) c = TM.steps trans (n + 1) c from rfl, this] at h
      exact invC_steps n (invC_step hc hs) h

/-- The local fact: three steps before any halt the head is in F reading 0 or in B reading 1, with 0, 1, 0 to its
left (checked over every state and every content of the seven cells the three steps and the halt can look at). -/
theorem pre_halt (q : St) (a b c d e f g : Bool) (L R : Tape) (hC : q = .C → a = true) (c' : Config)
    (h3 : steps 3 ⟨cons a (cons b (cons c L)), cons d (cons e (cons f (cons g R))), q⟩ = some c')
    (hh : step c' = none) :
    ((q = .F ∧ d = false) ∨ (q = .B ∧ d = true)) ∧ a = false ∧ b = true ∧ c = false := by
  cases q <;> cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> cases g <;>
    simp [steps, TM.steps, TM.step, trans, cons] at h3 hC ⊢ <;>
    (try subst h3) <;> simp [step, TM.step, trans, cons] at hh

theorem steps_split {a b : Nat} {c c'' : Config} (h : steps (a + b) c = some c'') :
    ∃ c', steps a c = some c' ∧ steps b c' = some c'' := by
  induction a generalizing c with
  | zero => exact ⟨c, rfl, by simpa using h⟩
  | succ a ih =>
    have e : a + 1 + b = (a + b) + 1 := by omega
    rw [e] at h
    cases hs : step c with
    | none => simp [steps, TM.steps, step] at h hs; rw [hs] at h; cases h
    | some d =>
      rw [show steps (a + b + 1) c = TM.steps trans (a + b + 1) c from rfl, steps_succ_of_step trans _ hs] at h
      obtain ⟨c', h1, h2⟩ := ih h
      exact ⟨c', by rw [show steps (a + 1) c = TM.steps trans (a + 1) c from rfl, steps_succ_of_step trans _ hs]; exact h1, h2⟩

theorem split_tape (t : Tape) : t = cons (t 0) (cons (t 1) (cons (t 2) (fun n => t (n + 3)))) := by
  funext n; rcases n with _ | _ | _ | n <;> rfl

theorem split_tape4 (t : Tape) :
    t = cons (t 0) (cons (t 1) (cons (t 2) (cons (t 3) (fun n => t (n + 4))))) := by
  funext n; rcases n with _ | _ | _ | _ | n <;> rfl

/-- The pattern a halt needs: D about to move left onto 0, 1, 0. -/
def PreHalt (c : Config) : Prop :=
  ((c.st = .F ∧ c.r 0 = false) ∨ (c.st = .B ∧ c.r 0 = true)) ∧ c.l 0 = false ∧ c.l 1 = true ∧ c.l 2 = false

/-- The machine halts from blank tape iff its run reaches `PreHalt` (and then it halts on the fourth step). -/
theorem halts_iff : HaltsFromBlank ↔ ∃ n c, steps n init = some c ∧ PreHalt c := by
  constructor
  · rintro ⟨n, c', h1, h2⟩
    have hn : 3 ≤ n := by
      refine Classical.byContradiction fun hlt => ?_
      obtain ⟨c0, hc0⟩ := blank_runs_kernel
      have := steps_halt trans h1 h2 (10000 - n - 1)
      rw [show n + (10000 - n - 1 + 1) = 10000 by omega] at this
      rw [show steps 10000 init = TM.steps trans 10000 init from rfl, this] at hc0
      cases hc0
    obtain ⟨c, hc, h3⟩ := steps_split (a := n - 3) (b := 3) (by rw [show n - 3 + 3 = n by omega]; exact h1)
    have hinv := invC_steps (n - 3) (c := init) (fun h => by cases h) hc
    refine ⟨n - 3, c, hc, ?_⟩
    obtain ⟨l, r, q⟩ := c
    rw [split_tape l, split_tape4 r] at h3
    have := pre_halt q (l 0) (l 1) (l 2) (r 0) (r 1) (r 2) (r 3) _ _ hinv c' h3 h2
    exact this
  · rintro ⟨n, c, hc, hp⟩
    obtain ⟨l, r, q⟩ := c
    obtain ⟨hq, h0, h1, h2⟩ := hp
    simp only at hq h0 h1 h2
    have hl := split_tape l
    rw [h0, h1, h2] at hl
    rcases hq with ⟨rfl, hr⟩ | ⟨rfl, hr⟩
    · refine ⟨n + 3, ⟨fun k => l (k + 3), cons false (cons true (cons false (cons false (tail r)))), .E⟩, ?_, rfl⟩
      have h3 : steps 3 ⟨l, r, .F⟩ = some ⟨fun k => l (k + 3), cons false (cons true (cons false (cons false (tail r)))), .E⟩ := by
        rw [hl, ← CTL.cons_head_tail r, hr]; rfl
      exact steps_seq trans hc h3
    · refine ⟨n + 3, ⟨fun k => l (k + 3), cons false (cons true (cons false (cons true (tail r)))), .E⟩, ?_, rfl⟩
      have h3 : steps 3 ⟨l, r, .B⟩ = some ⟨fun k => l (k + 3), cons false (cons true (cons false (cons true (tail r)))), .E⟩ := by
        rw [hl, ← CTL.cons_head_tail r, hr]; rfl
      exact steps_seq trans hc h3

end H51101
