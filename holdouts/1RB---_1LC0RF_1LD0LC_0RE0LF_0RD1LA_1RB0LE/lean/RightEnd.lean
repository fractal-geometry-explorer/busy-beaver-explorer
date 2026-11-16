import Lockstep

/-!
# The right end grows only through `far_B` (`Good30773` proved)

`Good30773` (`Lockstep.lean`) says that in the run of 1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE from its
configuration after 2 steps, the head leaves the cell q to the right only in state B on a 1, where q is the
rightmost cell the tracked run has reached.  It looked like a statement about the rebuilds of the counter, but it is
a local fact about the last four cells, q-3 to q.

Look only at those four cells and at the state, and forget everything left of them.  While the head is inside the
four cells, record the state, the cells left of the head inside the window (`wl`, nearest first) and the cells from
the head to q (`u`).  While the head is further left, record only the four cells (`out w`); the head can come back
into the window in any state that a move to the right can produce (B, D, E or F).  This over-approximation has
exactly 32 abstract states (`S`): 30 with the head in the window and 2 with it outside.  Whenever the head is left
of the window, the last three cells read `101`.  None of the 32 moves right from q except in state B on a 1, and
the set is closed under one step (`closed`, checked by `decide`).  So the tracked run never reaches a `Bad`
pair, for every number of steps (`good30773`), and the condition of `two_machines` is dropped:

* **`two_machines'`**: 1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE halts from blank tape if and only if
  1RB0RA_0LC0RF_0LB1RD_1LE---_1RA0LF_1LE0RC does.

`py/rightend.py` computes `S`.  Kernel only: `propext` and `Quot.sound`.
-/

set_option linter.unusedSimpArgs false

namespace H30773

open TM

/-- An abstract configuration: the head inside the last four cells (state, cells left of the head inside the
window nearest first, cells from the head to q), or the head left of them (the four cells). -/
inductive Ab where
  | inn (s : St) (wl u : List Bool)
  | out (w : List Bool)
  deriving DecidableEq

/-- The states a move to the right can lead to. -/
def rTargets : List St := [.B, .D, .E, .F]

theorem mem_rTargets {s s' : St} {a b : Bool} (h : trans s a = some (b, .R, s')) : s' ∈ rTargets := by
  cases s <;> cases a <;> simp [trans] at h <;> obtain ⟨-, rfl⟩ := h <;> simp [rTargets]

/-- The abstract successors.  A move right from q (`u` of length 1) is followed only in state B on a 1; the window
then moves two cells right. -/
def next : Ab → List Ab
  | .inn _ _ [] => []
  | .inn s wl (a :: u) =>
    match trans s a with
    | none => []
    | some (b, .L, s') =>
      match wl with
      | [] => [.out (b :: u)]
      | x :: wl' => [.inn s' wl' (x :: b :: u)]
    | some (b, .R, s') =>
      match u with
      | [] => [.inn s' ((b :: wl).take 2) [false, false]]
      | u => [.inn s' (b :: wl) u]
  | .out w => .out w :: rTargets.map (fun t => .inn t [] w)

/-- No bad move: an abstract configuration at q moves right only in state B on a 1; the window outside is not
empty. -/
def okb : Ab → Bool
  | .inn s _ [a] =>
    match trans s a with
    | some (_, .R, _) => s == .B && a
    | _ => true
  | .inn _ _ _ => true
  | .out w => !w.isEmpty

/-- The 32 abstract configurations of the run (`py/rightend.py`). -/
def S : List Ab := [
  .inn .A [] [false, true, false, true],
  .inn .B [] [false, true, false, true],
  .inn .B [] [true, true, false, true],
  .inn .B [true] [false, false, true],
  .inn .B [true] [true, false, true],
  .inn .B [true, false, false] [false],
  .inn .B [true, false, true] [false],
  .inn .B [true, false, true] [true],
  .inn .C [] [true, true, false, true],
  .inn .C [false] [false, false, true],
  .inn .C [false, false] [true, true],
  .inn .C [false, true] [true, true],
  .inn .C [true] [false, false, true],
  .inn .D [] [false, true, false, true],
  .inn .D [] [true, true, false, true],
  .inn .D [false] [false, false, true],
  .inn .D [false] [true, false, true],
  .inn .D [false, false, false] [true],
  .inn .E [] [false, false, false, true],
  .inn .E [] [false, true, false, true],
  .inn .E [] [true, true, false, true],
  .inn .E [false] [true, false, true],
  .inn .E [false, false] [false, true],
  .inn .F [] [false, false, false, true],
  .inn .F [] [false, true, false, true],
  .inn .F [] [true, true, false, true],
  .inn .F [false] [true, false, true],
  .inn .F [false, false] [false, false],
  .inn .F [false, true] [false, false],
  .inn .F [false, true] [false, true],
  .out [false, true, false, true],
  .out [true, true, false, true]]

def check (L : List Ab) : Bool := L.all (fun σ => okb σ && (next σ).all (fun τ => L.contains τ))

/-- `S` contains no bad move and is closed under `next`. -/
theorem closed : check S = true := by decide

theorem closed' {σ : Ab} (h : σ ∈ S) : okb σ = true ∧ ∀ τ ∈ next σ, τ ∈ S := by
  have := List.all_eq_true.1 closed σ h
  simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at this
  exact this

/-- A configuration, with q `n` cells right of the head, matches an abstract one. -/
def Matches : Ab → Nat → Config → Prop
  | .inn s wl u, n, c => c.st = s ∧ u.length = n + 1 ∧ c.r = app u blank ∧ ∃ X, c.l = app wl X
  | .out w, n, c => ∃ v, v ≠ [] ∧ (v ++ w).length = n + 1 ∧ c.r = app (v ++ w) blank

theorem app_take_drop (L : List Bool) (k : Nat) (X : Tape) : app L X = app (L.take k) (app (L.drop k) X) := by
  rw [app_app, List.take_append_drop]

theorem ne_nil_of_okb {w : List Bool} (h : okb (.out w) = true) : w ≠ [] := by
  cases w with
  | nil => cases h
  | cons _ _ => exact List.cons_ne_nil _ _

theorem len_ne_zero {v : List Bool} (h : v ≠ []) : v.length ≠ 0 := by
  cases v with
  | nil => exact absurd rfl h
  | cons _ _ => exact Nat.succ_ne_zero _

/-- One step keeps a match, with q tracked by `tnext`. -/
theorem match_step {σ : Ab} {n : Nat} {c d : Config} (hok : okb σ = true) (hm : Matches σ n c)
    (h : TM.step trans c = some d) : ∃ τ ∈ next σ, Matches τ (tnext n c) d := by
  obtain ⟨l, r, s0⟩ := c
  cases σ with
  | inn s wl u =>
    obtain ⟨hs, hu, hr, X, hl⟩ := hm
    simp only at hs hr hl
    subst s0; subst hr hl
    rcases u with _ | ⟨a, u⟩
    · exact Nat.noConfusion hu
    rcases trans_cases s a with ht | ⟨b, s', ht⟩ | ⟨b, s', ht⟩
    · rw [step_none (l := app wl X) (r := app (a :: u) blank) ht] at h; cases h
    · rw [step_R (l := app wl X) (r := app (a :: u) blank) ht] at h
      cases h
      rcases u with _ | ⟨a2, u⟩
      · -- at q: only B on a 1
        have hB : s = .B ∧ a = true := by
          simp only [okb, ht, Bool.and_eq_true, beq_iff_eq] at hok; exact hok
        obtain ⟨rfl, rfl⟩ := hB
        simp only [trans, Option.some.injEq, Prod.mk.injEq] at ht
        obtain ⟨rfl, -, rfl⟩ := ht
        have hn : n = 0 := by simp only [List.length_cons, List.length_append, List.length_nil] at hu; omega
        subst hn
        refine ⟨.inn .F ((false :: wl).take 2) [false, false], by simp [next, trans], rfl, rfl, ?_, ⟨app ((false :: wl).drop 2) X, ?_⟩⟩
        · show tail (app [true] blank) = app [false, false] blank
          simp only [app_cons, app_nil, tail_cons, cons_false_blank]
        · show cons false (app wl X) = _
          rw [← app_take_drop]; rfl
      · have hn0 : n ≠ 0 := by simp only [List.length_cons, List.length_append, List.length_nil] at hu; omega
        refine ⟨.inn s' (b :: wl) (a2 :: u), by simp [next, ht], rfl, ?_, rfl, ⟨X, rfl⟩⟩
        simp only [tnext, app_cons, cons_zero, ht, if_neg hn0]
        simp only [List.length_cons, List.length_append, List.length_nil] at hu ⊢; omega
    · rw [step_L (l := app wl X) (r := app (a :: u) blank) ht] at h
      cases h
      have htn : tnext n ⟨app wl X, app (a :: u) blank, s⟩ = n + 1 := by
        simp only [tnext, app_cons, cons_zero, ht]
      rw [htn]
      rcases wl with _ | ⟨x, wl⟩
      · refine ⟨.out (b :: u), by simp [next, ht], [X 0], List.cons_ne_nil _ _, by simp only [List.length_cons, List.length_append, List.length_nil] at hu ⊢; omega, rfl⟩
      · refine ⟨.inn s' wl (x :: b :: u), by simp [next, ht], rfl, by simp only [List.length_cons, List.length_append, List.length_nil] at hu ⊢; omega, rfl, ⟨X, rfl⟩⟩
  | out w =>
    obtain ⟨v, hv, hlen, hr⟩ := hm
    simp only at hr
    subst hr
    have hw : w ≠ [] := ne_nil_of_okb hok
    rcases v with _ | ⟨a, v⟩
    · exact absurd rfl hv
    rcases trans_cases s0 a with ht | ⟨b, s', ht⟩ | ⟨b, s', ht⟩
    · rw [step_none (l := l) (r := app ((a :: v) ++ w) blank) ht] at h; cases h
    · rw [step_R (l := l) (r := app ((a :: v) ++ w) blank) ht] at h
      cases h
      have hn0 : n ≠ 0 := by
        have : w.length ≠ 0 := len_ne_zero hw
        simp only [List.length_cons, List.length_append, List.length_nil] at hlen; omega
      have htn : tnext n ⟨l, app ((a :: v) ++ w) blank, s0⟩ = n - 1 := by
        simp only [tnext, List.cons_append, app_cons, cons_zero, ht, if_neg hn0]
      rw [htn]
      rcases v with _ | ⟨a2, v⟩
      · refine ⟨.inn s' [] w, ?_, rfl, by simp only [List.length_cons, List.length_append, List.length_nil] at hlen ⊢; omega, rfl, ⟨cons b l, rfl⟩⟩
        simp only [next, List.mem_cons, List.mem_map]
        exact Or.inr ⟨s', mem_rTargets ht, rfl⟩
      · refine ⟨.out w, by simp [next], a2 :: v, List.cons_ne_nil _ _, by simp only [List.length_cons, List.length_append, List.length_nil] at hlen ⊢; omega, rfl⟩
    · rw [step_L (l := l) (r := app ((a :: v) ++ w) blank) ht] at h
      cases h
      have htn : tnext n ⟨l, app ((a :: v) ++ w) blank, s0⟩ = n + 1 := by
        simp only [tnext, List.cons_append, app_cons, cons_zero, ht]
      rw [htn]
      refine ⟨.out w, by simp [next], l 0 :: b :: v, List.cons_ne_nil _ _, by simp only [List.length_cons, List.length_append, List.length_nil] at hlen ⊢; omega, ?_⟩
      simp

/-- The invariant: the configuration matches one of the 32. -/
def Inv (n : Nat) (c : Config) : Prop := ∃ σ ∈ S, Matches σ n c

theorem inv_step {n : Nat} {c d : Config} (hi : Inv n c) (h : TM.step trans c = some d) : Inv (tnext n c) d := by
  obtain ⟨σ, hσ, hm⟩ := hi
  obtain ⟨hok, hcl⟩ := closed' hσ
  obtain ⟨τ, hτ, hm'⟩ := match_step hok hm h
  exact ⟨τ, hcl τ hτ, hm'⟩

theorem inv_trk : ∀ (m n : Nat) (c : Config) {n' : Nat} {d : Config}, Inv n c → trk m n c = some (n', d) → Inv n' d
  | 0, n, c, n', d, hi, h => by
    simp only [trk, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact hi
  | m + 1, n, c, n', d, hi, h => by
    simp only [trk] at h
    rcases hs : TM.step trans c with _ | e
    · rw [hs] at h; cases h
    · rw [hs] at h; exact inv_trk m _ e (inv_step hi hs) h

theorem not_bad {n : Nat} {d : Config} (hi : Inv n d) : ¬ Bad n d := by
  rintro ⟨rfl, ⟨b, s', ht⟩, hne⟩
  obtain ⟨σ, hσ, hm⟩ := hi
  have hok := (closed' hσ).1
  cases σ with
  | inn s wl u =>
    obtain ⟨hs, hu, hr, -⟩ := hm
    rcases u with _ | ⟨a, _ | ⟨a2, u⟩⟩
    · cases hu
    · rw [hs, hr] at ht hne
      simp only [app_cons, cons_zero] at ht hne
      simp only [okb, ht, Bool.and_eq_true, beq_iff_eq] at hok
      exact hne hok
    · simp only [List.length_cons, List.length_append, List.length_nil] at hu; omega
  | out w =>
    obtain ⟨v, hv, hlen, -⟩ := hm
    have hw : w ≠ [] := ne_nil_of_okb hok
    have h1 : v.length ≠ 0 := len_ne_zero hv
    have h2 : w.length ≠ 0 := len_ne_zero hw
    simp only [List.length_cons, List.length_append, List.length_nil] at hlen; omega

theorem good_of_inv {n : Nat} {c : Config} (hi : Inv n c) : Good n c :=
  fun m _ _ h => not_bad (inv_trk m n c hi h)

/-- **`Good30773` holds.** -/
theorem good30773 : Good30773 := by
  refine good_of_inv ⟨.inn .C [false, false] [true, true], by decide, rfl, rfl, rfl, ⟨blank, ?_⟩⟩
  show blank = cons false (cons false blank)
  rw [cons_false_blank, cons_false_blank]

/-- **One halting question for two machines**, with no condition: 1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE halts
from blank tape if and only if 1RB0RA_0LC0RF_0LB1RD_1LE---_1RA0LF_1LE0RC does. -/
theorem two_machines' : Halts trans (blankCfg .A) ↔ Halts M114265.trans (blankCfg .A) :=
  two_machines good30773

end H30773
