import FarEnd

/-!
# One run for two machines

1RB0RA_0LC0RF_0LB1RD_1LE---_1RA0LF_1LE0RC is this machine's table (1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE) read
in a mirror with the states renamed, started in state C.  After 2 and 49 steps the runs from A and from C are at the
same configuration, `C>1 1`, except that the second has the word `10001101` once more at the right end
(`at_A`, `at_C`).

`Rel k n c c'` says that `c'` is `c` with `k` words `10001101` inserted just right of a cell q, `n` cells right of
the head, with blank tape beyond q in `c`.  A step keeps the relation (with `n` one more or one less) unless the
head moves right from cell q.  In the runs that happens only in state B on a 1, and then the head crosses the `k`
words and comes back with the same cells for every `k` (`far_B`, from the symbolic runs of `FarEnd.lean`); the
cell q moves two cells to the right.  Any other move right from cell q is the excluded case (`Bad`).  `trk` runs the
first machine and keeps track of `n` (`tnext`); `Good n c` says that this tracked run never reaches a `Bad` pair.

* `lockstep`: if the tracked run from `c` is `Good`, `c` and `c'` both halt or both run forever;
* `two_machines`: if the tracked run of 1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE from its configuration after 2
  steps is `Good` (`Good30773`), it halts from blank tape if and only if 1RB0RA_0LC0RF_0LB1RD_1LE---_1RA0LF_1LE0RC
  does.

`Good30773` is not proved.  The cell q is the rightmost cell the run has visited, and the condition says that the
head leaves it to the right only in state B on a 1.  The README has the numbers.  Kernel only: `propext` and
`Quot.sound`.
-/

namespace H30773

open TM

/-! ## The relation: `c'` is `c` with `k` words `10001101` more at the right end -/

/-- The word that the tail of the run is made of, read left to right. -/
abbrev W8 : List Bool := [true, false, false, false, true, true, false, true]

/-- `c'` is `c` with `k` copies of `10001101` inserted just right of the cell q, `n` cells right of the head: same
state, same cells left of the head, and from the head rightwards the same `n + 1` cells `u` followed by blank tape
in `c` and by `(10001101)^k` and blank tape in `c'`. -/
def Rel (k n : Nat) (c c' : Config) : Prop :=
  c.st = c'.st ∧ c.l = c'.l ∧
    ∃ u : List Bool, u.length = n + 1 ∧ c.r = app u blank ∧ c'.r = app u (rep k W8 blank)

/-- How far the cell q is to the right of the head after one step.  A move right from q itself (only allowed in
state B on a 1) moves q two cells right. -/
def tnext (n : Nat) (c : Config) : Nat :=
  match trans c.st (c.r 0) with
  | some (_, .L, _) => n + 1
  | some (_, .R, _) => if n = 0 then 1 else n - 1
  | none => n

/-- The run, keeping track of `n`. -/
def trk : Nat → Nat → Config → Option (Nat × Config)
  | 0, n, c => some (n, c)
  | m + 1, n, c =>
    match TM.step trans c with
    | none => none
    | some d => trk m (tnext n c) d

/-- The one situation the relation cannot follow: a move right from the cell q, except in state B on a 1. -/
def Bad (n : Nat) (d : Config) : Prop :=
  n = 0 ∧ (∃ w s, trans d.st (d.r 0) = some (w, .R, s)) ∧ ¬ (d.st = .B ∧ d.r 0 = true)

/-- The tracked run from `(n, c)` never reaches a `Bad` pair. -/
def Good (n : Nat) (c : Config) : Prop := ∀ m n' d, trk m n c = some (n', d) → ¬ Bad n' d

theorem good_step {n : Nat} {c d : Config} (hG : Good n c) (h : TM.step trans c = some d) : Good (tnext n c) d := by
  intro m n' e he
  exact hG (m + 1) n' e (by simp only [trk, h]; exact he)

theorem good_trk {m n n' : Nat} {c d : Config} (hG : Good n c) (h : trk m n c = some (n', d)) : Good n' d := by
  induction m generalizing n c with
  | zero => simp only [trk, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact hG
  | succ m ih =>
    simp only [trk] at h
    rcases hs : TM.step trans c with _ | e
    · rw [hs] at h; cases h
    · rw [hs] at h; exact ih (good_step hG hs) h

/-! ## Runs -/

theorem steps_add (a b : Nat) (c : Config) : TM.steps trans (a + b) c = (TM.steps trans a c).bind (TM.steps trans b) := by
  induction a generalizing c with
  | zero => simp [TM.steps]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega]
    cases h : TM.step trans c with
    | none => simp [TM.steps, h]
    | some d => simp [TM.steps, h, ih d]

theorem steps_one {c d : Config} (h : TM.step trans c = some d) : TM.steps trans 1 c = some d := by
  simp [TM.steps, h]

theorem halts_of_step {c d : Config} (h : TM.step trans c = some d) (hd : Halts trans d) : Halts trans c := by
  obtain ⟨m, e, he, hs⟩ := hd
  exact ⟨m + 1, e, by simp [TM.steps, show TM.step trans c = some d from h, he], hs⟩

theorem halts_iff_of_steps {n : Nat} {c d : Config} (h : TM.steps trans n c = some d) :
    Halts trans c ↔ Halts trans d := by
  constructor
  · rintro ⟨m, e, he, hs⟩
    by_cases hmn : m < n
    · have := TM.steps_halt trans he hs (n - m - 1)
      rw [show m + (n - m - 1 + 1) = n by omega] at this
      rw [this] at h; cases h
    · have e2 : TM.steps trans (n + (m - n)) c = some e := by rw [show n + (m - n) = m by omega]; exact he
      rw [steps_add, h] at e2
      exact ⟨m - n, e, e2, hs⟩
  · rintro ⟨m, e, he, hs⟩
    exact ⟨n + m, e, by rw [steps_add, h]; exact he, hs⟩

/-- A run that halts after `m` TM.steps trans from `c`, where `TM.steps trans a c` is defined, has `a ≤ m` and halts after `m - a`
TM.steps trans from there. -/
theorem halt_after {a m : Nat} {c e d : Config} (ha : TM.steps trans a c = some e) (hm : TM.steps trans m c = some d)
    (hs : TM.step trans d = none) : a ≤ m ∧ TM.steps trans (m - a) e = some d := by
  by_cases h : m < a
  · have := TM.steps_halt trans hm hs (a - m - 1)
    rw [show m + (a - m - 1 + 1) = a by omega, ha] at this
    cases this
  · refine ⟨by omega, ?_⟩
    have e2 : TM.steps trans (a + (m - a)) c = some d := by rw [show a + (m - a) = m by omega]; exact hm
    rw [steps_add, ha] at e2
    exact e2

theorem trans_cases (q : St) (b : Bool) :
    trans q b = none ∨ (∃ w s, trans q b = some (w, .R, s)) ∨ (∃ w s, trans q b = some (w, .L, s)) := by
  cases q <;> cases b <;> simp [trans]

theorem step_R {l r : Tape} {q s : St} {w : Bool} (ht : trans q (r 0) = some (w, .R, s)) :
    TM.step trans ⟨l, r, q⟩ = some ⟨cons w l, tail r, s⟩ := by
  simp [TM.step, ht]

theorem step_L {l r : Tape} {q s : St} {w : Bool} (ht : trans q (r 0) = some (w, .L, s)) :
    TM.step trans ⟨l, r, q⟩ = some ⟨tail l, cons (l 0) (cons w (tail r)), s⟩ := by
  simp [TM.step, ht]

theorem step_none {l r : Tape} {q : St} (ht : trans q (r 0) = none) : TM.step trans ⟨l, r, q⟩ = none := by
  simp [TM.step, ht]

/-! ## The far end: the only place where the two tapes differ -/

theorem far_B (k : Nat) (a : Bool) (X : Tape) :
    TM.steps trans (44 * k + 5) ⟨cons a X, cons true (rep k W8 blank), .B⟩ =
      some ⟨X, app [a, true, false, true] (rep k W8 blank), .D⟩ := by
  have e : cons true (cons false (rep k [true, true, false, false, false, true, true, false] (cons true blank))) =
      app [true, false, true] (rep k W8 blank) := by
    show app [true, false] (rep k [true, true, false, false, false, true, true, false] (app [true] blank)) =
      app [true, false] (app [true] (rep k W8 blank))
    rw [rep_rotate k [true] W8 [true, true, false, false, false, true, true, false] rfl blank]
  cases a
  · refine (far_B0_run k X).trans ?_
    show some (⟨X, cons false (cons true (cons false (rep k [true, true, false, false, false, true, true, false]
      (cons true blank)))), .D⟩ : Config) = _
    rw [e]; rfl
  · refine (far_B1_run k X).trans ?_
    show some (⟨X, cons true (cons true (cons false (rep k [true, true, false, false, false, true, true, false]
      (cons true blank)))), .D⟩ : Config) = _
    rw [e]; rfl

/-- The tracked run of the first machine over the same five steps (`k = 0`): q moves two cells right, and the head
ends three cells left of it. -/
theorem far_trk (a : Bool) (X : Tape) :
    trk 5 0 ⟨cons a X, cons true blank, .B⟩ = some (3, ⟨X, app [a, true, false, true] blank, .D⟩) := by
  cases a <;> rfl

theorem cons_tail (s : Tape) : cons (s 0) (tail s) = s := by
  funext n; cases n <;> rfl

/-! ## The simulation -/

theorem fwd (k : Nat) : ∀ m n (c c' : Config), Rel k n c c' → Good n c →
    (∃ d, TM.steps trans m c = some d ∧ TM.step trans d = none) → Halts trans c' := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
  intro n c c' hR hG hH
  obtain ⟨l, r, q⟩ := c
  obtain ⟨l', r', q'⟩ := c'
  obtain ⟨hq, hl, u, hu, hr, hr'⟩ := hR
  simp only at hq hl hr hr'
  subst hq hl hr hr'
  obtain ⟨d, hd, hdh⟩ := hH
  rcases u with _ | ⟨a, u⟩
  · exact Nat.noConfusion hu
  rcases trans_cases q a with ht | ⟨w, s, ht⟩ | ⟨w, s, ht⟩
  · exact ⟨0, _, rfl, step_none (r := app (a :: u) (rep k W8 blank)) ht⟩
  · -- a move to the right
    have h1 := step_R (l := l) (r := app (a :: u) blank) ht
    have h1' := step_R (l := l) (r := app (a :: u) (rep k W8 blank)) ht
    rcases u with _ | ⟨b, u⟩
    · -- from the cell q: only B on a 1 is allowed
      have hB : q = .B ∧ a = true := by
        rcases Decidable.em (q = .B ∧ a = true) with hB | hne
        · exact hB
        · exact (hG 0 n ⟨l, app [a] blank, q⟩ rfl ⟨by simp only [List.length_cons, List.length_nil] at hu; omega, ⟨w, s, ht⟩, hne⟩).elim
      obtain ⟨rfl, rfl⟩ := hB
      have hn0 : n = 0 := by simp only [List.length_cons, List.length_nil] at hu; omega
      subst hn0
      obtain ⟨a0, X, rfl⟩ : ∃ a0 X, l = cons a0 X := ⟨l 0, tail l, (cons_tail l).symm⟩
      have f0 := far_B 0 a0 X
      have fk := far_B k a0 X
      have hG5 := good_trk hG (far_trk a0 X)
      obtain ⟨hle, hrest⟩ := halt_after f0 hd hdh
      refine (halts_iff_of_steps fk).2 (ih (m - (44 * 0 + 5)) (by omega) 3 _ _ ?_ hG5 ⟨d, hrest, hdh⟩)
      exact ⟨rfl, rfl, [a0, true, false, true], rfl, rfl, rfl⟩
    · cases m with
      | zero => simp only [TM.steps, Option.some.injEq] at hd; subst hd; rw [h1] at hdh; cases hdh
      | succ m =>
        rw [TM.steps, h1] at hd
        dsimp only at hd
        have hG1 := good_step hG h1
        have hn : tnext n ⟨l, app (a :: b :: u) blank, q⟩ = n - 1 := by
          have hn0 : n ≠ 0 := by simp only [List.length_cons, List.length_nil] at hu; omega
          simp only [tnext, app_cons, cons_zero, ht, if_neg hn0]
        rw [hn] at hG1
        refine halts_of_step h1' (ih m (by omega) (n - 1) _ _ ?_ hG1 ⟨d, hd, hdh⟩)
        exact ⟨rfl, rfl, b :: u, by simp only [List.length_cons, List.length_nil] at hu ⊢; omega, rfl, rfl⟩
  · -- a move to the left
    have h1 := step_L (l := l) (r := app (a :: u) blank) ht
    have h1' := step_L (l := l) (r := app (a :: u) (rep k W8 blank)) ht
    cases m with
    | zero => simp only [TM.steps, Option.some.injEq] at hd; subst hd; rw [h1] at hdh; cases hdh
    | succ m =>
      rw [TM.steps, h1] at hd
      dsimp only at hd
      have hG1 := good_step hG h1
      have hn : tnext n ⟨l, app (a :: u) blank, q⟩ = n + 1 := by
        simp only [tnext, app_cons, cons_zero, ht]
      rw [hn] at hG1
      refine halts_of_step h1' (ih m (by omega) (n + 1) _ _ ?_ hG1 ⟨d, hd, hdh⟩)
      exact ⟨rfl, rfl, l 0 :: w :: u, by simp only [List.length_cons, List.length_nil] at hu ⊢; omega, rfl, rfl⟩
theorem bwd (k : Nat) : ∀ m n (c c' : Config), Rel k n c c' → Good n c →
    (∃ d, TM.steps trans m c' = some d ∧ TM.step trans d = none) → Halts trans c := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
  intro n c c' hR hG hH
  obtain ⟨l, r, q⟩ := c
  obtain ⟨l', r', q'⟩ := c'
  obtain ⟨hq, hl, u, hu, hr, hr'⟩ := hR
  simp only at hq hl hr hr'
  subst hq hl hr hr'
  obtain ⟨d, hd, hdh⟩ := hH
  rcases u with _ | ⟨a, u⟩
  · exact Nat.noConfusion hu
  rcases trans_cases q a with ht | ⟨w, s, ht⟩ | ⟨w, s, ht⟩
  · exact ⟨0, _, rfl, step_none (r := app (a :: u) blank) ht⟩
  · -- a move to the right
    have h1 := step_R (l := l) (r := app (a :: u) blank) ht
    have h1' := step_R (l := l) (r := app (a :: u) (rep k W8 blank)) ht
    rcases u with _ | ⟨b, u⟩
    · -- from the cell q: only B on a 1 is allowed
      have hB : q = .B ∧ a = true := by
        rcases Decidable.em (q = .B ∧ a = true) with hB | hne
        · exact hB
        · exact (hG 0 n ⟨l, app [a] blank, q⟩ rfl ⟨by simp only [List.length_cons, List.length_nil] at hu; omega, ⟨w, s, ht⟩, hne⟩).elim
      obtain ⟨rfl, rfl⟩ := hB
      have hn0 : n = 0 := by simp only [List.length_cons, List.length_nil] at hu; omega
      subst hn0
      obtain ⟨a0, X, rfl⟩ : ∃ a0 X, l = cons a0 X := ⟨l 0, tail l, (cons_tail l).symm⟩
      have f0 := far_B 0 a0 X
      have fk := far_B k a0 X
      have hG5 := good_trk hG (far_trk a0 X)
      obtain ⟨hle, hrest⟩ := halt_after fk hd hdh
      refine (halts_iff_of_steps f0).2 (ih (m - (44 * k + 5)) (by omega) 3 _ _ ?_ hG5 ⟨d, hrest, hdh⟩)
      exact ⟨rfl, rfl, [a0, true, false, true], rfl, rfl, rfl⟩
    · cases m with
      | zero => simp only [TM.steps, Option.some.injEq] at hd; subst hd; rw [h1'] at hdh; cases hdh
      | succ m =>
        rw [TM.steps, h1'] at hd
        dsimp only at hd
        have hG1 := good_step hG h1
        have hn : tnext n ⟨l, app (a :: b :: u) blank, q⟩ = n - 1 := by
          have hn0 : n ≠ 0 := by simp only [List.length_cons, List.length_nil] at hu; omega
          simp only [tnext, app_cons, cons_zero, ht, if_neg hn0]
        rw [hn] at hG1
        refine halts_of_step h1 (ih m (by omega) (n - 1) _ _ ?_ hG1 ⟨d, hd, hdh⟩)
        exact ⟨rfl, rfl, b :: u, by simp only [List.length_cons, List.length_nil] at hu ⊢; omega, rfl, rfl⟩
  · -- a move to the left
    have h1 := step_L (l := l) (r := app (a :: u) blank) ht
    have h1' := step_L (l := l) (r := app (a :: u) (rep k W8 blank)) ht
    cases m with
    | zero => simp only [TM.steps, Option.some.injEq] at hd; subst hd; rw [h1'] at hdh; cases hdh
    | succ m =>
      rw [TM.steps, h1'] at hd
      dsimp only at hd
      have hG1 := good_step hG h1
      have hn : tnext n ⟨l, app (a :: u) blank, q⟩ = n + 1 := by
        simp only [tnext, app_cons, cons_zero, ht]
      rw [hn] at hG1
      refine halts_of_step h1 (ih m (by omega) (n + 1) _ _ ?_ hG1 ⟨d, hd, hdh⟩)
      exact ⟨rfl, rfl, l 0 :: w :: u, by simp only [List.length_cons, List.length_nil] at hu ⊢; omega, rfl, rfl⟩

/-- **Lockstep.**  If `c'` is `c` with `k` more words `10001101` just right of the cell q and the tracked run from
`c` never reaches a `Bad` pair, then `c` and `c'` both halt or both run forever. -/
theorem lockstep {k n : Nat} {c c' : Config} (hR : Rel k n c c') (hG : Good n c) : Halts trans c ↔ Halts trans c' :=
  ⟨fun ⟨m, d, hd, hs⟩ => fwd k m n c c' hR hG ⟨d, hd, hs⟩, fun ⟨m, d, hd, hs⟩ => bwd k m n c c' hR hG ⟨d, hd, hs⟩⟩

/-! ## The two runs -/

/-- The run of this machine after 2 steps: `C>1 1`, blank tape around. -/
theorem at_A : TM.steps trans 2 (blankCfg .A) = some ⟨blank, app [true, true] blank, .C⟩ := rfl

/-- The run of the table from state C (1RB0RA_0LC0RF_0LB1RD_1LE---_1RA0LF_1LE0RC, mirrored) after 49 steps: the same
with `10001101` more on the right. -/
theorem at_C : TM.steps trans 49 (blankCfg .C) = some ⟨blank, app [true, true] (app W8 blank), .C⟩ := rfl

/-! ## The other machine -/

/-- A map of configurations that commutes with one step commutes with every run, and keeps halting. -/
theorem halts_map {Q Q' : Type} (δ : Q → Bool → Option (Bool × Dir × Q)) (δ' : Q' → Bool → Option (Bool × Dir × Q'))
    (φ : Cfg Q → Cfg Q') (hφ : ∀ c, TM.step δ' (φ c) = (TM.step δ c).map φ) (c : Cfg Q) :
    Halts δ c ↔ Halts δ' (φ c) := by
  have hs : ∀ n (c : Cfg Q), TM.steps δ' n (φ c) = (TM.steps δ n c).map φ := by
    intro n
    induction n with
    | zero => intro c; rfl
    | succ n ih =>
      intro c
      simp only [TM.steps, hφ c]
      rcases TM.step δ c with _ | c'
      · rfl
      · exact ih c'
  constructor
  · rintro ⟨n, d, hd, hh⟩
    exact ⟨n, φ d, by rw [hs, hd]; rfl, by rw [hφ, hh]; rfl⟩
  · rintro ⟨n, d', hd', hh'⟩
    rw [hs] at hd'
    rcases h : TM.steps δ n c with _ | d
    · rw [h] at hd'; cases hd'
    · rw [h] at hd'
      cases hd'
      refine ⟨n, d, h, ?_⟩
      rw [hφ] at hh'
      rcases h2 : TM.step δ d with _ | e
      · rfl
      · rw [h2] at hh'; cases hh'

def flipD : Dir → Dir
  | .L => .R
  | .R => .L


/-- The mirror image of a configuration, the states renamed by `f`: the head stays on its cell, the sides swap. -/
def mir {Q Q' : Type} (f : Q → Q') (c : Cfg Q) : Cfg Q' := ⟨tail c.r, cons (c.r 0) c.l, f c.st⟩

theorem step_mir {Q Q' : Type} (δ : Q → Bool → Option (Bool × Dir × Q)) (δ' : Q' → Bool → Option (Bool × Dir × Q'))
    (f : Q → Q') (hδ : ∀ q b, δ' (f q) b = (δ q b).map (fun t => (t.1, flipD t.2.1, f t.2.2))) (c : Cfg Q) :
    TM.step δ' (mir f c) = (TM.step δ c).map (mir f) := by
  obtain ⟨l, r, q⟩ := c
  rcases h : δ q (r 0) with _ | ⟨w, d, s⟩
  · simp [TM.step, mir, hδ, h]
  · cases d
    · simp [TM.step, mir, hδ, h, flipD]
      exact (cons_tail l).symm
    · simp [TM.step, mir, hδ, h, flipD]

/-- The states renamed by `f`, nothing mirrored. -/
def ren {Q Q' : Type} (f : Q → Q') (c : Cfg Q) : Cfg Q' := ⟨c.l, c.r, f c.st⟩

theorem step_ren {Q Q' : Type} (δ : Q → Bool → Option (Bool × Dir × Q)) (δ' : Q' → Bool → Option (Bool × Dir × Q'))
    (f : Q → Q') (hδ : ∀ q b, δ' (f q) b = (δ q b).map (fun t => (t.1, t.2.1, f t.2.2))) (c : Cfg Q) :
    TM.step δ' (ren f c) = (TM.step δ c).map (ren f) := by
  obtain ⟨l, r, q⟩ := c
  rcases h : δ q (r 0) with _ | ⟨w, d, s⟩
  · simp [TM.step, ren, hδ, h]
  · cases d <;> simp [TM.step, ren, hδ, h]

theorem mir_blank {Q Q' : Type} (f : Q → Q') (q : Q) : mir f (blankCfg q) = blankCfg (f q) := by
  show (⟨tail blank, cons false blank, f q⟩ : Cfg Q') = ⟨blank, blank, f q⟩
  rw [TM.cons_false_blank]; rfl


/-- 1RB0RA_0LC0RF_0LB1RD_1LE---_1RA0LF_1LE0RC is this table mirrored, with A, B, C, D, E, F renamed D, E, A, B, C,
F. -/
def f114265 : St → M114265.St
  | .A => .D | .B => .E | .C => .A | .D => .B | .E => .C | .F => .F

theorem halts_114265 : Halts trans (blankCfg .C) ↔ Halts M114265.trans (blankCfg .A) := by
  have := halts_map trans M114265.trans (mir f114265)
    (step_mir trans M114265.trans f114265 (by intro q b; cases q <;> cases b <;> rfl)) (blankCfg .C)
  rw [mir_blank] at this; exact this

/-- The condition, on the run of 1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE from blank tape after its first 2 steps
(`at_A`), with the cell q one cell right of the head: the tracked run never moves right from the cell q except in
state B on a 1. -/
def Good30773 : Prop := Good 1 ⟨blank, app [true, true] blank, .C⟩

/-- **One halting question for two machines.**  If `Good30773` holds, 1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE
halts from blank tape if and only if 1RB0RA_0LC0RF_0LB1RD_1LE---_1RA0LF_1LE0RC does. -/
theorem two_machines (h : Good30773) : Halts trans (blankCfg .A) ↔ Halts M114265.trans (blankCfg .A) := by
  rw [halts_iff_of_steps at_A, ← halts_114265, halts_iff_of_steps at_C]
  exact lockstep (k := 1) (n := 1) (c := ⟨blank, app [true, true] blank, .C⟩)
    (c' := ⟨blank, app [true, true] (app W8 blank), .C⟩) ⟨rfl, rfl, [true, true], rfl, rfl, rfl⟩ h

end H30773
