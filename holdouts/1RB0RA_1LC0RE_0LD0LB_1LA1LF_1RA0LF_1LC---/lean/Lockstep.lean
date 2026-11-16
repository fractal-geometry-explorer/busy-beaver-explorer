import FarEnd

/-!
# One run for four machines

Four holdouts share the table of 1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC--- up to renaming the states and mirroring
the tape, and start it in four different states: A (this machine), D (1RB1RF_1LC0LB_1RE0LD_1LB0RF_0RA0RC_1RE---,
mirrored), B (1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---, mirrored) and E (1RB0LF_1RC0RB_1LD0RA_0LE0LC_1LB1LF_1LD---).
After 2, 11, 26 and 50 steps the four runs are at the same configuration except that the first run of alternating
cells at the left end is 4, 8 and 12 cells longer than in the run from D (`at_D`, `at_A`, `at_B`, `at_E`).

`Rel k c c'` says that `c'` is `c` with `k` periods `1010` inserted at the left end.  The relation survives every
step except one in which the head steps onto the leftmost 1 (`fwd`, `bwd`); there `far_cases` (from the symbolic runs
of `FarEnd.lean`) takes over: in C and D the head crosses the extra periods and comes back with the same cells, in F
both runs halt at once.  The only case left is the head stepping onto the leftmost 1 in state A or B (`Bad`), which
the theorems exclude by hypothesis (`Good`).  So:

* `lockstep`: if the run from `c` never reaches a `Bad` configuration, `c` and `c'` both halt or both run forever;
* `three_questions`: if this machine's own run never reaches a `Bad` configuration, the runs from B and E (two
  of the sisters) halt if and only if it does;
* `one_question`: if the head of 1RB1RF_1LC0LB_1RE0LD_1LB0RF_0RA0RC_1RE--- never reads a 1 in state B or C with blank
  tape to its right (`Good40600`), the four machines halt together or not at all.

`Good40600` is not proved.  It says that the first run never gets short: a `Bad` configuration needs a doubled cell
within three cells of the left end, and the first run grows by 8 cells every three trips of the counter.  The README
has the numbers (it holds in the first 10^14 steps).  Kernel only: `propext` and `Quot.sound`.
-/

namespace H32883

open TM

/-! ## The relation: `c'` is `c` with `k` periods `1010` more at the left end -/

/-- `1010` read left to right on the tape: one period of an alternating run.  In the left stream (nearest cell
first) it is `0101`. -/
abbrev W4 : List Bool := [false, true, false, true]

/-- `c'` is `c` with `k` copies of `1010` inserted at the left end of the tape, just left of the leftmost 1 to the
left of the head: same state, same cells from the head rightwards, and on the left the same cells `u 1` (nearest
first) followed by blank tape in `c` and by `(1010)^k` and blank tape in `c'`. -/
def Rel (k : Nat) (c c' : Config) : Prop :=
  c.st = c'.st ∧ c.r = c'.r ∧
    ∃ u : List Bool, c.l = app (u ++ [true]) blank ∧ c'.l = app (u ++ [true]) (rep k W4 blank)

/-- The one situation the relation cannot follow: the head reads a 1 with blank tape to its left, in state A or B. -/
def Bad (d : Config) : Prop := d.l = blank ∧ d.r 0 = true ∧ (d.st = St.A ∨ d.st = St.B)

/-- No configuration of the run from `c` is `Bad`. -/
def Good (c : Config) : Prop := ∀ n d, TM.steps trans n c = some d → ¬ Bad d

/-! ## Runs -/

theorem steps_add (a b : Nat) (c : Config) : TM.steps trans (a + b) c = (TM.steps trans a c).bind (TM.steps trans b) := by
  induction a generalizing c with
  | zero => simp [TM.steps]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega]
    cases h : TM.step trans c with
    | none => simp [TM.steps, h]
    | some d => simp [TM.steps, h, ih d]

theorem good_steps {n : Nat} {c d : Config} (hG : Good c) (h : TM.steps trans n c = some d) : Good d := by
  intro m e he
  exact hG (n + m) e (by rw [steps_add, h]; exact he)

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

/-- Every transition halts, moves right, or moves left into a state other than E (no left move leads to E). -/
theorem trans_cases (q : St) (b : Bool) :
    trans q b = none ∨ (∃ w s, trans q b = some (w, .R, s)) ∨ (∃ w s, trans q b = some (w, .L, s) ∧ s ≠ .E) := by
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

theorem far_C (k : Nat) (X : Tape) :
    TM.steps trans (8 * k + 9) ⟨rep k W4 blank, cons true X, .C⟩ =
      some ⟨app [true, false, true, false, true] (rep k W4 blank), X, .B⟩ := by
  refine (far_C_run k X).trans ?_
  show some (⟨app [true, false, true] (rep k W4 (app [false, true] blank)), X, .B⟩ : Config) = _
  rw [← rep_rotate k [false, true] W4 W4 rfl blank]
  rfl

theorem far_D (k : Nat) (X : Tape) :
    TM.steps trans (8 * k + 9) ⟨rep k W4 blank, cons true X, .D⟩ =
      some ⟨app [false, false, true, false, true] (rep k W4 blank), X, .A⟩ := by
  cases k with
  | zero => exact far_D0_run X
  | succ j =>
    rw [show 8 * (j + 1) + 9 = 8 * j + 17 by omega]
    refine (far_D_run j X).trans ?_
    show some (⟨app [false, false, true, false, true] (rep j W4 (app W4 blank)), X, .A⟩ : Config) = _
    rw [rep_app_comm]

/-- At the far end, in the two runs: the head has just stepped onto the leftmost 1 (blank tape, or `(1010)^k`, to
its left).  A and B are excluded by `Good`; F halts at once in both; C and D cross the `k` periods and come back
with the same cells left of the leftmost 1 as `k = 0`. -/
theorem far_cases (k : Nat) (X : Tape) (s : St) (hs : s ≠ .E) (hG : Good ⟨blank, cons true X, s⟩) :
    (TM.step trans ⟨blank, cons true X, s⟩ = none ∧ TM.step trans ⟨rep k W4 blank, cons true X, s⟩ = none) ∨
    (∃ u e e', TM.steps trans 9 ⟨blank, cons true X, s⟩ = some e ∧
      TM.steps trans (8 * k + 9) ⟨rep k W4 blank, cons true X, s⟩ = some e' ∧
      e = ⟨app (u ++ [true]) blank, X, e.st⟩ ∧ e' = ⟨app (u ++ [true]) (rep k W4 blank), X, e.st⟩) := by
  cases s with
  | A => exact absurd (hG 0 _ rfl) (fun h => h ⟨rfl, rfl, Or.inl rfl⟩)
  | B => exact absurd (hG 0 _ rfl) (fun h => h ⟨rfl, rfl, Or.inr rfl⟩)
  | C => exact Or.inr ⟨[true, false, true, false], _, _, far_C 0 X, far_C k X, rfl, rfl⟩
  | D => exact Or.inr ⟨[false, false, true, false], _, _, far_D 0 X, far_D k X, rfl, rfl⟩
  | E => exact absurd rfl hs
  | F => exact Or.inl ⟨rfl, rfl⟩

/-! ## The simulation -/

theorem fwd (k : Nat) : ∀ n (c c' : Config), Rel k c c' → Good c →
    (∃ d, TM.steps trans n c = some d ∧ TM.step trans d = none) → Halts trans c' := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro c c' hR hG hH
  obtain ⟨l, r, q⟩ := c
  obtain ⟨l', r', q'⟩ := c'
  obtain ⟨hq, hr, u, hl, hl'⟩ := hR
  simp only at hq hr hl hl'
  subst hq hr hl hl'
  obtain ⟨d, hd, hdh⟩ := hH
  rcases trans_cases q (r 0) with ht | ⟨w, s, ht⟩ | ⟨w, s, ht, hs⟩
  · exact ⟨0, _, rfl, step_none ht⟩
  · -- a move to the right
    have h1 := step_R (l := app (u ++ [true]) blank) ht
    have h1' := step_R (l := app (u ++ [true]) (rep k W4 blank)) ht
    cases n with
    | zero => simp [TM.steps] at hd; subst hd; rw [h1] at hdh; cases hdh
    | succ m =>
      rw [TM.steps, h1] at hd
      dsimp only at hd
      refine halts_of_step h1' (ih m (by omega) _ _ ?_
        (good_steps hG (steps_one h1)) ⟨d, hd, hdh⟩)
      exact ⟨rfl, rfl, w :: u, rfl, rfl⟩
  · -- a move to the left
    have h1 := step_L (l := app (u ++ [true]) blank) ht
    have h1' := step_L (l := app (u ++ [true]) (rep k W4 blank)) ht
    cases n with
    | zero => simp [TM.steps] at hd; subst hd; rw [h1] at hdh; cases hdh
    | succ m =>
      rw [TM.steps, h1] at hd
      dsimp only at hd
      have hG1 := good_steps hG (steps_one h1)
      rcases u with _ | ⟨a, u⟩
      · -- onto the leftmost 1
        refine halts_of_step h1' ?_
        rcases far_cases k (cons w (tail r)) s hs hG1 with ⟨hn, hn'⟩ | ⟨v, e, e', f0, fk, he, he'⟩
        · exact ⟨0, _, rfl, hn'⟩
        · obtain ⟨hle, hrest⟩ := halt_after f0 hd hdh
          refine (halts_iff_of_steps fk).2 (ih (m - 9) (by omega) e e' ?_ (good_steps hG1 f0) ⟨d, hrest, hdh⟩)
          rw [he, he']
          exact ⟨rfl, rfl, v, rfl, rfl⟩
      · refine halts_of_step h1' (ih m (by omega) _ _ ?_ hG1 ⟨d, hd, hdh⟩)
        exact ⟨rfl, rfl, u, rfl, rfl⟩

theorem bwd (k : Nat) : ∀ n (c c' : Config), Rel k c c' → Good c →
    (∃ d, TM.steps trans n c' = some d ∧ TM.step trans d = none) → Halts trans c := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro c c' hR hG hH
  obtain ⟨l, r, q⟩ := c
  obtain ⟨l', r', q'⟩ := c'
  obtain ⟨hq, hr, u, hl, hl'⟩ := hR
  simp only at hq hr hl hl'
  subst hq hr hl hl'
  obtain ⟨d, hd, hdh⟩ := hH
  rcases trans_cases q (r 0) with ht | ⟨w, s, ht⟩ | ⟨w, s, ht, hs⟩
  · exact ⟨0, _, rfl, step_none ht⟩
  · have h1 := step_R (l := app (u ++ [true]) blank) ht
    have h1' := step_R (l := app (u ++ [true]) (rep k W4 blank)) ht
    cases n with
    | zero => simp [TM.steps] at hd; subst hd; rw [h1'] at hdh; cases hdh
    | succ m =>
      rw [TM.steps, h1'] at hd
      dsimp only at hd
      refine halts_of_step h1 (ih m (by omega) _ _ ?_
        (good_steps hG (steps_one h1)) ⟨d, hd, hdh⟩)
      exact ⟨rfl, rfl, w :: u, rfl, rfl⟩
  · have h1 := step_L (l := app (u ++ [true]) blank) ht
    have h1' := step_L (l := app (u ++ [true]) (rep k W4 blank)) ht
    cases n with
    | zero => simp [TM.steps] at hd; subst hd; rw [h1'] at hdh; cases hdh
    | succ m =>
      rw [TM.steps, h1'] at hd
      dsimp only at hd
      have hG1 := good_steps hG (steps_one h1)
      rcases u with _ | ⟨a, u⟩
      · refine halts_of_step h1 ?_
        rcases far_cases k (cons w (tail r)) s hs hG1 with ⟨hn, hn'⟩ | ⟨v, e, e', f0, fk, he, he'⟩
        · exact ⟨0, _, rfl, hn⟩
        · obtain ⟨hle, hrest⟩ := halt_after fk hd hdh
          refine (halts_iff_of_steps f0).2 (ih (m - (8 * k + 9)) (by omega) e e' ?_ (good_steps hG1 f0) ⟨d, hrest, hdh⟩)
          rw [he, he']
          exact ⟨rfl, rfl, v, rfl, rfl⟩
      · refine halts_of_step h1 (ih m (by omega) _ _ ?_ hG1 ⟨d, hd, hdh⟩)
        exact ⟨rfl, rfl, u, rfl, rfl⟩

/-- **Lockstep.**  If `c'` is `c` with `k` more periods `1010` at the left end and the run from `c` never reaches a
`Bad` configuration, then `c` and `c'` both halt or both run forever. -/
theorem lockstep {k : Nat} {c c' : Config} (hR : Rel k c c') (hG : Good c) : Halts trans c ↔ Halts trans c' :=
  ⟨fun ⟨n, d, hd, hs⟩ => fwd k n c c' hR hG ⟨d, hd, hs⟩, fun ⟨n, d, hd, hs⟩ => bwd k n c c' hR hG ⟨d, hd, hs⟩⟩

/-! ## The four runs -/

/-- The run of the table from state D (the machine 1RB1RF_1LC0LB_1RE0LD_1LB0RF_0RA0RC_1RE---, mirrored) after 2
steps: `0^inf 1 B>1 0^inf`. -/
theorem at_D : TM.steps trans 2 (blankCfg .D) = some ⟨cons true blank, cons true blank, .B⟩ := rfl

/-- The run from state A (this machine) after 11 steps: the same with `1010` more on the left. -/
theorem at_A : TM.steps trans 11 (blankCfg .A) =
    some ⟨app [true, false, true, false, true] blank, cons true blank, .B⟩ := rfl

/-- The run from state B (1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---, mirrored) after 26 steps: `(1010)^2` more. -/
theorem at_B : TM.steps trans 26 (blankCfg .B) =
    some ⟨app [true, false, true, false, true, false, true, false, true] blank, cons true blank, .B⟩ := rfl

/-- The run from state E (1RB0LF_1RC0RB_1LD0RA_0LE0LC_1LB1LF_1LD---) after 50 steps: `(1010)^3` more. -/
theorem at_E : TM.steps trans 50 (blankCfg .E) =
    some ⟨app [true, false, true, false, true, false, true, false, true, false, true, false, true] blank,
      cons true blank, .B⟩ := rfl

/-- **The runs from A, B and E are the run from D with 4, 8 and 12 more cells in the first run**: each halts if and
only if the run from D halts, provided the run from D never reaches a `Bad` configuration. -/
theorem shared (h : Good (blankCfg .D)) :
    (Halts trans (blankCfg .A) ↔ Halts trans (blankCfg .D)) ∧
    (Halts trans (blankCfg .B) ↔ Halts trans (blankCfg .D)) ∧
    (Halts trans (blankCfg .E) ↔ Halts trans (blankCfg .D)) := by
  have g := good_steps h at_D
  have hD := halts_iff_of_steps at_D
  refine ⟨?_, ?_, ?_⟩
  · rw [halts_iff_of_steps at_A, hD]
    exact (lockstep (k := 1) (c := ⟨cons true blank, cons true blank, .B⟩)
      (c' := ⟨app [true, false, true, false, true] blank, cons true blank, .B⟩) ⟨rfl, rfl, [], rfl, rfl⟩ g).symm
  · rw [halts_iff_of_steps at_B, hD]
    exact (lockstep (k := 2) (c := ⟨cons true blank, cons true blank, .B⟩)
      (c' := ⟨app [true, false, true, false, true, false, true, false, true] blank, cons true blank, .B⟩) ⟨rfl, rfl, [], rfl, rfl⟩ g).symm
  · rw [halts_iff_of_steps at_E, hD]
    exact (lockstep (k := 3) (c := ⟨cons true blank, cons true blank, .B⟩)
      (c' := ⟨app [true, false, true, false, true, false, true, false, true, false, true, false, true] blank, cons true blank, .B⟩) ⟨rfl, rfl, [], rfl, rfl⟩ g).symm

/-! ## The other three machines

Their tables (`M40600.trans`, `M103746.trans`, `M131976.trans`, generated in `FarEnd.lean`), and the maps that turn
runs of this table into theirs. -/

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

theorem cons_tail (s : Tape) : cons (s 0) (tail s) = s := by
  funext n; cases n <;> rfl

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

/-- 1RB1RF_1LC0LB_1RE0LD_1LB0RF_0RA0RC_1RE--- is this table mirrored, with A, B, C, D, E, F renamed B, C, E, A, D, F. -/
def f40600 : St → M40600.St
  | .A => .B | .B => .C | .C => .E | .D => .A | .E => .D | .F => .F

/-- 1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB--- is this table mirrored, with A, B, C, D, E, F renamed D, A, B, C, E, F. -/
def f103746 : St → M103746.St
  | .A => .D | .B => .A | .C => .B | .D => .C | .E => .E | .F => .F

/-- 1RB0LF_1RC0RB_1LD0RA_0LE0LC_1LB1LF_1LD--- is this table with A, B, C, D, E, F renamed B, C, D, E, A, F. -/
def f131976 : St → M131976.St
  | .A => .B | .B => .C | .C => .D | .D => .E | .E => .A | .F => .F

theorem mir_blank {Q Q' : Type} (f : Q → Q') (q : Q) : mir f (blankCfg q) = blankCfg (f q) := by
  show (⟨tail blank, cons false blank, f q⟩ : Cfg Q') = ⟨blank, blank, f q⟩
  rw [TM.cons_false_blank]; rfl

theorem halts_40600 : Halts trans (blankCfg .D) ↔ Halts M40600.trans (blankCfg .A) := by
  have := halts_map trans M40600.trans (mir f40600)
    (step_mir trans M40600.trans f40600 (by intro q b; cases q <;> cases b <;> rfl)) (blankCfg .D)
  rw [mir_blank] at this; exact this

theorem halts_103746 : Halts trans (blankCfg .B) ↔ Halts M103746.trans (blankCfg .A) := by
  have := halts_map trans M103746.trans (mir f103746)
    (step_mir trans M103746.trans f103746 (by intro q b; cases q <;> cases b <;> rfl)) (blankCfg .B)
  rw [mir_blank] at this; exact this

theorem halts_131976 : Halts trans (blankCfg .E) ↔ Halts M131976.trans (blankCfg .A) :=
  halts_map trans M131976.trans (ren f131976)
    (step_ren trans M131976.trans f131976 (by intro q b; cases q <;> cases b <;> rfl)) (blankCfg .E)

/-- The condition, in the machine 1RB1RF_1LC0LB_1RE0LD_1LB0RF_0RA0RC_1RE--- itself: in its run from blank tape, the head
never reads a 1 in state B or C with blank tape to its right. -/
def Good40600 : Prop :=
  ∀ n (e : Cfg M40600.St), TM.steps M40600.trans n (blankCfg .A) = some e →
    ¬ (tail e.r = blank ∧ e.r 0 = true ∧ (e.st = M40600.St.B ∨ e.st = M40600.St.C))

theorem good_of_40600 (h : Good40600) : Good (blankCfg .D) := by
  intro n d hd hbad
  have hs : ∀ n (c : Config), TM.steps M40600.trans n (mir f40600 c) = (TM.steps trans n c).map (mir f40600) := by
    intro n
    induction n with
    | zero => intro c; rfl
    | succ n ih =>
      intro c
      simp only [TM.steps, step_mir trans M40600.trans f40600 (by intro q b; cases q <;> cases b <;> rfl) c]
      rcases TM.step trans c with _ | c'
      · rfl
      · exact ih c'
  have e1 := hs n (blankCfg .D)
  rw [mir_blank, hd] at e1
  obtain ⟨hl, hr, hq⟩ := hbad
  refine h n _ e1 ⟨hl, hr, ?_⟩
  show f40600 d.st = .B ∨ f40600 d.st = .C
  rcases hq with hq | hq <;> rw [hq]
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- **One halting question for four machines.**  If, in the run of 1RB1RF_1LC0LB_1RE0LD_1LB0RF_0RA0RC_1RE--- from
blank tape, the head never reads a 1 in state B or C with blank tape to its right, then
1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---, 1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB--- and
1RB0LF_1RC0RB_1LD0RA_0LE0LC_1LB1LF_1LD--- each halt from blank tape if and only if
1RB1RF_1LC0LB_1RE0LD_1LB0RF_0RA0RC_1RE--- does. -/
theorem one_question (h : Good40600) :
    (Halts trans (blankCfg .A) ↔ Halts M40600.trans (blankCfg .A)) ∧
    (Halts M103746.trans (blankCfg .A) ↔ Halts M40600.trans (blankCfg .A)) ∧
    (Halts M131976.trans (blankCfg .A) ↔ Halts M40600.trans (blankCfg .A)) := by
  obtain ⟨hA, hB, hE⟩ := shared (good_of_40600 h)
  exact ⟨hA.trans halts_40600, halts_103746.symm.trans (hB.trans halts_40600),
    halts_131976.symm.trans (hE.trans halts_40600)⟩

/-- **Three of the four, on this machine's own condition.**  If the run of this machine (from A) never reaches a `Bad`
configuration, 1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB--- and 1RB0LF_1RC0RB_1LD0RA_0LE0LC_1LB1LF_1LD--- each halt
from blank tape if and only if this machine does.  (The first run of this machine is that of the run from D plus 4
cells for as long as `one_question`'s condition holds, so this condition is the weaker one.) -/
theorem three_questions (h : Good (blankCfg .A)) :
    (Halts M103746.trans (blankCfg .A) ↔ Halts trans (blankCfg .A)) ∧
    (Halts M131976.trans (blankCfg .A) ↔ Halts trans (blankCfg .A)) := by
  have g := good_steps h at_A
  have hA := halts_iff_of_steps at_A
  refine ⟨?_, ?_⟩
  · rw [← halts_103746, halts_iff_of_steps at_B, hA]
    exact (lockstep (k := 1) (c := ⟨app [true, false, true, false, true] blank, cons true blank, .B⟩)
      (c' := ⟨app [true, false, true, false, true, false, true, false, true] blank, cons true blank, .B⟩)
      ⟨rfl, rfl, [true, false, true, false], rfl, rfl⟩ g).symm
  · rw [← halts_131976, halts_iff_of_steps at_E, hA]
    exact (lockstep (k := 2) (c := ⟨app [true, false, true, false, true] blank, cons true blank, .B⟩)
      (c' := ⟨app [true, false, true, false, true, false, true, false, true, false, true, false, true] blank,
        cons true blank, .B⟩) ⟨rfl, rfl, [true, false, true, false], rfl, rfl⟩ g).symm

end H32883
