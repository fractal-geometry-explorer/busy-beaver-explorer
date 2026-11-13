import TM

/-!
# The 3-cell-block family of G12 (3a): one machine, a shadow of it, and a second start

The three holdouts
* `M1 = 1RB1LB_1RC1LE_1RD0LF_0LA0RD_---1LD_0LD1LF` (bbchallenge 111363),
* `T  = 1RB1LE_1RC1LD_1RD0LF_0LA0RD_---1LB_0LD1LF` (bbchallenge 51101),
* `M3 = 1RB1LC_1RC0LF_0LD0RC_1RA1LE_---1LA_0LC1LF` (bbchallenge 72232)
are tied together here.

* `M3` is `T` with its states renamed (A→D, B→A, C→B, D→C, E→E, F→F), every transition included, so the run of
  `M3` from blank tape is the run of `T` started in state B on blank tape (`m3_iff`).
* `M1` and `T` differ in the 1-transitions of A, B and E, all of which write 1 and move left.  The seven-state machine
  `S` below is the part they share: it is `T` (and `M1`) with the state B split into B (entered from A on a 0) and
  E (entered from A on a 1), and halts where the two machines could part.  Every step `S` makes, `M1` and `T` make
  too, on the same tape (`shadow`); B entered from A0 always reads a 0 (`star_good`), so `S` can only stop at E0 or
  G0, and there exactly one of `M1`, `T` halts (`deviation`).  Hence `S` halts iff `M1` or `T` halts
  (`star_halts_iff`), and if neither halts the two make the same run, step for step (`same_run`).

This file is the same in the three machines' folders (`py/family.py check` in the folder of `T` compares the
copies); each folder's `Link.lean` ties its own `Machine.lean` to the table here.
-/

namespace G12Blocks3

open TM

/-- Rename the state of a configuration. -/
def cmap {Q₁ Q₂ : Type} (f : Q₁ → Q₂) (c : Cfg Q₁) : Cfg Q₂ := ⟨c.l, c.r, f c.st⟩

section Sim
variable {Q₁ Q₂ : Type} (δ₁ : Q₁ → Bool → Option (Bool × Dir × Q₁)) (δ₂ : Q₂ → Bool → Option (Bool × Dir × Q₂))
  (f : Q₁ → Q₂)

/-- One-way simulation: every transition of `δ₁` is a transition of `δ₂` on the renamed states. -/
def Sims : Prop := ∀ q y w d q', δ₁ q y = some (w, d, q') → δ₂ (f q) y = some (w, d, f q')

/-- Exact renaming: `δ₂` on renamed states is `δ₁`, halts included. -/
def Renames : Prop := ∀ q y, δ₂ (f q) y = (δ₁ q y).map (fun t => (t.1, t.2.1, f t.2.2))

theorem sim_step (h : Sims δ₁ δ₂ f) {c c' : Cfg Q₁} (hs : step δ₁ c = some c') :
    step δ₂ (cmap f c) = some (cmap f c') := by
  obtain ⟨l, r, q⟩ := c
  unfold step at hs ⊢
  simp only [cmap] at hs ⊢
  cases hq : δ₁ q (r 0) with
  | none => rw [hq] at hs; cases hs
  | some t =>
    obtain ⟨w, d, q'⟩ := t
    rw [h q (r 0) w d q' hq]
    rw [hq] at hs
    cases d <;> (simp only [Option.some.injEq] at hs; subst hs; rfl)

theorem sim_steps (h : Sims δ₁ δ₂ f) :
    ∀ (n : Nat) {c c' : Cfg Q₁}, steps δ₁ n c = some c' → steps δ₂ n (cmap f c) = some (cmap f c')
  | 0, c, c', hc => by simp [steps] at hc; subst hc; rfl
  | n + 1, c, c', hc => by
    cases hs : step δ₁ c with
    | none => simp [steps, hs] at hc
    | some d =>
      rw [steps_succ_of_step δ₁ n hs] at hc
      rw [steps_succ_of_step δ₂ n (sim_step δ₁ δ₂ f h hs)]
      exact sim_steps h n hc

theorem ren_step (h : Renames δ₁ δ₂ f) (c : Cfg Q₁) : step δ₂ (cmap f c) = (step δ₁ c).map (cmap f) := by
  obtain ⟨l, r, q⟩ := c
  unfold step
  simp only [cmap]
  rw [h q (r 0)]
  cases hq : δ₁ q (r 0) with
  | none => rfl
  | some t =>
    obtain ⟨w, d, q'⟩ := t
    cases d <;> rfl

theorem ren_steps (h : Renames δ₁ δ₂ f) :
    ∀ (n : Nat) (c : Cfg Q₁), steps δ₂ n (cmap f c) = (steps δ₁ n c).map (cmap f)
  | 0, c => rfl
  | n + 1, c => by
    cases hs : step δ₁ c with
    | none =>
      have h2 : step δ₂ (cmap f c) = none := by rw [ren_step δ₁ δ₂ f h, hs]; rfl
      simp [steps, hs, h2]
    | some d =>
      have h2 : step δ₂ (cmap f c) = some (cmap f d) := by rw [ren_step δ₁ δ₂ f h, hs]; rfl
      rw [steps_succ_of_step δ₁ n hs, steps_succ_of_step δ₂ n h2]
      exact ren_steps h n d

theorem ren_halts (h : Renames δ₁ δ₂ f) (c : Cfg Q₁) : Halts δ₂ (cmap f c) ↔ Halts δ₁ c := by
  constructor
  · rintro ⟨n, c'', h1, h2⟩
    rw [ren_steps δ₁ δ₂ f h] at h1
    cases e : steps δ₁ n c with
    | none => rw [e] at h1; cases h1
    | some c' =>
      rw [e] at h1
      simp only [Option.map_some, Option.some.injEq] at h1
      subst h1
      refine ⟨n, c', e, ?_⟩
      rw [ren_step δ₁ δ₂ f h] at h2
      cases e2 : step δ₁ c' with
      | none => rfl
      | some _ => rw [e2] at h2; cases h2
  · rintro ⟨n, c', h1, h2⟩
    refine ⟨n, cmap f c', ?_, ?_⟩
    · rw [ren_steps δ₁ δ₂ f h, h1]; rfl
    · rw [ren_step δ₁ δ₂ f h, h2]; rfl

end Sim

/-- A run that is undefined at some length halts on the way. -/
theorem halts_of_steps_none {Q : Type} (δ : Q → Bool → Option (Bool × Dir × Q)) :
    ∀ (n : Nat) (c : Cfg Q), steps δ n c = none → Halts δ c
  | 0, c, h => by simp [steps] at h
  | n + 1, c, h => by
    cases hs : step δ c with
    | none => exact ⟨0, c, rfl, hs⟩
    | some d =>
      rw [steps_succ_of_step δ n hs] at h
      obtain ⟨m, c', h1, h2⟩ := halts_of_steps_none δ n d h
      exact ⟨m + 1, c', by rw [steps_succ_of_step δ m hs]; exact h1, h2⟩

theorem forall_of_not_halts {Q : Type} (δ : Q → Bool → Option (Bool × Dir × Q)) {c : Cfg Q} (h : ¬ Halts δ c)
    (n : Nat) : ∃ c', steps δ n c = some c' := by
  cases e : steps δ n c with
  | none => exact absurd (halts_of_steps_none δ n c e) h
  | some c' => exact ⟨c', rfl⟩

/-- Six states, for `T`, `M1` and `M3`. -/
inductive St6 where
  | A | B | C | D | E | F
  deriving DecidableEq, Repr

/-- Seven states, for the shared part `S`. -/
inductive St7 where
  | A | B | C | D | E | F | G
  deriving DecidableEq, Repr

/-- `T = 1RB1LE_1RC1LD_1RD0LF_0LA0RD_---1LB_0LD1LF`. -/
def tT : St6 → Bool → Option (Bool × Dir × St6)
  | .A, false => some (true, .R, .B)
  | .A, true => some (true, .L, .E)
  | .B, false => some (true, .R, .C)
  | .B, true => some (true, .L, .D)
  | .C, false => some (true, .R, .D)
  | .C, true => some (false, .L, .F)
  | .D, false => some (false, .L, .A)
  | .D, true => some (false, .R, .D)
  | .E, false => none
  | .E, true => some (true, .L, .B)
  | .F, false => some (false, .L, .D)
  | .F, true => some (true, .L, .F)

/-- `M1 = 1RB1LB_1RC1LE_1RD0LF_0LA0RD_---1LD_0LD1LF`. -/
def tM1 : St6 → Bool → Option (Bool × Dir × St6)
  | .A, false => some (true, .R, .B)
  | .A, true => some (true, .L, .B)
  | .B, false => some (true, .R, .C)
  | .B, true => some (true, .L, .E)
  | .C, false => some (true, .R, .D)
  | .C, true => some (false, .L, .F)
  | .D, false => some (false, .L, .A)
  | .D, true => some (false, .R, .D)
  | .E, false => none
  | .E, true => some (true, .L, .D)
  | .F, false => some (false, .L, .D)
  | .F, true => some (true, .L, .F)

/-- `M3 = 1RB1LC_1RC0LF_0LD0RC_1RA1LE_---1LA_0LC1LF`. -/
def tM3 : St6 → Bool → Option (Bool × Dir × St6)
  | .A, false => some (true, .R, .B)
  | .A, true => some (true, .L, .C)
  | .B, false => some (true, .R, .C)
  | .B, true => some (false, .L, .F)
  | .C, false => some (false, .L, .D)
  | .C, true => some (false, .R, .C)
  | .D, false => some (true, .R, .A)
  | .D, true => some (true, .L, .E)
  | .E, false => none
  | .E, true => some (true, .L, .A)
  | .F, false => some (false, .L, .C)
  | .F, true => some (true, .L, .F)

/-- `S = 1RB1LE_1RC---_1RD0LF_0LA0RD_---1LG_0LD1LF_---1LD`: E is "B entered from A1", G is "the state after E1". -/
def tS : St7 → Bool → Option (Bool × Dir × St7)
  | .A, false => some (true, .R, .B)
  | .A, true => some (true, .L, .E)
  | .B, false => some (true, .R, .C)
  | .B, true => none
  | .C, false => some (true, .R, .D)
  | .C, true => some (false, .L, .F)
  | .D, false => some (false, .L, .A)
  | .D, true => some (false, .R, .D)
  | .E, false => none
  | .E, true => some (true, .L, .G)
  | .F, false => some (false, .L, .D)
  | .F, true => some (true, .L, .F)
  | .G, false => none
  | .G, true => some (true, .L, .D)

/-- `S` as `M1`: E is M1's B, G is M1's E. -/
def phi1 : St7 → St6
  | .A => .A | .B => .B | .C => .C | .D => .D | .E => .B | .F => .F | .G => .E

/-- `S` as `T`: G is T's B. -/
def phi2 : St7 → St6
  | .A => .A | .B => .B | .C => .C | .D => .D | .E => .E | .F => .F | .G => .B

/-- `T` renamed into `M3`. -/
def psi : St6 → St6
  | .A => .D | .B => .A | .C => .B | .D => .C | .E => .E | .F => .F

theorem sims1 : Sims tS tM1 phi1 := by
  intro q y w d q' h; cases q <;> cases y <;> simp [tS] at h <;> obtain ⟨rfl, rfl, rfl⟩ := h <;> rfl

theorem sims2 : Sims tS tT phi2 := by
  intro q y w d q' h; cases q <;> cases y <;> simp [tS] at h <;> obtain ⟨rfl, rfl, rfl⟩ := h <;> rfl

theorem renames3 : Renames tT tM3 psi := by
  intro q y; cases q <;> cases y <;> rfl

/-- `M3` from blank tape is `T` started in state B on blank tape. -/
theorem m3_iff : Halts tM3 (blankCfg .A) ↔ Halts tT (blankCfg .B) :=
  ren_halts tT tM3 psi renames3 (blankCfg .B)

/-- The invariant of `S`: in state A the cell right of the head is 0 (A is entered only by D0 = 0LA), and in
state B the head reads 0 (B is entered only by A0 = 1RB). -/
def Good (c : Cfg St7) : Prop := (c.st = .A → c.r 1 = false) ∧ (c.st = .B → c.r 0 = false)

theorem good_step {c c' : Cfg St7} (hc : Good c) (hs : step tS c = some c') : Good c' := by
  obtain ⟨l, r, q⟩ := c
  obtain ⟨hA, hB⟩ := hc
  simp only at hA hB
  unfold step at hs
  simp only at hs
  cases q <;> cases h0 : r 0 <;> simp [tS, h0] at hs <;> subst hs <;> simp [Good, cons, tail] <;>
    simp_all

theorem good_steps : ∀ (n : Nat) {c c' : Cfg St7}, Good c → steps tS n c = some c' → Good c'
  | 0, c, c', hc, h => by simp [steps] at h; exact h ▸ hc
  | n + 1, c, c', hc, h => by
    cases hs : step tS c with
    | none => simp [steps, hs] at h
    | some d =>
      rw [steps_succ_of_step tS n hs] at h
      exact good_steps n (good_step hc hs) h

/-- Every configuration of the run of `S` from blank tape satisfies `Good`. -/
theorem star_good {n : Nat} {c : Cfg St7} (h : steps tS n (blankCfg .A) = some c) : Good c :=
  good_steps n ⟨fun _ => rfl, fun h => by cases h⟩ h

/-- Where `S` can stop: B1 never happens, so it stops on E0 or on G0. -/
theorem star_halt {n : Nat} {c : Cfg St7} (h : steps tS n (blankCfg .A) = some c) (hs : step tS c = none) :
    (c.st = .E ∨ c.st = .G) ∧ c.r 0 = false := by
  have hg := star_good h
  obtain ⟨l, r, q⟩ := c
  obtain ⟨_, hB⟩ := hg
  unfold step at hs
  simp only at hs hB ⊢
  cases q <;> cases h0 : r 0 <;> simp [tS, h0] at hs <;> simp_all

/-- As long as `S` runs, `M1` and `T` make the same steps on the same tape. -/
theorem shadow {n : Nat} {c : Cfg St7} (h : steps tS n (blankCfg .A) = some c) :
    steps tM1 n (blankCfg .A) = some (cmap phi1 c) ∧ steps tT n (blankCfg .A) = some (cmap phi2 c) :=
  ⟨sim_steps tS tM1 phi1 sims1 n h, sim_steps tS tT phi2 sims2 n h⟩

/-- Where `S` stops, exactly one of `M1` and `T` halts: on E0 `T` halts and `M1` moves on (B0 = 1RC); on G0 `M1`
halts and `T` moves on (B0 = 1RC). -/
theorem deviation {n : Nat} {c : Cfg St7} (h : steps tS n (blankCfg .A) = some c) (hs : step tS c = none) :
    (step tT (cmap phi2 c) = none ∧ (step tM1 (cmap phi1 c)).isSome) ∨
    (step tM1 (cmap phi1 c) = none ∧ (step tT (cmap phi2 c)).isSome) := by
  obtain ⟨hq, h0⟩ := star_halt h hs
  obtain ⟨l, r, q⟩ := c
  simp only at hq h0
  rcases hq with rfl | rfl
  · left; simp [step, cmap, phi1, phi2, tT, tM1, h0]
  · right; simp [step, cmap, phi1, phi2, tT, tM1, h0]

theorem star_halts_iff : Halts tS (blankCfg .A) ↔ Halts tM1 (blankCfg .A) ∨ Halts tT (blankCfg .A) := by
  constructor
  · rintro ⟨n, c, h1, h2⟩
    have hsh := shadow h1
    rcases deviation h1 h2 with ⟨hT, _⟩ | ⟨hM, _⟩
    · exact Or.inr ⟨n, _, hsh.2, hT⟩
    · exact Or.inl ⟨n, _, hsh.1, hM⟩
  · intro hor
    refine Classical.byContradiction fun hn => ?_
    have hall := forall_of_not_halts tS hn
    rcases hor with hM | hT
    · exact not_halts_of_forall tM1 (fun n => by
        obtain ⟨c, hc⟩ := hall n; exact ⟨_, (shadow hc).1⟩) hM
    · exact not_halts_of_forall tT (fun n => by
        obtain ⟨c, hc⟩ := hall n; exact ⟨_, (shadow hc).2⟩) hT

/-- If `S` never halts, neither `M1` nor `T` halts, and at every step they have the same tape and head, in states
related by `phi1`/`phi2`. -/
theorem same_run (hn : ¬ Halts tS (blankCfg .A)) (n : Nat) :
    ∃ c, steps tM1 n (blankCfg .A) = some (cmap phi1 c) ∧ steps tT n (blankCfg .A) = some (cmap phi2 c) := by
  obtain ⟨c, hc⟩ := forall_of_not_halts tS hn n
  exact ⟨c, shadow hc⟩

end G12Blocks3
