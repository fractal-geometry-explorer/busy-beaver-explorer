import TM.Basic

/-!
# Two machines that differ only at rare moments

`δ₁` and `δ₂` are two machines on one state type.  They make the same step at every *synchronised* configuration
(`Syn`) that is not a *segment start* (`Seg`).  From a segment start the two machines may take different paths, but
unless the configuration is *bad* (`Bad`) they meet again: after `n₁ + 1` steps of `δ₁` and `n₂ + 1` steps of `δ₂`
both are in the same synchronised configuration, or both halt.  `Resync` collects these three hypotheses, each a
statement about single configurations that a finite computation can check.

The main result, `halt_together`: from a synchronised start `c0`,

* the run of `δ₁` never meets a bad configuration if and only if the run of `δ₂` never does (`NoBad`), and
* if it never does, `δ₁` halts from `c0` if and only if `δ₂` halts from `c0`.

So two such machines have one open question between them: whether the run reaches a bad configuration.  The proof
follows the run of `δ₂` and keeps, at each of its configurations, a configuration of the run of `δ₁` that it is
synchronised with, or the start of the segment it is crossing (`Rep`).  Kernel only, no `native_decide`.
-/

namespace TM

variable {Q : Type}

/-- One more step at the end of a run. -/
theorem steps_succ_bind (δ : Q → Bool → Option (Bool × Dir × Q)) :
    ∀ (n : Nat) (c : Cfg Q), steps δ (n + 1) c = (steps δ n c).bind (step δ) := by
  intro n
  induction n with
  | zero =>
    intro c
    cases h : step δ c with
    | none => simp [steps, h]
    | some d => simp [steps, h]
  | succ n ih =>
    intro c
    cases h : step δ c with
    | none => simp [steps, h]
    | some d =>
      rw [steps_succ_of_step δ _ h, steps_succ_of_step δ _ h]
      exact ih d

theorem steps_one' (δ : Q → Bool → Option (Bool × Dir × Q)) {c d : Cfg Q} (h : step δ c = some d) :
    steps δ 1 c = some d := by
  simp [steps, h]

/-- A run of `n + 1` steps starts with a step. -/
theorem step_of_steps_succ (δ : Q → Bool → Option (Bool × Dir × Q)) {n : Nat} {c e : Cfg Q}
    (h : steps δ (n + 1) c = some e) : ∃ d, step δ c = some d ∧ steps δ n d = some e := by
  cases hs : step δ c with
  | none => simp [steps, hs] at h
  | some d => exact ⟨d, rfl, by rw [steps_succ_of_step δ _ hs] at h; exact h⟩

/-- Every stream is a first cell in front of a stream. -/
theorem tape_cell (s : Tape) : ∃ b t, s = cons b t :=
  ⟨s 0, tail s, by funext n; cases n <;> rfl⟩

section

variable (δ₁ δ₂ : Q → Bool → Option (Bool × Dir × Q)) (Syn Seg Bad : Cfg Q → Prop)

/-- `c` is a configuration of the run from `c0`. -/
def Reach (δ : Q → Bool → Option (Bool × Dir × Q)) (c0 c : Cfg Q) : Prop := ∃ n, steps δ n c0 = some c

/-- The run from `c0` never meets a bad configuration. -/
def NoBad (δ : Q → Bool → Option (Bool × Dir × Q)) (Bad : Cfg Q → Prop) (c0 : Cfg Q) : Prop :=
  ∀ n e, steps δ n c0 = some e → ¬ Bad e

/-- The configurations after 1, ..., n steps from `c` are not bad. -/
def Clean (δ : Q → Bool → Option (Bool × Dir × Q)) (Bad : Cfg Q → Prop) (n : Nat) (c : Cfg Q) : Prop :=
  ∀ j e, j < n → steps δ (j + 1) c = some e → ¬ Bad e

/-- How the segment from `c` ends: both machines reach one synchronised configuration, or both halt. -/
def SegOK (c : Cfg Q) : Prop :=
  ∃ n₁ n₂, Clean δ₁ Bad n₁ c ∧ Clean δ₂ Bad n₂ c ∧
    ((∃ d, Syn d ∧ steps δ₁ (n₁ + 1) c = some d ∧ steps δ₂ (n₂ + 1) c = some d) ∨
     ((∃ h, steps δ₁ n₁ c = some h ∧ step δ₁ h = none) ∧ (∃ h, steps δ₂ n₂ c = some h ∧ step δ₂ h = none)))

/-- The hypotheses: agreement off the segment starts, no halt there, and every good segment closes. -/
structure Resync : Prop where
  agree : ∀ c, Syn c → ¬ Seg c → step δ₁ c = step δ₂ c
  live : ∀ c, Syn c → ¬ Seg c → ∃ d, step δ₁ c = some d ∧ Syn d
  seg : ∀ c, Syn c → Seg c → ¬ Bad c → SegOK δ₁ δ₂ Syn Bad c

/-- What the followed run of `δ₂` keeps: a synchronised configuration `d` of the run of `δ₁`, and `e` is `d` or
lies inside the segment that starts at `d`. -/
def Rep (c0 e : Cfg Q) : Prop :=
  ∃ d, Syn d ∧ Reach δ₁ c0 d ∧ (e = d ∨ (Seg d ∧ ∃ n₁ n₂, Clean δ₁ Bad n₁ d ∧ Clean δ₂ Bad n₂ d ∧
    ((∃ d', Syn d' ∧ steps δ₁ (n₁ + 1) d = some d' ∧ steps δ₂ (n₂ + 1) d = some d') ∨
     ((∃ h, steps δ₁ n₁ d = some h ∧ step δ₁ h = none) ∧ (∃ h, steps δ₂ n₂ d = some h ∧ step δ₂ h = none))) ∧
    ∃ k, k < n₂ ∧ steps δ₂ (k + 1) d = some e))

variable {δ₁ δ₂ Syn Seg Bad}

theorem SegOK.symm {c : Cfg Q} (h : SegOK δ₁ δ₂ Syn Bad c) : SegOK δ₂ δ₁ Syn Bad c := by
  obtain ⟨n₁, n₂, h₁, h₂, h₃⟩ := h
  refine ⟨n₂, n₁, h₂, h₁, ?_⟩
  rcases h₃ with ⟨d, hd, e₁, e₂⟩ | ⟨a, b⟩
  · exact Or.inl ⟨d, hd, e₂, e₁⟩
  · exact Or.inr ⟨b, a⟩

theorem Resync.symm (h : Resync δ₁ δ₂ Syn Seg Bad) : Resync δ₂ δ₁ Syn Seg Bad where
  agree c hs hg := (h.agree c hs hg).symm
  live c hs hg := by rw [← h.agree c hs hg]; exact h.live c hs hg
  seg c hs hg hb := (h.seg c hs hg hb).symm

theorem reach_steps {δ : Q → Bool → Option (Bool × Dir × Q)} {c0 d d' : Cfg Q} {n : Nat}
    (h : Reach δ c0 d) (h' : steps δ n d = some d') : Reach δ c0 d' := by
  obtain ⟨m, hm⟩ := h
  exact ⟨m + n, steps_seq δ hm h'⟩

theorem rep_notbad {c0 e : Cfg Q} (hnb : NoBad δ₁ Bad c0) (h : Rep δ₁ δ₂ Syn Seg Bad c0 e) :
    ¬ Bad e := by
  obtain ⟨d, _, ⟨m, hm⟩, h | ⟨_, n₁, n₂, _, h₂, _, k, hk, he⟩⟩ := h
  · subst h; exact hnb m _ hm
  · exact h₂ k e hk he

/-- A halt of `δ₂` at a followed configuration is a halt of `δ₁`. -/
theorem rep_halt {c0 e : Cfg Q} (hR : Resync δ₁ δ₂ Syn Seg Bad) (hnb : NoBad δ₁ Bad c0)
    (h : Rep δ₁ δ₂ Syn Seg Bad c0 e) (hs : step δ₂ e = none) : Halts δ₁ c0 := by
  obtain ⟨d, hd, hr, h | ⟨hg, n₁, n₂, _, _, ho, k, hk, he⟩⟩ := h
  · subst h
    by_cases hg : Seg e
    · obtain ⟨m, hm⟩ := hr
      obtain ⟨n₁, n₂, _, _, ho⟩ := hR.seg e hd hg (hnb m e hm)
      rcases ho with ⟨d', _, _, e₂⟩ | ⟨⟨h₁, a, b⟩, _⟩
      · obtain ⟨x, hx, _⟩ := step_of_steps_succ δ₂ e₂
        rw [hs] at hx; cases hx
      · exact ⟨m + n₁, h₁, steps_seq δ₁ hm a, b⟩
    · obtain ⟨x, hx, _⟩ := hR.live e hd hg
      rw [hR.agree e hd hg, hs] at hx; cases hx
  · rcases ho with ⟨d', _, _, e₂⟩ | ⟨⟨h₁, a, b⟩, _⟩
    · have e3 : steps δ₂ ((k + 2) + (n₂ - (k + 1))) d = some d' := by
        rw [show (k + 2) + (n₂ - (k + 1)) = n₂ + 1 by omega]; exact e₂
      obtain ⟨y, hy⟩ := steps_le δ₂ e3
      rw [steps_succ_bind, he] at hy
      simp [hs] at hy
    · obtain ⟨m, hm⟩ := hr
      exact ⟨m + n₁, h₁, steps_seq δ₁ hm a, b⟩

/-- A step of `δ₂` from a followed configuration leads to a followed configuration. -/
theorem rep_step {c0 e e' : Cfg Q} (hR : Resync δ₁ δ₂ Syn Seg Bad) (hnb : NoBad δ₁ Bad c0)
    (h : Rep δ₁ δ₂ Syn Seg Bad c0 e) (hs : step δ₂ e = some e') :
    Rep δ₁ δ₂ Syn Seg Bad c0 e' := by
  obtain ⟨d, hd, hr, h | ⟨hg, n₁, n₂, c₁, c₂, ho, k, hk, he⟩⟩ := h
  · subst h
    by_cases hg : Seg e
    · obtain ⟨m, hm⟩ := hr
      obtain ⟨n₁, n₂, c₁, c₂, ho⟩ := hR.seg e hd hg (hnb m e hm)
      cases n₂ with
      | zero =>
        rcases ho with ⟨d', hd', e₁, e₂⟩ | ⟨_, ⟨x, hx, hx'⟩⟩
        · rw [steps_one' δ₂ hs] at e₂
          cases e₂
          exact ⟨e', hd', reach_steps ⟨m, hm⟩ e₁, Or.inl rfl⟩
        · simp at hx; subst hx; rw [hs] at hx'; cases hx'
      | succ n₂ =>
        exact ⟨e, hd, ⟨m, hm⟩, Or.inr ⟨hg, n₁, n₂ + 1, c₁, c₂, ho, 0, by omega, steps_one' δ₂ hs⟩⟩
    · obtain ⟨x, hx, hx'⟩ := hR.live e hd hg
      rw [hR.agree e hd hg, hs] at hx
      cases hx
      exact ⟨e', hx', reach_steps hr (steps_one' δ₁ (by rw [hR.agree e hd hg]; exact hs)), Or.inl rfl⟩
  · have hk2 : steps δ₂ (k + 2) d = some e' := by rw [steps_succ_bind, he]; exact hs
    by_cases hlt : k + 1 < n₂
    · exact ⟨d, hd, hr, Or.inr ⟨hg, n₁, n₂, c₁, c₂, ho, k + 1, hlt, hk2⟩⟩
    · have hkn : n₂ = k + 1 := by omega
      subst hkn
      rcases ho with ⟨d', hd', e₁, e₂⟩ | ⟨_, ⟨x, hx, hx'⟩⟩
      · rw [hk2] at e₂; cases e₂
        exact ⟨e', hd', reach_steps hr e₁, Or.inl rfl⟩
      · rw [he] at hx; cases hx; rw [hs] at hx'; cases hx'

/-- Following the run of `δ₂`: every configuration of it is followed. -/
theorem track (hR : Resync δ₁ δ₂ Syn Seg Bad) {c0 : Cfg Q} (h0 : Syn c0) (hnb : NoBad δ₁ Bad c0) :
    ∀ n e, steps δ₂ n c0 = some e → Rep δ₁ δ₂ Syn Seg Bad c0 e := by
  intro n
  induction n with
  | zero => intro e he; cases he; exact ⟨c0, h0, ⟨0, rfl⟩, Or.inl rfl⟩
  | succ n ih =>
    intro e he
    rw [steps_succ_bind] at he
    cases hn : steps δ₂ n c0 with
    | none => rw [hn] at he; cases he
    | some x =>
      rw [hn] at he
      exact rep_step hR hnb (ih x hn) he

theorem nobad_of (hR : Resync δ₁ δ₂ Syn Seg Bad) {c0 : Cfg Q} (h0 : Syn c0) (hnb : NoBad δ₁ Bad c0) :
    NoBad δ₂ Bad c0 :=
  fun n e he => rep_notbad hnb (track hR h0 hnb n e he)

theorem halts_of (hR : Resync δ₁ δ₂ Syn Seg Bad) {c0 : Cfg Q} (h0 : Syn c0) (hnb : NoBad δ₁ Bad c0) :
    Halts δ₂ c0 → Halts δ₁ c0 := by
  rintro ⟨n, e, he, hs⟩
  exact rep_halt hR hnb (track hR h0 hnb n e he) hs

/-- **The two machines have one question.**  Their runs from `c0` meet a bad configuration together, and if they
never do, the machines halt together. -/
theorem halt_together (hR : Resync δ₁ δ₂ Syn Seg Bad) {c0 : Cfg Q} (h0 : Syn c0) :
    (NoBad δ₁ Bad c0 ↔ NoBad δ₂ Bad c0) ∧ (NoBad δ₁ Bad c0 → (Halts δ₁ c0 ↔ Halts δ₂ c0)) :=
  ⟨⟨nobad_of hR h0, nobad_of hR.symm h0⟩,
   fun hnb => ⟨halts_of hR.symm h0 (nobad_of hR h0 hnb), halts_of hR h0 hnb⟩⟩

/-! ## Checking a segment by computation -/

/-- `true` when the configurations after 1, ..., n steps from `c` all pass `g` (a halt ends the check). -/
def chk (δ : Q → Bool → Option (Bool × Dir × Q)) (g : Cfg Q → Bool) : Nat → Cfg Q → Bool
  | 0, _ => true
  | n + 1, c =>
    match step δ c with
    | none => true
    | some d => g d && chk δ g n d

theorem clean_of_chk (δ : Q → Bool → Option (Bool × Dir × Q)) (g : Cfg Q → Bool)
    (hg : ∀ e, g e = true → ¬ Bad e) : ∀ n c, chk δ g n c = true → Clean δ Bad n c := by
  intro n
  induction n with
  | zero => intro c _ j e hj; omega
  | succ n ih =>
    intro c hc j e hj he
    obtain ⟨d, hd, hde⟩ := step_of_steps_succ δ he
    simp only [chk, hd, Bool.and_eq_true] at hc
    cases j with
    | zero => simp at hde; subst hde; exact hg _ hc.1
    | succ j => exact ih d hc.2 j e (by omega) hde

end

end TM
