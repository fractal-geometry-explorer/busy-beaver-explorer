import Macro

/-!
# Odd numbers are the only danger

Call a macro configuration *even* when every stack entry is even, every segment `m` of the word is even and every gap
`g` is odd (in the two-stack form of `notes/LAB_NOTES.md`, where `n = g − 1`: every number even); in state B the head
gap `h` must also be even and at least 2.  The last segment `mt` may be anything.

* `even_not_stuck`: an even configuration is never stuck.
* `even_step`: its successor is even again, unless the step is B with an empty stack (the left end of the tape, where
  B takes a segment 1 from below the stack).
* `even_run`: so an even configuration runs on for as long as it does not reach B with an empty stack, for all values
  of all parameters.

So odd numbers are born only at the left end of the tape, the last segment never matters, and the macro machine (and
the Turing machine) can get stuck only through odd numbers that came from the left end.  This is the part of the
picture in the notes that is a theorem; how the odd numbers then move (they hop from a frame's gap to its caller's
value, one flip at a time) is what a proof of non-halting would still have to control.  Kernel only.
-/

namespace BB6e

/-- Every stack entry even. -/
def EvS (S : List Nat) : Prop := ∀ s ∈ S, s % 2 = 0

/-- Every segment even and every gap odd. -/
def EvW (ws : List (Nat × Nat)) : Prop := ∀ p ∈ ws, p.1 % 2 = 0 ∧ p.2 % 2 = 1

/-- Even configurations (the last segment is free). -/
def Even : MC → Prop
  | .F S ws _ => EvS S ∧ EvW ws
  | .B S h ws _ => EvS S ∧ h % 2 = 0 ∧ 2 ≤ h ∧ EvW ws
  | .Binf _ => False

/-- B with an empty stack: the one step that reads below the stack. -/
def AtBottom : MC → Prop
  | .B [] _ _ _ => True
  | _ => False

theorem evS_cons {s : Nat} {S : List Nat} : EvS (s :: S) ↔ s % 2 = 0 ∧ EvS S := by
  simp [EvS]

theorem evW_cons {p : Nat × Nat} {ws : List (Nat × Nat)} : EvW (p :: ws) ↔ (p.1 % 2 = 0 ∧ p.2 % 2 = 1) ∧ EvW ws := by
  simp [EvW]

/-- The pass from F over an even word ends inside the word or at its end, never at two 1s side by side, and leaves an
even B configuration with the same last segment. -/
theorem fscan_even (ws : List (Nat × Nat)) :
    ∀ (S : List Nat) (u mt : Nat), EvS S → u % 2 = 0 → EvW ws →
      ∃ S' h ws', fscan S u ws mt = some (.B S' h ws' mt) ∧ Even (.B S' h ws' mt) := by
  induction ws with
  | nil =>
    intro S u mt hS hu _
    exact ⟨S, u + 2, [], rfl, hS, by omega, by omega, by simp [EvW]⟩
  | cons p ws ih =>
    obtain ⟨m, g⟩ := p
    intro S u mt hS hu hW
    rw [evW_cons] at hW
    obtain ⟨⟨hm, hg⟩, hW⟩ := hW
    simp only at hm hg
    simp only [fscan]
    by_cases g1 : g = 1
    · simp only [g1, ite_true]
      exact ih (u :: S) m mt (evS_cons.2 ⟨hu, hS⟩) hm hW
    · have g2 : 2 ≤ g := by omega
      simp only [g1, g2, ite_false, ite_true]
      refine ⟨S, u + 2, (m, g - 2) :: ws, rfl, hS, by omega, by omega, ?_⟩
      rw [evW_cons]
      exact ⟨⟨hm, by simp only; omega⟩, hW⟩

/-- **An even configuration is never stuck.** -/
theorem even_not_stuck (M : MC) (hM : Even M) : ∃ M', mstep M = some M' := by
  match M, hM with
  | .F S ws mt, ⟨hS, hW⟩ =>
    obtain ⟨S', h, ws', e, _⟩ := fscan_even ws S 0 mt hS rfl hW
    exact ⟨_, e⟩
  | .B [] h ws mt, ⟨_, _, h2, _⟩ =>
    exact ⟨.F [] ((1, h - 1) :: ws) mt, by simp only [mstep, show h ≠ 0 by omega, ite_false]⟩
  | .B (j :: S) h ws mt, ⟨_, _, h2, _⟩ =>
    exact ⟨.F S ((j + 2, h - 1) :: ws) mt, by simp only [mstep, show h ≠ 0 by omega, ite_false]⟩

/-- **Away from the left end, evenness is kept.** -/
theorem even_step (M M' : MC) (hM : Even M) (hb : ¬ AtBottom M) (h : mstep M = some M') : Even M' := by
  match M, hM, hb with
  | .F S ws mt, ⟨hS, hW⟩, _ =>
    obtain ⟨S', hh, ws', e, he⟩ := fscan_even ws S 0 mt hS rfl hW
    simp only [mstep] at h
    rw [e, Option.some.injEq] at h
    subst h
    exact he
  | .B [] _ _ _, _, hb => exact absurd trivial hb
  | .B (j :: S) hh ws mt, ⟨hS, he, h2, hW⟩, _ =>
    rw [evS_cons] at hS
    simp only [mstep, show hh ≠ 0 by omega, ite_false, Option.some.injEq] at h
    subst h
    refine ⟨hS.2, ?_⟩
    rw [evW_cons]
    exact ⟨⟨by simp only; omega, by simp only; omega⟩, hW⟩

/-- The next `t` steps from `M` never start from B with an empty stack. -/
def NoBottom : Nat → MC → Prop
  | 0, _ => True
  | t + 1, M => ¬ AtBottom M ∧ ∀ M', mstep M = some M' → NoBottom t M'

/-- **An even configuration runs on until it reaches the left end**: if none of its next `t` steps is B with an
empty stack, the macro machine runs those `t` steps without getting stuck, and stays even. -/
theorem even_run (t : Nat) : ∀ M, Even M → NoBottom t M → ∃ M', mrun t M = some M' ∧ Even M' := by
  induction t with
  | zero => intro M hM _; exact ⟨M, rfl, hM⟩
  | succ t ih =>
    intro M hM hN
    obtain ⟨hb, hN⟩ := hN
    obtain ⟨M₁, e⟩ := even_not_stuck M hM
    obtain ⟨M', e', hM'⟩ := ih M₁ (even_step M M₁ hM hb e) (hN M₁ e)
    exact ⟨M', by simp only [mrun, e, Option.bind_some]; exact e', hM'⟩

/-! ## Counting the odd numbers

`oddc` counts the odd numbers of a configuration, as the two-stack form sees them: stack entries, segments, gaps
`n = g − 1` (odd when `g` is even), and in state B the head gap (it becomes the gap `n = h − 2` of the next F
configuration); the last segment is left out.  In the interior of the tape the count never goes up:

* `oddc_B`: B with a nonempty stack keeps it;
* `oddc_F`: a pass from F keeps it or takes 2 off (two 1s side by side next to an odd segment: two odd numbers
  cancel), unless the pass reaches the last segment, where it can lose 1 (two 1s side by side next to the last
  segment) or meet blank tape;
* `oddc_bottom`: B with an empty stack adds exactly 1.

So every odd number in the run was born at the left end of the tape (or comes from the last segment), and odd numbers
disappear only in pairs or at the right end.  Kernel only.
-/

/-- 1 if odd. -/
def ob (n : Nat) : Int := ((n % 2 : Nat) : Int)

def oS : List Nat → Int
  | [] => 0
  | s :: S => ob s + oS S

/-- Segments `m` and gaps `n = g − 1` that are odd. -/
def oW : List (Nat × Nat) → Int
  | [] => 0
  | (m, g) :: ws => ob m + (1 - ob g) + oW ws

/-- The number of odd numbers, the last segment left out. -/
def oddc : MC → Int
  | .F S ws _ => oS S + oW ws
  | .B S h ws _ => oS S + ob h + oW ws
  | .Binf S => oS S

theorem ob_le (n : Nat) : 0 ≤ ob n ∧ ob n ≤ 1 := by unfold ob; omega

theorem fscan_odd (ws : List (Nat × Nat)) :
    ∀ (S : List Nat) (u mt : Nat) (M : MC), fscan S u ws mt = some M →
      (∃ S' h ws', M = .B S' h ws' mt ∧
        (oddc M = oS S + ob u + oW ws ∨ oddc M = oS S + ob u + oW ws - 2)) ∨
      (∃ S' h, M = .B S' h [] (mt - 1) ∧ 1 ≤ mt ∧ oddc M = oS S + ob u + oW ws - 1) ∨
      (∃ S', M = .Binf S' ∧ oddc M < oS S + ob u + oW ws) := by
  induction ws with
  | nil =>
    intro S u mt M h
    simp only [fscan, Option.some.injEq] at h
    subst h
    left
    refine ⟨S, u + 2, [], rfl, Or.inl ?_⟩
    simp only [oddc, oW, ob]; omega
  | cons p ws ih =>
    obtain ⟨m, g⟩ := p
    intro S u mt M h
    simp only [fscan] at h
    by_cases g1 : g = 1
    · subst g1
      simp only [ite_true] at h
      have := ih (u :: S) m mt M h
      simp only [oS, oW] at this ⊢
      have e1 : ob 1 = 1 := rfl
      rw [e1]
      rcases this with ⟨S', hh, ws', e, h'⟩ | ⟨S', hh, e, t1, h'⟩ | ⟨S', e, h'⟩
      · left; exact ⟨S', hh, ws', e, by omega⟩
      · right; left; exact ⟨S', hh, e, t1, by omega⟩
      · right; right; exact ⟨S', e, by omega⟩
    · simp only [g1, ite_false] at h
      by_cases g2 : 2 ≤ g
      · simp only [g2, ite_true, Option.some.injEq] at h
        subst h
        left
        refine ⟨S, u + 2, (m, g - 2) :: ws, rfl, Or.inl ?_⟩
        simp only [oddc, oW, ob]; omega
      · have g0 : g = 0 := by omega
        subst g0
        simp only [show ¬ (2 ≤ 0) by omega, ite_false] at h
        by_cases m0 : m = 0
        · simp [m0] at h
        simp only [m0, ite_false] at h
        cases ws with
        | nil =>
          by_cases t0 : mt = 0
          · simp only [t0, ite_true, Option.some.injEq] at h
            subst h
            right; right; refine ⟨_, rfl, ?_⟩
            simp only [oddc, oS, oW, ob]; omega
          · simp only [t0, ite_false, Option.some.injEq] at h
            subst h
            right; left
            refine ⟨_, _, rfl, by omega, ?_⟩
            simp only [oddc, oS, oW, ob]; omega
        | cons q ws' =>
          obtain ⟨m', g'⟩ := q
          by_cases z : m' = 0
          · simp [z] at h
          simp only [z, ite_false, Option.some.injEq] at h
          subst h
          left
          refine ⟨_, _, _, rfl, ?_⟩
          simp only [oddc, oS, oW, ob]
          omega

/-- **A pass from F never adds odd numbers**: it keeps their count or takes 2 off, with the last segment unchanged;
or it reaches the last segment, losing one odd number (the gap −1) while the last segment goes down by 1; or it
meets blank tape. -/
theorem oddc_F (S : List Nat) (ws : List (Nat × Nat)) (mt : Nat) (M' : MC) (h : mstep (.F S ws mt) = some M') :
    (∃ S' hh ws', M' = .B S' hh ws' mt ∧
      (oddc M' = oddc (.F S ws mt) ∨ oddc M' = oddc (.F S ws mt) - 2)) ∨
    (∃ S' hh, M' = .B S' hh [] (mt - 1) ∧ 1 ≤ mt ∧ oddc M' = oddc (.F S ws mt) - 1) ∨
    (∃ S', M' = .Binf S' ∧ oddc M' < oddc (.F S ws mt)) := by
  have : ob 0 = 0 := rfl
  have eF : oddc (.F S ws mt) = oS S + oW ws := rfl
  rw [eF]
  rcases fscan_odd ws S 0 mt M' h with ⟨S', hh, ws', e, h'⟩ | ⟨S', hh, e, t1, h'⟩ | hb
  · left; exact ⟨S', hh, ws', e, by omega⟩
  · right; left; exact ⟨S', hh, e, t1, by omega⟩
  · obtain ⟨S', e, h'⟩ := hb; right; right; exact ⟨S', e, by omega⟩

/-- **B with a nonempty stack keeps the count.** -/
theorem oddc_B (j : Nat) (S : List Nat) (hh : Nat) (ws : List (Nat × Nat)) (mt : Nat) (M' : MC)
    (h : mstep (.B (j :: S) hh ws mt) = some M') : oddc M' = oddc (.B (j :: S) hh ws mt) := by
  simp only [mstep] at h
  by_cases h0 : hh = 0
  · simp [h0] at h
  simp only [h0, ite_false, Option.some.injEq] at h
  subst h
  simp only [oddc, oS, oW, ob]
  omega

/-- **The left end adds exactly one odd number** (the segment 1 taken from below the stack). -/
theorem oddc_bottom (hh : Nat) (ws : List (Nat × Nat)) (mt : Nat) (M' : MC) (h : mstep (.B [] hh ws mt) = some M') :
    oddc M' = oddc (.B [] hh ws mt) + 1 := by
  simp only [mstep] at h
  by_cases h0 : hh = 0
  · simp [h0] at h
  simp only [h0, ite_false, Option.some.injEq] at h
  subst h
  simp only [oddc, oS, oW, ob]
  omega

/-- Blank tape ahead of B: the top stack entry becomes the last segment, which is not counted. -/
theorem oddc_binf (S : List Nat) (M' : MC) (h : mstep (.Binf S) = some M') : oddc M' ≤ oddc (.Binf S) := by
  cases S with
  | nil =>
    simp only [mstep, Option.some.injEq] at h
    subst h; simp [oddc, oS, oW]
  | cons j S =>
    simp only [mstep, Option.some.injEq] at h
    subst h
    have := ob_le j
    simp only [oddc, oS, oW]; omega

/-- 1 at the left end (B with an empty stack), else 0. -/
def bot : MC → Int
  | .B [] _ _ _ => 1
  | _ => 0

/-- **The count of odd numbers goes up only at the left end, by 1.** -/
theorem oddc_le (M M' : MC) (h : mstep M = some M') : oddc M' ≤ oddc M + bot M := by
  match M with
  | .F S ws mt =>
    have hb : bot (.F S ws mt) = 0 := rfl
    rw [hb]
    rcases oddc_F S ws mt M' h with ⟨_, _, _, _, e | e⟩ | ⟨_, _, _, _, e⟩ | ⟨_, _, e⟩
    · omega
    · omega
    · omega
    · omega
  | .B [] hh ws mt =>
    have := oddc_bottom hh ws mt M' h
    simp only [bot]; omega
  | .B (j :: S) hh ws mt =>
    have := oddc_B j S hh ws mt M' h
    simp only [bot]; omega
  | .Binf S =>
    have := oddc_binf S M' h
    simp only [bot]; omega

/-- How many of the first `t` steps from `M` are B with an empty stack. -/
def botc : Nat → MC → Int
  | 0, _ => 0
  | t + 1, M => match mstep M with
    | none => 0
    | some M' => bot M + botc t M'

/-- **Along a run, every odd number is paid for by a visit to the left end**: after `t` steps the count is at most
the starting count plus the number of those steps that were B with an empty stack. -/
theorem oddc_run (t : Nat) : ∀ M M', mrun t M = some M' → oddc M' ≤ oddc M + botc t M := by
  induction t with
  | zero => intro M M' h; simp only [mrun, Option.some.injEq] at h; subst h; simp [botc]
  | succ t ih =>
    intro M M' h
    simp only [mrun] at h
    cases e : mstep M with
    | none => rw [e] at h; cases h
    | some M₁ =>
      rw [e, Option.bind_some] at h
      have h1 := oddc_le M M₁ e
      have h2 := ih M₁ M' h
      simp only [botc, e]
      omega

end BB6e
