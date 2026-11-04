import Machine
import Pass

/-!
# The macro machine

At every pass start the tape has the shape

    0^∞ 1^(2s₁+2) 0 1^(2s₂+2) 0 … 0 1^(2sₚ+2) [head] 0^(2h+1) 1 (0 1)^m₁ 0^(2g₁) 1 (0 1)^m₂ 0^(2g₂) 1 … (0 1)^mₜ 0^∞

a *stack* of solid blocks of even length (top `sₚ` next to the head), a *head gap* of `2h + 2` cells counting the head's
own cell, and a *word* of segments `(0 1)^m` and gaps `0^(2g) 1`.  (In `notes/LAB_NOTES.md` gaps are counted as
`n = g − 1`, so `g = 0` is two 1s side by side.)  In state F the head gap is always `0 0 1` (`h = 0`); in state B it
is longer, or runs to the blank end.

`mstep` is the map from one pass start to the next, on these numbers.  Moving right, the head turns every segment
followed by a gap of 2 cells (`g = 1`) into a solid block and pushes it; the first other gap ends the pass; moving
left, the head sweeps the last block back into a segment and B erases the one before it, which becomes the next head
gap.  The theorem `mstep_sound` says that whenever `mstep` gives a next configuration, the machine really goes there,
in at least one step, without halting; the proof composes the pass lemmas of `Pass.lean`, for all parameters.

`mstep` returns `none` in exactly two cases, both never seen in the run from blank: a gap `g = 0` with an empty
segment on its left, or with an empty segment on its right that is not the last one (that one would make an odd gap,
which is where a halt could come from).  So `no_halt_of_macro` reduces the question to the macro machine: if it never
gets stuck from `B [] 1 [] 1` (the tape after 12 steps), the machine never halts.  Everything here is checked by the
kernel.
-/

namespace BB6e

open TM

/-! ## The encoding -/

/-- The tape left of the head: blocks `1^(2s+2)`, top of the stack (nearest the head) first, separated by single 0s,
blank below the bottom. -/
def encL : List Nat → Tape
  | [] => blank
  | s :: S => rep (s + 1) [true, true] (cons false (encL S))

/-- The word: pairs `(m, g)`, a segment `(0 1)^m` and a gap `0^(2g) 1`, then the last segment `(0 1)^mt` and blank. -/
def encW : List (Nat × Nat) → Nat → Tape
  | [], mt => rep mt [false, true] blank
  | (m, g) :: ws, mt => rep m [false, true] (rep g [false, false] (cons true (encW ws mt)))

/-- Configurations at pass starts. -/
inductive MC where
  /-- F on the first cell of the gap `0 0 1`. -/
  | F (S : List Nat) (ws : List (Nat × Nat)) (mt : Nat)
  /-- B on the first cell of a gap of `2h + 2` cells. -/
  | B (S : List Nat) (h : Nat) (ws : List (Nat × Nat)) (mt : Nat)
  /-- B with blank tape from the head on. -/
  | Binf (S : List Nat)
  deriving DecidableEq, Repr

/-- The machine configuration a macro configuration stands for. -/
def enc : MC → Config
  | .F S ws mt => ⟨encL S, rep 1 [false, false] (cons true (encW ws mt)), .F⟩
  | .B S h ws mt => ⟨encL S, rep (h + 1) [false, false] (cons true (encW ws mt)), .B⟩
  | .Binf S => ⟨encL S, blank, .B⟩

/-! ## The macro step -/

/-- The pass from F, scanning the word: `S` is the stack so far, `u` the last segment crossed (0 at the start). -/
def fscan (S : List Nat) (u : Nat) : List (Nat × Nat) → Nat → Option MC
  | [], mt => some (.B S (u + 2) [] mt)
  | (m, g) :: ws, mt =>
    if g = 1 then fscan (u :: S) m ws mt
    else if 2 ≤ g then some (.B S (u + 2) ((m, g - 2) :: ws) mt)
    else if m = 0 then none
    else match ws with
      | [] => if mt = 0 then some (.Binf (u :: S)) else some (.B (u :: S) m [] (mt - 1))
      | (m', g') :: ws' => if m' = 0 then none else some (.B (u :: S) m ((m' - 1, g') :: ws') mt)

/-- From one pass start to the next. -/
def mstep : MC → Option MC
  | .F S ws mt => fscan S 0 ws mt
  | .B [] h ws mt => if h = 0 then none else some (.F [] ((1, h - 1) :: ws) mt)
  | .B (j :: S) h ws mt => if h = 0 then none else some (.F S ((j + 2, h - 1) :: ws) mt)
  | .Binf [] => some (.F [] [] 1)
  | .Binf (j :: S) => some (.F S [] (j + 2))

/-- `t` macro steps. -/
def mrun : Nat → MC → Option MC
  | 0, M => some M
  | t + 1, M => (mstep M).bind (mrun t)

/-- The pass start after 12 steps from blank tape: `B> 0^4 1 0 1`. -/
def M0 : MC := .B [] 1 [] 1

/-! ## Tape identities -/

theorem rep_double (a : Bool) (n : Nat) (s : Tape) : rep n [a, a] s = rep (n * 2) [a] s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show (n + 1) * 2 = n * 2 + 1 + 1 by omega, rep_succ, rep_succ, rep_succ, ih]
    rfl

theorem app_false_blank (w : List Bool) (h : ∀ a ∈ w, a = false) : app w blank = blank := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [app_cons, h a (List.mem_cons_self ..), ih (fun b hb => h b (List.mem_cons_of_mem _ hb)), cons_false_blank]

theorem rep_false_blank (k : Nat) : rep k [false] blank = blank := by
  induction k with
  | zero => rfl
  | succ k ih => rw [rep_succ, ih]; exact cons_false_blank

/-! ## The pieces -/

/-- Crossing a segment followed by a gap of 2 cells: C on the second cell of a gap of 2 cells, `C>0 1 (0 1)^m 0`,
leaves `1 1 0 1^(2m)` and stands on the second cell of the next gap. -/
theorem unit_cross (m : Nat) (L R : Tape) :
    steps (3 + m * 2) ⟨L, app [false, true] (rep m [false, true] (app [false] R)), .C⟩ =
      some ⟨rep m [true, true] (app [false, true, true] L), R, .C⟩ := by
  have e : app [false, true] (rep m [false, true] (app [false] R)) = app [false, true, false] (rep m [true, false] R) := by
    rw [← rep_rotate m [false] [true, false] [false, true] rfl R, app_app]; rfl
  rw [e]
  have h₂ := cross_r trans (u := []) (w := [true, false]) (v := [true, true]) (fun L R => gap1 L R) m
    (app [false, true, true] L) R
  exact steps_seq trans (gap2 L _) h₂

/-- The leftward run after a pass that ended at a gap of 4 or more cells: E turns, A sweeps the last block into a
segment, A fills the 0 before it, B erases the block before that and stops on the 0 below it. -/
theorem end_big (u m : Nat) (L Q : Tape) :
    ∃ n, steps n ⟨rep u [true, true] (cons false L), app [false, true] (rep m [false, true] (app [false, false, false, false] Q)), .C⟩ =
      some ⟨L, rep (u + 3) [false, false] (cons true (rep m [false, true] Q)), .B⟩ := by
  have e₁ : app [false, true] (rep m [false, true] (app [false, false, false, false] Q)) =
      app [false, true, false] (rep m [true, false] (app [false, false, false] Q)) := by
    rw [show app [false, false, false, false] Q = app [false] (app [false, false, false] Q) from rfl,
      ← rep_rotate m [false] [true, false] [false, true] rfl, app_app]; rfl
  rw [e₁]
  let Lc := rep u [true, true] (cons false L)
  have h₁ := gap2 Lc (rep m [true, false] (app [false, false, false] Q))
  have h₂ := cross_r trans (u := []) (w := [true, false]) (v := [true, true]) (fun L R => gap1 L R) m
    (app [false, true, true] Lc) (app [false, false, false] Q)
  have h₃ := gapBig (rep m [true, true] (app [false, true, true] Lc)) Q
  have e₃ : app [true] (rep m [true, true] (app [false, true, true] Lc)) = rep m [true, true] (app [true, false, true, true] Lc) := by
    rw [rep_rotate m [true] [true, true] [true, true] rfl, app_app]; rfl
  rw [e₃] at h₃
  have h₄ := sweep m (app [true, false, true, true] Lc) (app [true] Q)
  have h₅ := sweep_end_even (app [true, true] Lc) (rep m [true, false] (app [true] Q))
  have e₅ : app [true, true] Lc = rep ((u + 1) * 2) [true] (cons false L) := by
    rw [← rep_double]; rfl
  have h₆ := erase ((u + 1) * 2) (cons false L) (app [false, false] (rep m [true, false] (app [true] Q)))
  rw [← e₅] at h₆
  have h₇ : steps 1 ⟨cons false L, app [true] (rep ((u + 1) * 2) [false] (app [false, false] (rep m [true, false] (app [true] Q)))), .B⟩ =
      some ⟨L, cons false (cons false (rep ((u + 1) * 2) [false] (app [false, false] (rep m [true, false] (app [true] Q))))), .B⟩ := rfl
  have e₇ : cons false (cons false (rep ((u + 1) * 2) [false] (app [false, false] (rep m [true, false] (app [true] Q))))) =
      rep (u + 3) [false, false] (cons true (rep m [false, true] Q)) := by
    rw [← rep_double, ← rep_rotate m [true] [false, true] [true, false] rfl, rep_app_comm]
    rfl
  rw [e₇] at h₇
  exact ⟨_, steps_seq trans (steps_seq trans (steps_seq trans (steps_seq trans (steps_seq trans (steps_seq trans h₁ h₂) h₃) h₄) h₅) h₆) h₇⟩

/-- The leftward run after a pass that ended at two 1s side by side, after a gap of 1 cell: B erases the last block
and stops on the 0 below it. -/
theorem end_double (u m : Nat) (L Z : Tape) :
    ∃ n, steps n ⟨rep u [true, true] (cons false L), app [false, true] (rep (m + 1) [false, true] (cons true Z)), .C⟩ =
      some ⟨rep (u + 1) [true, true] (cons false L), cons false (cons false (rep (m * 2) [false] (app [false] Z))), .B⟩ := by
  have e₁ : app [false, true] (rep (m + 1) [false, true] (cons true Z)) =
      app [false, true, false] (rep m [true, false] (app [true, true] Z)) := by
    rw [show rep (m + 1) [false, true] (cons true Z) = rep m [false, true] (app [false] (app [true, true] Z)) by
      rw [← rep_app_comm]; rfl, ← rep_rotate m [false] [true, false] [false, true] rfl, app_app]; rfl
  rw [e₁]
  let Lc := rep u [true, true] (cons false L)
  have h₁ := gap2 Lc (rep m [true, false] (app [true, true] Z))
  have h₂ := cross_r trans (u := []) (w := [true, false]) (v := [true, true]) (fun L R => gap1 L R) m
    (app [false, true, true] Lc) (app [true, true] Z)
  have h₃ := gap1_then_0 (rep m [true, true] (app [false, true, true] Lc)) Z
  have h₄ := erase (m * 2) (app [false, true, true] Lc) (app [false] Z)
  rw [← rep_double true m] at h₄
  have h₅ : steps 1 ⟨app [false, true, true] Lc, app [true] (rep (m * 2) [false] (app [false] Z)), .B⟩ =
      some ⟨app [true, true] Lc, cons false (cons false (rep (m * 2) [false] (app [false] Z))), .B⟩ := rfl
  exact ⟨_, steps_seq trans (steps_seq trans (steps_seq trans (steps_seq trans h₁ h₂) h₃) h₄) h₅⟩

/-- The gap of `2h + 2` cells after an erase: `0 0 0^(2m) 0 (0 1) …` is a gap of `2m + 4` cells. -/
theorem double_gap (m m' : Nat) (W : Tape) :
    cons false (cons false (rep (m * 2) [false] (app [false] (rep (m' + 1) [false, true] W)))) =
      rep (m + 2) [false, false] (cons true (rep m' [false, true] W)) := by
  rw [← rep_double]
  show app [false, false] (rep m [false, false] (app [false] (app [false, true] (rep m' [false, true] W)))) = _
  rw [app_app, show [false] ++ [false, true] = [false, false] ++ [true] from rfl, ← app_app, rep_app_comm]
  rfl

/-- The pass from B: B fills the first cell of its gap, C, D and E three more, and A sweeps the whole block left of
them, which ends at the 0 below it, where F starts the next pass. -/
theorem b_pass (a : Nat) (L Q : Tape) :
    ∃ n, steps n ⟨rep a [true, true] (cons false L), app [false, false, false, false] Q, .B⟩ =
      some ⟨L, rep 1 [false, false] (cons true (rep (a + 1) [false, true] Q)), .F⟩ := by
  have h₁ := start_B (rep a [true, true] (cons false L)) (app [false, false, false] Q)
  have h₂ := gapBig (app [true] (rep a [true, true] (cons false L))) Q
  have h₃ := sweep (a + 1) (cons false L) (app [true] Q)
  have e : rep (a + 1) [true, false] (app [true] Q) = app [true] (rep (a + 1) [false, true] Q) :=
    (rep_rotate (a + 1) [true] [false, true] [true, false] rfl Q).symm
  have h₄ : steps 1 ⟨cons false L, app [true] (rep (a + 1) [true, false] (app [true] Q)), .A⟩ =
      some ⟨L, rep 1 [false, false] (cons true (rep (a + 1) [false, true] Q)), .F⟩ := by
    rw [e]; rfl
  exact ⟨_, steps_seq trans (steps_seq trans (steps_seq trans h₁ h₂) h₃) h₄⟩

/-! ## Soundness -/

/-- C during a pass from F: the blocks pushed so far, the last crossed segment `u` (its block not closed yet). -/
def cscan (S : List Nat) (u : Nat) (ws : List (Nat × Nat)) (mt : Nat) : Config :=
  ⟨rep u [true, true] (cons false (encL S)), app [false, true] (encW ws mt), .C⟩

theorem fscan_sound (ws : List (Nat × Nat)) :
    ∀ (S : List Nat) (u mt : Nat) (M : MC), fscan S u ws mt = some M → ∃ n, steps n (cscan S u ws mt) = some (enc M) := by
  induction ws with
  | nil =>
    intro S u mt M h
    simp only [fscan, Option.some.injEq] at h
    subst h
    have e : encW [] mt = rep mt [false, true] (app [false, false, false, false] blank) := by
      rw [app_false_blank _ (by decide)]; rfl
    obtain ⟨n, hn⟩ := end_big u mt (encL S) blank
    refine ⟨n, ?_⟩
    simp only [cscan, e]
    rw [hn]
    simp only [enc, encW]
  | cons p ws ih =>
    obtain ⟨m, g⟩ := p
    intro S u mt M h
    simp only [fscan] at h
    by_cases g1 : g = 1
    · subst g1
      simp only [ite_true] at h
      obtain ⟨n, hn⟩ := ih (u :: S) m mt M h
      refine ⟨(3 + m * 2) + n, steps_seq trans ?_ hn⟩
      exact unit_cross m _ (app [false, true] (encW ws mt))
    · simp only [g1, ite_false] at h
      by_cases g2 : 2 ≤ g
      · simp only [g2, ite_true, Option.some.injEq] at h
        subst h
        obtain ⟨g', rfl⟩ : ∃ g', g = g' + 2 := ⟨g - 2, by omega⟩
        obtain ⟨n, hn⟩ := end_big u m (encL S) (rep g' [false, false] (cons true (encW ws mt)))
        exact ⟨n, hn⟩
      · have g0 : g = 0 := by omega
        subst g0
        simp only [show ¬ (2 ≤ 0) by omega, ite_false] at h
        by_cases m0 : m = 0
        · simp [m0] at h
        simp only [m0, ite_false] at h
        obtain ⟨m₁, rfl⟩ : ∃ m₁, m = m₁ + 1 := ⟨m - 1, by omega⟩
        obtain ⟨n, hn⟩ := end_double u m₁ (encL S) (encW ws mt)
        refine ⟨n, ?_⟩
        show steps n ⟨rep u [true, true] (cons false (encL S)), app [false, true] (rep (m₁ + 1) [false, true] (cons true (encW ws mt))), .C⟩ = _
        rw [hn]
        cases ws with
        | nil =>
          by_cases t0 : mt = 0
          · simp only [t0, ite_true, Option.some.injEq] at h
            subst h
            subst t0
            simp only [enc, encL, encW, rep_zero]
            rw [app_false_blank [false] (by decide), rep_false_blank, cons_false_blank, cons_false_blank]
          · simp only [t0, ite_false, Option.some.injEq] at h
            subst h
            obtain ⟨t₁, rfl⟩ : ∃ t₁, mt = t₁ + 1 := ⟨mt - 1, by omega⟩
            simp only [enc, encL, encW]
            rw [double_gap]
            rfl
        | cons q ws' =>
          obtain ⟨m', g'⟩ := q
          by_cases z : m' = 0
          · simp [z] at h
          simp only [z, ite_false, Option.some.injEq] at h
          subst h
          obtain ⟨m'', rfl⟩ : ∃ m'', m' = m'' + 1 := ⟨m' - 1, by omega⟩
          simp only [enc, encL, encW]
          rw [double_gap]
          rfl

/-- **The macro rules are sound**: whenever `mstep` gives a next configuration, the machine goes there. -/
theorem mstep_sound (M M' : MC) (h : mstep M = some M') : ∃ n, 0 < n ∧ steps n (enc M) = some (enc M') := by
  cases M with
  | F S ws mt =>
    obtain ⟨n, hn⟩ := fscan_sound ws S 0 mt M' h
    refine ⟨1 + n, by omega, steps_seq trans ?_ hn⟩
    exact start_F (encL S) (app [false, true] (encW ws mt))
  | B S hh ws mt =>
    have hpos : hh ≠ 0 := by
      intro e; subst e; cases S <;> simp [mstep] at h
    obtain ⟨k, rfl⟩ : ∃ k, hh = k + 1 := ⟨hh - 1, by omega⟩
    have eR : rep (k + 1 + 1) [false, false] (cons true (encW ws mt)) =
        app [false, false, false, false] (rep k [false, false] (cons true (encW ws mt))) := rfl
    cases S with
    | nil =>
      simp only [mstep, Nat.add_one_ne_zero, ite_false, Option.some.injEq] at h
      subst h
      obtain ⟨n, hn⟩ := b_pass 0 blank (rep k [false, false] (cons true (encW ws mt)))
      refine ⟨n, ?_, ?_⟩
      · rcases n with _ | n
        · simp at hn
        · omega
      show steps n ⟨blank, _, .B⟩ = _
      rw [eR, show blank = rep 0 [true, true] (cons false blank) from cons_false_blank.symm, hn]
      rfl
    | cons j S =>
      simp only [mstep, Nat.add_one_ne_zero, ite_false, Option.some.injEq] at h
      subst h
      obtain ⟨n, hn⟩ := b_pass (j + 1) (encL S) (rep k [false, false] (cons true (encW ws mt)))
      refine ⟨n, ?_, ?_⟩
      · rcases n with _ | n
        · simp at hn
        · omega
      show steps n ⟨rep (j + 1) [true, true] (cons false (encL S)), _, .B⟩ = _
      rw [eR, hn]
      rfl
  | Binf S =>
    have eR : (blank : Tape) = app [false, false, false, false] blank := (app_false_blank _ (by decide)).symm
    cases S with
    | nil =>
      simp only [mstep, Option.some.injEq] at h
      subst h
      obtain ⟨n, hn⟩ := b_pass 0 blank blank
      refine ⟨n, ?_, ?_⟩
      · rcases n with _ | n
        · simp at hn
        · omega
      show steps n ⟨blank, blank, .B⟩ = _
      rw [show (⟨blank, blank, .B⟩ : Config) = ⟨rep 0 [true, true] (cons false blank), app [false, false, false, false] blank, .B⟩ by
        rw [← eR, cons_false_blank]; rfl, hn]
      rfl
    | cons j S =>
      simp only [mstep, Option.some.injEq] at h
      subst h
      obtain ⟨n, hn⟩ := b_pass (j + 1) (encL S) blank
      refine ⟨n, ?_, ?_⟩
      · rcases n with _ | n
        · simp at hn
        · omega
      show steps n ⟨rep (j + 1) [true, true] (cons false (encL S)), blank, .B⟩ = _
      rw [eR, hn]
      rfl

/-- The run from blank tape reaches the first pass start, `M0`, after 12 steps. -/
theorem blank_to_M0 : steps 12 init = some (enc M0) := by
  have h := blank_reaches trans (q := St.A) (n := 12) (c := ⟨[], [false, false, false, false, true, false, true], .B⟩)
    (by decide +kernel)
  exact h.trans rfl

/-- `t` macro steps take the machine at least `t` steps, without a halt. -/
theorem mrun_sound (t : Nat) : ∀ M M', mrun t M = some M' → ∃ n, t ≤ n ∧ steps n (enc M) = some (enc M') := by
  induction t with
  | zero => intro M M' h; simp only [mrun, Option.some.injEq] at h; subst h; exact ⟨0, Nat.le_refl _, rfl⟩
  | succ t ih =>
    intro M M' h
    simp only [mrun] at h
    cases hs : mstep M with
    | none => simp [hs] at h
    | some M₁ =>
      rw [hs, Option.bind_some] at h
      obtain ⟨a, ha, h₁⟩ := mstep_sound M M₁ hs
      obtain ⟨b, hb, h₂⟩ := ih M₁ M' h
      exact ⟨a + b, by omega, steps_seq trans h₁ h₂⟩

/-- **The reduction.**  If the macro machine never gets stuck from `M0`, the machine never halts from blank tape. -/
theorem no_halt_of_macro (h : ∀ t, ∃ M, mrun t M0 = some M) : ¬ HaltsFromBlank := by
  apply not_halts_of_forall
  apply forall_of_unbounded trans (fun n => ∃ c, steps n init = some c)
  · intro n
    obtain ⟨M, hM⟩ := h n
    obtain ⟨k, hk, hs⟩ := mrun_sound n M0 M hM
    exact ⟨12 + k, by omega, ⟨_, steps_seq trans blank_to_M0 hs⟩⟩
  · intro m hm; exact hm

end BB6e
