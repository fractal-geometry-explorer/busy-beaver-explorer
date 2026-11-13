import Model

/-! # A model of 1RB0RF_1LC1RF_1RA0LD_0LC0RE_1LD---_0RC0RD that is defined everywhere

`halts_iff_model` (`Model.lean`) needs the hypothesis that the gap counter never meets a pattern its rules do not
cover (`stuck`).  This file removes the hypothesis by making the model total in the plainest way: the *hybrid*
model `hstep` uses the gap counter `bounceM` wherever it gives an answer, and where it does not it goes on with
single steps of the machine itself, on a configuration written out as two finite lists (`raw`).

* `halts_iff_hybrid`: the machine halts from blank tape iff the hybrid run from the gap list `[1, 1, 1, 1, 0]`
  reaches `halt`.  No hypothesis.
* `hrun_of_runM`: as long as the gap counter is not stuck, the hybrid run *is* the run of the gap counter; so the
  fallback matters only if an uncovered pattern is ever reached (none in the run computed so far).

The fallback adds no understanding: after an uncovered pattern the hybrid model simply is the machine.  What the
theorem buys is a statement with nothing assumed. -/

namespace H58767

open TM

/-- The cells of a gap list: `0^g 1` for each gap. -/
def gbits : List Nat → List Bool
  | [] => []
  | g :: G => List.replicate g false ++ true :: gbits G

theorem app_zeros (g : Nat) (w : List Bool) (R : Tape) :
    app (List.replicate g false ++ w) R = rep g [false] (app w R) := by
  induction g with
  | zero => rfl
  | succ g ih => show cons false (app (List.replicate g false ++ w) R) = cons false (rep g [false] (app w R)); rw [ih]

theorem gbits_tape (G : List Nat) : app (gbits G) blank = gws G blank := by
  induction G with
  | nil => rfl
  | cons g G ih =>
    show app (List.replicate g false ++ true :: gbits G) blank = gw g (gws G blank)
    rw [app_zeros, ← ih]; rfl

/-- The configuration of a gap list, written out as finite lists. -/
def toF (G : List Nat) : FCfg St := ⟨[true, true, true], false :: false :: true :: gbits G, .C⟩

theorem toF_cfg (G : List Nat) : (toF G).toCfg = cfg G := by
  show (⟨app [true, true, true] blank, app (false :: false :: true :: gbits G) blank, .C⟩ : Config) = _
  unfold cfg
  have : app (false :: false :: true :: gbits G) blank = gw 2 (gws G blank) := by
    show cons false (cons false (cons true (app (gbits G) blank))) = _
    rw [gbits_tape]; rfl
  rw [this]; rfl

/-- A state of the hybrid model: a gap list, or a written-out configuration of the machine. -/
inductive HS where
  | gap (G : List Nat)
  | raw (c : FCfg St)

/-- The machine configuration of a state. -/
def HS.cfg : HS → Config
  | .gap G => H58767.cfg G
  | .raw c => c.toCfg

/-- The outcome of one move of the hybrid model. -/
inductive HRes where
  | next (s : HS)
  | halt

/-- One step of the machine on a written-out configuration. -/
def rawStep (c : FCfg St) : HRes :=
  match fstep c with
  | none => .halt
  | some c' => .next (.raw c')

/-- From a gap list: a bounce of the gap counter if it is defined, one machine step otherwise. -/
def gapStep (G : List Nat) : HRes :=
  match bounceM G with
  | .next G' => .next (.gap G')
  | .halt => .halt
  | .stuck => rawStep (toF G)

/-- One move of the hybrid model. -/
def hstep : HS → HRes
  | .gap G => gapStep G
  | .raw c => rawStep c

theorem rawStep_next {c : FCfg St} {s : HS} (h : rawStep c = .next s) :
    ∃ t, 0 < t ∧ steps t c.toCfg = some s.cfg := by
  unfold rawStep at h
  cases e : fstep c with
  | none => rw [e] at h; cases h
  | some c' =>
    rw [e] at h; cases h
    refine ⟨1, by omega, ?_⟩
    have := FCfg.steps_eq trans 1 c
    change steps 1 c.toCfg = (TM.fsteps trans 1 c).map FCfg.toCfg at this
    rw [this]
    show (TM.fsteps trans 1 c).map FCfg.toCfg = some c'.toCfg
    have e' : TM.fstep trans c = some c' := e
    simp [TM.fsteps, e']

theorem rawStep_halt {c : FCfg St} (h : rawStep c = .halt) : Halts trans c.toCfg := by
  unfold rawStep at h
  cases e : fstep c with
  | none =>
    refine ⟨0, c.toCfg, rfl, ?_⟩
    have e' : TM.fstep trans c = none := e
    rw [FCfg.step_eq, e']; rfl
  | some c' => rw [e] at h; cases h

/-- A `next` of the hybrid model is a run of the machine of at least one step. -/
theorem hstep_next {s s' : HS} (h : hstep s = .next s') : ∃ t, 0 < t ∧ steps t s.cfg = some s'.cfg := by
  cases s with
  | gap G =>
    change gapStep G = _ at h; unfold gapStep at h
    cases hb : bounceM G with
    | next G' => rw [hb] at h; cases h; exact bounceM_next hb
    | halt => rw [hb] at h; cases h
    | stuck =>
      rw [hb] at h
      have := rawStep_next h
      rw [toF_cfg] at this; exact this
  | raw c => exact rawStep_next h

/-- A `halt` of the hybrid model is a halting configuration of the machine. -/
theorem hstep_halt {s : HS} (h : hstep s = .halt) : Halts trans s.cfg := by
  cases s with
  | gap G =>
    change gapStep G = _ at h; unfold gapStep at h
    cases hb : bounceM G with
    | next G' => rw [hb] at h; cases h
    | halt => exact bounceM_halt hb
    | stuck =>
      rw [hb] at h
      have := rawStep_halt h
      rw [toF_cfg] at this; exact this
  | raw c => exact rawStep_halt h

/-- The run of the hybrid model. -/
def hrun : Nat → HRes → HRes
  | 0, r => r
  | k + 1, .next s => hrun k (hstep s)
  | _ + 1, .halt => .halt

theorem hrun_halt (k : Nat) : hrun k .halt = .halt := by cases k <;> rfl

theorem halts_of_hrun (k : Nat) : ∀ s, hrun k (.next s) = .halt → Halts trans s.cfg := by
  induction k with
  | zero => intro s h; cases h
  | succ k ih =>
    intro s h
    change hrun k (hstep s) = .halt at h
    cases hb : hstep s with
    | next s' =>
      rw [hb] at h
      obtain ⟨t, _, ht⟩ := hstep_next hb
      exact halts_of_steps ht (ih s' h)
    | halt => exact hstep_halt hb

theorem steps_of_hrun (k : Nat) : ∀ s s', hrun k (.next s) = .next s' →
    ∃ t, k ≤ t ∧ steps t s.cfg = some s'.cfg := by
  induction k with
  | zero => intro s s' h; cases h; exact ⟨0, Nat.le_refl 0, rfl⟩
  | succ k ih =>
    intro s s' h
    change hrun k (hstep s) = .next s' at h
    cases hb : hstep s with
    | next s1 =>
      rw [hb] at h
      obtain ⟨t, ht0, ht⟩ := hstep_next hb
      obtain ⟨t', ht', h'⟩ := ih s1 s' h
      exact ⟨t + t', by omega, steps_seq trans ht h'⟩
    | halt => rw [hb, hrun_halt] at h; cases h

/-- From any state, the machine halts exactly when the hybrid run reaches `halt`. -/
theorem halts_iff_hrun (s : HS) : Halts trans s.cfg ↔ ∃ k, hrun k (.next s) = .halt := by
  constructor
  · intro hh
    refine Classical.byContradiction fun hne => ?_
    have hn : ∀ k, ∃ s', hrun k (.next s) = .next s' := by
      intro k
      cases e : hrun k (.next s) with
      | next a => exact ⟨a, rfl⟩
      | halt => exact absurd ⟨k, e⟩ hne
    apply not_halts_of_forall trans _ hh
    apply forall_of_unbounded trans (fun m => ∃ c', steps m s.cfg = some c')
    · intro n
      obtain ⟨a, e⟩ := hn n
      obtain ⟨t, ht, h⟩ := steps_of_hrun n s a e
      exact ⟨t, ht, _, h⟩
    · intro m hm; exact hm
  · rintro ⟨k, hk⟩
    exact halts_of_hrun k s hk

/-- While the gap counter is not stuck, the hybrid run is the run of the gap counter. -/
theorem hrun_of_runM (k : Nat) : ∀ G,
    (∀ G', runM k (.next G) = .next G' → hrun k (.next (.gap G)) = .next (.gap G')) ∧
    (runM k (.next G) = .halt → hrun k (.next (.gap G)) = .halt) := by
  induction k with
  | zero => intro G; exact ⟨fun G' h => (by cases h; rfl), fun h => (by cases h)⟩
  | succ k ih =>
    intro G
    have e1 : runM (k + 1) (.next G) = runM k (bounceM G) := rfl
    have e2 : hrun (k + 1) (.next (.gap G)) = hrun k (hstep (.gap G)) := rfl
    rw [e1, e2]
    cases hb : bounceM G with
    | next G1 =>
      have : hstep (.gap G) = .next (.gap G1) := by show gapStep G = _; unfold gapStep; rw [hb]
      rw [this]; exact ih G1
    | halt =>
      have : hstep (.gap G) = .halt := by show gapStep G = _; unfold gapStep; rw [hb]
      rw [this, hrun_halt, (runM_halt_stuck k).1]
      exact ⟨fun G' h => (by cases h), fun _ => rfl⟩
    | stuck =>
      rw [(runM_halt_stuck k).2]
      exact ⟨fun G' h => (by cases h), fun h => (by cases h)⟩

/-- **The machine halts from blank tape iff the hybrid model, started at the gap list `[1, 1, 1, 1, 0]`, reaches
`halt`.**  No hypothesis. -/
theorem halts_iff_hybrid :
    HaltsFromBlank ↔ ∃ k, hrun k (.next (.gap [1, 1, 1, 1, 0])) = .halt := by
  rw [← halts_iff_hrun (.gap [1, 1, 1, 1, 0])]
  show HaltsFromBlank ↔ Halts trans (cfg [1, 1, 1, 1, 0])
  constructor
  · rintro ⟨n, c, h1, h2⟩
    have hn : 71 ≤ n := by
      refine Classical.byContradiction fun hlt => ?_
      obtain ⟨c', hc'⟩ := blank_runs_kernel
      have e : 10000 = n + ((10000 - n - 1) + 1) := by omega
      change TM.steps trans 10000 init = _ at hc'
      rw [e, steps_halt trans h1 h2] at hc'
      cases hc'
    obtain ⟨d, rfl⟩ : ∃ d, n = 71 + d := ⟨n - 71, by omega⟩
    have hb : TM.steps trans 71 init = some (cfg [1, 1, 1, 1, 0]) := blank_to_cfg
    rw [steps_add, hb] at h1
    exact ⟨d, c, h1, h2⟩
  · intro h; exact halts_of_steps blank_to_cfg h

/-- A result that is a state (not `halt`, not `stuck`). -/
def Res.isNext : Res → Bool
  | .next _ => true
  | _ => false

/-- The gap counter runs 200 bounces from `[1, 1, 1, 1, 0]` without halting and without leaving its rules
(evaluated by Lean's kernel). -/
theorem model_runs_kernel : (runM 200 (.next [1, 1, 1, 1, 0])).isNext = true := by decide +kernel

/-- The same for 30,000 bounces (compiled evaluation). -/
theorem model_runs_native : (runM 30000 (.next [1, 1, 1, 1, 0])).isNext = true := by native_decide

end H58767
