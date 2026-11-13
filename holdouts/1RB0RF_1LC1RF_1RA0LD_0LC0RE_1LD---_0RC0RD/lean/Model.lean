import Counter
import Blank

/-! # The reduction of 1RB0RF_1LC1RF_1RA0LD_0LC0RE_1LD---_0RC0RD to the gap counter

`bounceM` (`Counter.lean`) is one bounce of the gap counter.  `runM k` runs `k` bounces.  From blank tape the machine
reaches `cfg [1, 1, 1, 1, 0]` in 71 steps (`blank_to_cfg`); if the model never gets `stuck` from there, the machine
halts exactly when the model reaches `halt` (`halts_iff_model`). -/

namespace H58767

open TM

theorem steps_add (a b : Nat) : ∀ c : Config,
    TM.steps trans (a + b) c = (TM.steps trans a c).bind (TM.steps trans b) := by
  induction a with
  | zero => intro c; simp [TM.steps]
  | succ a ih =>
    intro c
    have e : a + 1 + b = (a + b) + 1 := by omega
    rw [e]
    cases h : TM.step trans c with
    | none => simp [TM.steps, h]
    | some c' => simp [TM.steps, h, ih c']

/-- The run of the model: `k` bounces from a result. -/
def runM : Nat → Res → Res
  | 0, r => r
  | k + 1, .next G => runM k (bounceM G)
  | _ + 1, r => r

theorem runM_halt_stuck (k : Nat) : runM k .halt = .halt ∧ runM k .stuck = .stuck := by
  cases k <;> exact ⟨rfl, rfl⟩

theorem halts_of_steps {a : Nat} {c c' : Config} (h : steps a c = some c') (hc : Halts trans c') :
    Halts trans c := by
  obtain ⟨n, c'', h1, h2⟩ := hc
  exact ⟨a + n, c'', steps_seq trans h h1, h2⟩

/-- A `halt` of the model's run is a halt of the machine. -/
theorem halts_of_runM (k : Nat) : ∀ G, runM k (.next G) = .halt → Halts trans (cfg G) := by
  induction k with
  | zero => intro G h; cases h
  | succ k ih =>
    intro G h
    change runM k (bounceM G) = .halt at h
    cases hb : bounceM G with
    | next G' =>
      rw [hb] at h
      obtain ⟨t, _, ht⟩ := bounceM_next hb
      exact halts_of_steps ht (ih G' h)
    | halt => exact bounceM_halt hb
    | stuck => rw [hb, (runM_halt_stuck k).2] at h; cases h

/-- `k` bounces of the model are at least `k` steps of the machine. -/
theorem steps_of_runM (k : Nat) : ∀ G G', runM k (.next G) = .next G' →
    ∃ t, k ≤ t ∧ steps t (cfg G) = some (cfg G') := by
  induction k with
  | zero => intro G G' h; cases h; exact ⟨0, Nat.le_refl 0, rfl⟩
  | succ k ih =>
    intro G G' h
    change runM k (bounceM G) = .next G' at h
    cases hb : bounceM G with
    | next G1 =>
      rw [hb] at h
      obtain ⟨t, ht0, ht⟩ := bounceM_next hb
      obtain ⟨t', ht', h'⟩ := ih G1 G' h
      exact ⟨t + t', by omega, steps_seq trans ht h'⟩
    | halt => rw [hb, (runM_halt_stuck k).1] at h; cases h
    | stuck => rw [hb, (runM_halt_stuck k).2] at h; cases h

/-- **Reduction.**  From any gap configuration, if the model never gets stuck, the machine halts exactly when the
model's run reaches `halt`. -/
theorem halts_iff_runM (G : List Nat) (hs : ∀ k, runM k (.next G) ≠ .stuck) :
    Halts trans (cfg G) ↔ ∃ k, runM k (.next G) = .halt := by
  constructor
  · intro hh
    refine Classical.byContradiction fun hne => ?_
    have hn : ∀ k, ∃ G', runM k (.next G) = .next G' := by
      intro k
      cases e : runM k (.next G) with
      | next a => exact ⟨a, rfl⟩
      | halt => exact absurd ⟨k, e⟩ hne
      | stuck => exact absurd e (hs k)
    apply not_halts_of_forall trans _ hh
    apply forall_of_unbounded trans (fun m => ∃ c', steps m (cfg G) = some c')
    · intro n
      obtain ⟨a, e⟩ := hn n
      obtain ⟨t, ht, h⟩ := steps_of_runM n G a e
      exact ⟨t, ht, _, h⟩
    · intro m hm; exact hm
  · rintro ⟨k, hk⟩
    exact halts_of_runM k G hk

/-- From blank tape the machine reaches the gap list `[1, 1, 1, 1, 0]` in 71 steps. -/
theorem blank_to_cfg : steps 71 init = some (cfg [1, 1, 1, 1, 0]) := by
  have h : fsteps 71 (FCfg.blank .A) = some ⟨[true, true, true], [false, false, true, false, true, false, true,
      false, true, false, true, true], .C⟩ := by decide +kernel
  exact blank_reaches trans h

/-- **The machine halts from blank tape iff the gap counter, started at `[1, 1, 1, 1, 0]`, reaches `halt`**
(provided it never gets `stuck`). -/
theorem halts_iff_model (hs : ∀ k, runM k (.next [1, 1, 1, 1, 0]) ≠ .stuck) :
    HaltsFromBlank ↔ ∃ k, runM k (.next [1, 1, 1, 1, 0]) = .halt := by
  rw [← halts_iff_runM _ hs]
  constructor
  · rintro ⟨n, c, h1, h2⟩
    -- no halt in the first 10,000 steps, so the halt comes after step 71
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

end H58767
