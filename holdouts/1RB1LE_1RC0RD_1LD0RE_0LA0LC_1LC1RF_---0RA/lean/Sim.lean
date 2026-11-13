import Tokens

/-!
# A checked accelerated simulator for 1RB1LE_1RC0RD_1LD0RE_0LA0LC_1LC1RF_---0RA

A hybrid frame is a token frame (`Tokens.lean`) or a raw configuration with finitely many written cells (`TM.FCfg`).
`stepH` applies the token model where it is defined (one rule = many machine steps, counted exactly); elsewhere (the
resets at the right end of the tape) it makes single machine steps until the configuration is a token frame again.

* `stepH_sound`: a step of `stepH` with count `n` is a run of exactly `n ≥ 1` machine steps.
* `stepH_none`: `stepH` is undefined only at a configuration where the machine halts.
* `halts_iff`: the machine halts from blank tape if and only if some iterate of `stepH` from blank tape is undefined.
  This is the simulator's correctness, for all time: it does not say whether that happens.
* `runH_sound` and `no_halt_of_runH`: a run of `k` simulator steps that counts `t` machine steps shows that the
  machine does not halt in its first `t` steps.

Hand-written.
-/

namespace H158007

open TM

/-! ## Token frames and cell lists -/

def lcells : List Tok → List Bool
  | [] => []
  | .z :: l => false :: false :: lcells l
  | .o :: l => true :: true :: lcells l
  | .x :: l => true :: false :: true :: false :: lcells l

def rcells : List Bool → List Bool
  | [] => []
  | true :: r => true :: true :: rcells r
  | false :: r => true :: false :: rcells r

theorem lcells_spec : ∀ L : List Tok, app (lcells L) blank = ltape L
  | [] => rfl
  | .z :: l => by show cons false (cons false (app (lcells l) blank)) = _; rw [lcells_spec l]; rfl
  | .o :: l => by show cons true (cons true (app (lcells l) blank)) = _; rw [lcells_spec l]; rfl
  | .x :: l => by
    show cons true (cons false (cons true (cons false (app (lcells l) blank)))) = _; rw [lcells_spec l]; rfl

theorem rcells_spec : ∀ R : List Bool, app (rcells R) blank = rtape R
  | [] => rfl
  | true :: r => by show cons true (cons true (app (rcells r) blank)) = _; rw [rcells_spec r]; rfl
  | false :: r => by show cons true (cons false (app (rcells r) blank)) = _; rw [rcells_spec r]; rfl

/-- The raw configuration of a token frame. -/
def untok (f : TF) : FCfg St := ⟨lcells f.L, false :: false :: rcells f.R, .A⟩

theorem untok_cfg (f : TF) : (untok f).toCfg = f.cfg := by
  show (⟨app (lcells f.L) blank, cons false (cons false (app (rcells f.R) blank)), .A⟩ : Config) = _
  rw [lcells_spec, rcells_spec]; rfl

/-- All cells of the list are 0. -/
def allF : List Bool → Bool
  | [] => true
  | b :: r => !b && allF r

theorem allF_spec : ∀ r : List Bool, allF r = true → app r blank = blank
  | [], _ => rfl
  | true :: r, h => by simp [allF] at h
  | false :: r, h => by
    have h' : allF r = true := by simpa [allF] using h
    show cons false (app r blank) = blank
    rw [allF_spec r h', cons_false_blank]

/-- Read cells right of the head's `00` as a right word (`11` = 1, `10` = 0, then blank tape). -/
def parseR : List Bool → Option (List Bool)
  | [] => some []
  | [true] => some [false]
  | true :: true :: r => (parseR r).map (true :: ·)
  | true :: false :: r => (parseR r).map (false :: ·)
  | false :: r => if allF r then some [] else none

theorem parseR_spec : ∀ (r R : List Bool), parseR r = some R → app r blank = rtape R
  | [], R, h => by simp only [parseR, Option.some.injEq] at h; subst h; rfl
  | [true], R, h => by
    simp only [parseR, Option.some.injEq] at h; subst h
    show cons true blank = cons true (cons false blank); rw [cons_false_blank]
  | true :: true :: r, R, h => by
    simp only [parseR, Option.map_eq_some_iff] at h
    obtain ⟨R', h', rfl⟩ := h
    show cons true (cons true (app r blank)) = _; rw [parseR_spec r R' h']; rfl
  | true :: false :: r, R, h => by
    simp only [parseR, Option.map_eq_some_iff] at h
    obtain ⟨R', h', rfl⟩ := h
    show cons true (cons false (app r blank)) = _; rw [parseR_spec r R' h']; rfl
  | false :: r, R, h => by
    simp only [parseR] at h
    split at h
    · rename_i ha
      simp only [Option.some.injEq] at h; subst h
      show cons false (app r blank) = blank
      rw [allF_spec r ha, cons_false_blank]
    · simp at h

/-- Read cells left of the head (nearest first) as a left word. -/
def parseL : List Bool → Option (List Tok)
  | [] => some []
  | [false] => some []
  | true :: true :: l => (parseL l).map (.o :: ·)
  | false :: false :: l => (parseL l).map (.z :: ·)
  | true :: false :: true :: false :: l => (parseL l).map (.x :: ·)
  | _ => none

theorem parseL_spec (l : List Bool) (L : List Tok) (h : parseL l = some L) : app l blank = ltape L := by
  induction l using parseL.induct generalizing L with
  | case1 => simp only [parseL, Option.some.injEq] at h; subst h; rfl
  | case2 =>
    simp only [parseL, Option.some.injEq] at h; subst h
    show cons false blank = blank; rw [cons_false_blank]
  | case3 l ih =>
    simp only [parseL, Option.map_eq_some_iff] at h
    obtain ⟨L', h', rfl⟩ := h
    show cons true (cons true (app l blank)) = _; rw [ih L' h']; rfl
  | case4 l ih =>
    simp only [parseL, Option.map_eq_some_iff] at h
    obtain ⟨L', h', rfl⟩ := h
    show cons false (cons false (app l blank)) = _; rw [ih L' h']; rfl
  | case5 l ih =>
    simp only [parseL, Option.map_eq_some_iff] at h
    obtain ⟨L', h', rfl⟩ := h
    show cons true (cons false (cons true (cons false (app l blank)))) = _; rw [ih L' h']; rfl
  | case6 l h1 h2 h3 h4 h5 => 
    unfold parseL at h
    split at h <;> first | (exfalso; simp_all; done) | simp at h

/-- A raw configuration as a token frame, if it is one. -/
def tokenize (c : FCfg St) : Option TF :=
  match c.st, c.r with
  | .A, false :: false :: r =>
    match parseL c.l, parseR r with
    | some L, some R => some ⟨L, R⟩
    | _, _ => none
  | _, _ => none

theorem tokenize_spec (c : FCfg St) (f : TF) (h : tokenize c = some f) : c.toCfg = f.cfg := by
  obtain ⟨l, r, st⟩ := c
  unfold tokenize at h
  split at h
  · rename_i r' hst hr
    simp only at hst hr; subst hst; subst hr
    split at h
    · rename_i L R hL hR
      simp only [Option.some.injEq] at h; subst h
      show (⟨app l blank, cons false (cons false (app r' blank)), .A⟩ : Config) = _
      rw [parseL_spec l L hL, parseR_spec r' R hR]; rfl
    · simp at h
  · simp at h

/-! ## The simulator -/

inductive HF where
  | tok (f : TF)
  | raw (c : FCfg St)

def HF.cfg : HF → Config
  | .tok f => f.cfg
  | .raw c => c.toCfg

/-- One machine step from a raw configuration; the result is read as a token frame when it is one. -/
def rawStep (c : FCfg St) : Option (HF × Nat) :=
  match fstep c with
  | none => none
  | some c' =>
    match tokenize c' with
    | some f => some (.tok f, 1)
    | none => some (.raw c', 1)

/-- One step of the simulator, with the number of machine steps it stands for. -/
def stepH : HF → Option (HF × Nat)
  | .tok f =>
    match next f with
    | some (f', n) => some (.tok f', n)
    | none => rawStep (untok f)
  | .raw c => rawStep c

theorem rawStep_sound (c : FCfg St) (g : HF × Nat) (h : rawStep c = some g) :
    0 < g.2 ∧ steps g.2 c.toCfg = some g.1.cfg := by
  unfold rawStep at h
  split at h
  · simp at h
  · rename_i c' hc
    have hc' : TM.fstep trans c = some c' := hc
    have h0 : TM.step trans c.toCfg = some c'.toCfg := by rw [FCfg.step_eq, hc']; rfl
    have h1 : steps 1 c.toCfg = some c'.toCfg := steps_succ_of_step trans 0 h0
    split at h
    · rename_i f hf
      simp only [Option.some.injEq] at h; subst h
      exact ⟨Nat.one_pos, by rw [h1, tokenize_spec c' f hf]; rfl⟩
    · simp only [Option.some.injEq] at h; subst h
      exact ⟨Nat.one_pos, h1⟩

theorem rawStep_none (c : FCfg St) (h : rawStep c = none) : step c.toCfg = none := by
  unfold rawStep at h
  split at h
  · rename_i hc
    have hc' : TM.fstep trans c = none := hc
    show TM.step trans c.toCfg = none; rw [FCfg.step_eq, hc']; rfl
  · split at h <;> simp at h

theorem stepH_sound (p : HF) (g : HF × Nat) (h : stepH p = some g) :
    0 < g.2 ∧ steps g.2 p.cfg = some g.1.cfg := by
  cases p with
  | tok f =>
    simp only [stepH] at h
    split at h
    · rename_i f' n hn
      simp only [Option.some.injEq] at h; subst h
      exact next_sound f (f', n) hn
    · have := rawStep_sound (untok f) g h
      rwa [untok_cfg] at this
  | raw c => exact rawStep_sound c g h

theorem stepH_none (p : HF) (h : stepH p = none) : step p.cfg = none := by
  cases p with
  | tok f =>
    simp only [stepH] at h
    split at h
    · simp at h
    · have := rawStep_none (untok f) h
      rwa [untok_cfg] at this
  | raw c => exact rawStep_none c h

/-- The start: blank tape. -/
def p0 : HF := .raw (FCfg.blank .A)

theorem p0_cfg : p0.cfg = init := rfl

/-- **The simulator is exact**: the machine halts from blank tape iff the simulator stops. -/
theorem halts_iff :
    HaltsFromBlank ↔ ∃ k p, iterF (fun p => (stepH p).map (·.1)) k p0 = some p ∧ stepH p = none := by
  refine frames_halts_iff trans HF.cfg (fun p => (stepH p).map (·.1)) (fun _ => True) (fun p => stepH p = none)
    ?_ (fun _ _ _ _ => trivial) ?_ ?_ (c0 := init) (p0 := p0) (n0 := 0) rfl trivial
  · intro p p' _ h
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨g, hg, rfl⟩ := h
    exact ⟨g.2, stepH_sound p g hg⟩
  · intro p _ h
    exact ⟨0, p.cfg, rfl, stepH_none p h⟩
  · intro p _ h
    simpa using h

/-- `k` simulator steps from `p`, adding the machine steps to `t`. -/
def runH : Nat → HF → Nat → Option (HF × Nat)
  | 0, p, t => some (p, t)
  | k + 1, p, t =>
    match stepH p with
    | none => none
    | some (p', n) => runH k p' (t + n)

theorem runH_sound : ∀ (k : Nat) (p : HF) (t : Nat) (g : HF × Nat), runH k p t = some g →
    ∃ n, g.2 = t + n ∧ steps n p.cfg = some g.1.cfg
  | 0, p, t, g, h => by
    simp only [runH, Option.some.injEq] at h; subst h; exact ⟨0, rfl, rfl⟩
  | k + 1, p, t, g, h => by
    simp only [runH] at h
    split at h
    · simp at h
    · rename_i p' n hp
      obtain ⟨_, h1⟩ := stepH_sound p (p', n) hp
      obtain ⟨m, hm, h2⟩ := runH_sound k p' (t + n) g h
      exact ⟨n + m, by omega, steps_seq trans h1 h2⟩

/-- The simulator, run for `k` steps from blank tape, counts at least `N` machine steps. -/
def checkRun (k N : Nat) : Bool :=
  match runH k p0 0 with
  | some (_, t) => decide (N ≤ t)
  | none => false

theorem no_halt_of_runH {k N : Nat} (h : checkRun k N = true) : ∃ c, steps N init = some c := by
  unfold checkRun at h
  split at h
  · rename_i p t hr
    obtain ⟨n, hn, hs⟩ := runH_sound k p0 0 (p, t) hr
    have hN : N ≤ n := by simp only [decide_eq_true_eq] at h; omega
    have e : n = N + (n - N) := by omega
    rw [e] at hs
    exact steps_le trans hs
  · simp at h

end H158007
