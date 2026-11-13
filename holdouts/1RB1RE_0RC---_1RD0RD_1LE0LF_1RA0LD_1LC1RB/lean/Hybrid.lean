import Chain
import Blank

/-! # A model of 1RB1RE_0RC---_1RD0RD_1LE0LF_1RA0LD_1LC1RB that is defined everywhere

`halts_iff_of_no_stuck` (`Chain.lean`) needs the hypothesis that the orbit of the map `F` never meets a node no
rule covers (`stuck`).  This file removes the hypothesis by making the map total in the plainest way: the *hybrid*
map `hstep` is `F` wherever `F` gives an answer, and where it does not it goes on with single steps of the machine
itself, on a configuration written out as two finite lists (`raw`).

* `halts_iff_hybrid`: the machine halts from blank tape iff the hybrid orbit of the node `d 1 0 []` reaches
  `halt`.  No hypothesis.
* `hrun_of_orbit`: as long as the orbit of `F` is not stuck, the hybrid orbit *is* the orbit of `F`; so the fallback
  matters only if an uncovered node is ever reached (none in the first 3·10^7 nodes, `orbit_native`).

The fallback adds no understanding: after an uncovered node the hybrid map simply is the machine.  What the theorem
buys is a statement with nothing assumed. -/

namespace H8002

open TM

/-- `n` copies of a word, as a list. -/
def repL : Nat → List Bool → List Bool
  | 0, _ => []
  | n + 1, w => w ++ repL n w

theorem app_append (v w : List Bool) (R : Tape) : app (v ++ w) R = app v (app w R) := by
  induction v with
  | nil => rfl
  | cons a v ih => show cons a (app (v ++ w) R) = cons a (app v (app w R)); rw [ih]

theorem app_repL (n : Nat) (w v : List Bool) (R : Tape) : app (repL n w ++ v) R = rep n w (app v R) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show app (w ++ repL n w ++ v) R = app w (rep n w (app v R))
    rw [List.append_assoc, app_append, ih]

/-- The cells of an environment: `0^g (10)^c 1` for each block. -/
def ebits : List (Nat × Nat) → List Bool
  | [] => []
  | (g, c) :: e => repL g [false] ++ (repL c [true, false] ++ true :: ebits e)

theorem ebits_tape (e : List (Nat × Nat)) : app (ebits e) blank = envT e := by
  induction e with
  | nil => rfl
  | cons x e ih =>
    obtain ⟨g, c⟩ := x
    show app (repL g [false] ++ (repL c [true, false] ++ true :: ebits e)) blank =
      rep g [false] (rep c [true, false] (cons true (envT e)))
    rw [app_repL, app_repL, ← ih]; rfl

/-- The configuration of a node, written out as finite lists. -/
def toF : Node → FCfg St
  | .d A B e => ⟨false :: (repL B [true, false] ++ repL A [true]), false :: ebits e, .C⟩
  | .p A B e => ⟨false :: true :: true :: true :: (repL B [true, false] ++ repL A [true]), false :: ebits e, .C⟩
  | .t n e => ⟨[], repL n [false, true] ++ ebits e, .E⟩

theorem repL_tape (n : Nat) (w : List Bool) : app (repL n w) blank = rep n w blank := by
  have := app_repL n w [] blank
  rwa [List.append_nil] at this

theorem toF_cfg (n : Node) : (toF n).toCfg = n.cfg := by
  cases n with
  | d A B e =>
    show (⟨app (false :: (repL B [true, false] ++ repL A [true])) blank, app (false :: ebits e) blank, .C⟩ : Config) =
      ⟨Dl A B blank, cons false (envT e), .C⟩
    have h1 : app (false :: (repL B [true, false] ++ repL A [true])) blank = Dl A B blank := by
      show cons false (app (repL B [true, false] ++ repL A [true]) blank) = _
      rw [app_repL, repL_tape]; rfl
    have h2 : app (false :: ebits e) blank = cons false (envT e) := by
      show cons false (app (ebits e) blank) = _; rw [ebits_tape]
    rw [h1, h2]
  | p A B e =>
    show (⟨app (false :: true :: true :: true :: (repL B [true, false] ++ repL A [true])) blank,
      app (false :: ebits e) blank, .C⟩ : Config) = ⟨Pl A B, cons false (envT e), .C⟩
    have h1 : app (false :: true :: true :: true :: (repL B [true, false] ++ repL A [true])) blank = Pl A B := by
      show cons false (cons true (cons true (cons true (app (repL B [true, false] ++ repL A [true]) blank)))) = _
      rw [app_repL, repL_tape]; rfl
    have h2 : app (false :: ebits e) blank = cons false (envT e) := by
      show cons false (app (ebits e) blank) = _; rw [ebits_tape]
    rw [h1, h2]
  | t n e =>
    show (⟨app [] blank, app (repL n [false, true] ++ ebits e) blank, .E⟩ : Config) =
      ⟨blank, rep n [false, true] (envT e), .E⟩
    rw [app_repL, ebits_tape]; rfl

/-- A state of the hybrid map: a node, or a written-out configuration of the machine. -/
inductive HS where
  | node (n : Node)
  | raw (c : FCfg St)

/-- The machine configuration of a state. -/
def HS.cfg : HS → Config
  | .node n => n.cfg
  | .raw c => c.toCfg

/-- The outcome of one move of the hybrid map. -/
inductive HRes where
  | next (s : HS)
  | halt

/-- One step of the machine on a written-out configuration. -/
def rawStep (c : FCfg St) : HRes :=
  match fstep c with
  | none => .halt
  | some c' => .next (.raw c')

/-- From a node: `F` if it is defined, one machine step otherwise. -/
def nodeStep (n : Node) : HRes :=
  match F n with
  | .next n' => .next (.node n')
  | .halt => .halt
  | .stuck => rawStep (toF n)

/-- One move of the hybrid map. -/
def hstep : HS → HRes
  | .node n => nodeStep n
  | .raw c => rawStep c

theorem h_steps_add (a b : Nat) : ∀ c : Config,
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

theorem halts_of_steps {a : Nat} {c c' : Config} (h : steps a c = some c') (hc : Halts trans c') :
    Halts trans c := by
  obtain ⟨n, c'', h1, h2⟩ := hc
  exact ⟨a + n, c'', steps_seq trans h h1, h2⟩

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

/-- A `next` of the hybrid map is a run of the machine of at least one step. -/
theorem hstep_next {s s' : HS} (h : hstep s = .next s') : ∃ t, 0 < t ∧ steps t s.cfg = some s'.cfg := by
  cases s with
  | node n =>
    change nodeStep n = _ at h; unfold nodeStep at h
    have hs := F_sem n
    cases hb : F n with
    | next n' =>
      rw [hb] at h hs; cases h
      obtain ⟨k, hk⟩ := hs
      exact ⟨k + 1, by omega, hk⟩
    | halt => rw [hb] at h; cases h
    | stuck =>
      rw [hb] at h
      have := rawStep_next h
      rw [toF_cfg] at this; exact this
  | raw c => exact rawStep_next h

/-- A `halt` of the hybrid map is a halting configuration of the machine. -/
theorem hstep_halt {s : HS} (h : hstep s = .halt) : Halts trans s.cfg := by
  cases s with
  | node n =>
    change nodeStep n = _ at h; unfold nodeStep at h
    have hs := F_sem n
    cases hb : F n with
    | next n' => rw [hb] at h; cases h
    | halt => rw [hb] at hs; exact hs
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

theorem iter_head (m : Node) (k : Nat) : iter (.next m) (k + 1) = iter (F m) k := rfl

theorem iter_halt : ∀ k, iter .halt k = .halt
  | 0 => rfl
  | k + 1 => iter_halt k

theorem iter_stuck : ∀ k, iter .stuck k = .stuck
  | 0 => rfl
  | k + 1 => iter_stuck k

/-- While the orbit of `F` is not stuck, the hybrid orbit is the orbit of `F`. -/
theorem hrun_of_orbit (k : Nat) :
    (∀ n, orbit k = .next n → hrun k (.next (.node (.d 1 0 []))) = .next (.node n)) ∧
    (orbit k = .halt → hrun k (.next (.node (.d 1 0 []))) = .halt) := by
  have gen : ∀ (k : Nat) (m : Node),
      (∀ n, iter (.next m) k = .next n → hrun k (.next (.node m)) = .next (.node n)) ∧
      (iter (.next m) k = .halt → hrun k (.next (.node m)) = .halt) := by
    intro k
    induction k with
    | zero => intro m; exact ⟨fun n h => (by cases h; rfl), fun h => (by cases h)⟩
    | succ k ih =>
      intro m
      have e2 : hrun (k + 1) (.next (.node m)) = hrun k (nodeStep m) := rfl
      have e1 : iter (.next m) (k + 1) = iter (F m) k := iter_head m k
      rw [e1, e2]
      cases hb : F m with
      | next m1 =>
        have : nodeStep m = .next (.node m1) := by unfold nodeStep; rw [hb]
        rw [this]; exact ih m1
      | halt =>
        have : nodeStep m = .halt := by unfold nodeStep; rw [hb]
        rw [this, hrun_halt, iter_halt]
        exact ⟨fun n h => (by cases h), fun _ => rfl⟩
      | stuck =>
        rw [iter_stuck]
        exact ⟨fun n h => (by cases h), fun h => (by cases h)⟩
  exact gen k _

/-- **The machine halts from blank tape iff the hybrid orbit of the node `d 1 0 []` reaches `halt`.**
No hypothesis. -/
theorem halts_iff_hybrid :
    HaltsFromBlank ↔ ∃ k, hrun k (.next (.node (.d 1 0 []))) = .halt := by
  rw [← halts_iff_hrun (.node (.d 1 0 []))]
  show HaltsFromBlank ↔ Halts trans (Node.d 1 0 []).cfg
  constructor
  · rintro ⟨n, c, h1, h2⟩
    have hn : 2 ≤ n := by
      refine Classical.byContradiction fun hlt => ?_
      obtain ⟨c', hc'⟩ := blank_runs_kernel
      have e : 10000 = n + ((10000 - n - 1) + 1) := by omega
      change TM.steps trans 10000 init = _ at hc'
      rw [e, steps_halt trans h1 h2] at hc'
      cases hc'
    obtain ⟨d, rfl⟩ : ∃ d, n = 2 + d := ⟨n - 2, by omega⟩
    have hb : TM.steps trans 2 init = some (Node.d 1 0 []).cfg := start_cfg
    rw [h_steps_add, hb] at h1
    exact ⟨d, c, h1, h2⟩
  · intro h; exact halts_of_steps start_cfg h

end H8002
