import WaveTime

/-!
# The super orbit by periodic tables of its last blocks

Read from the right end, the super step is a cascade.  With the list nearest first, `L = [p_m, …, p_1]`, every super
step the first level (`p_m`) receives a wave with `h = 10`; a level with block `p` that receives a wave `h` has
`d = p + h`, and if `d` is odd it becomes `(d + 5) / 2` and the next level receives an add of `(d - 1) / 2`, if `d` is
even it becomes `d / 2` and the next level receives the wave `d / 2`.  Nothing flows back, so the first `k` levels
(`B`, the bottom) run on their own, whatever the rest (`U`) is: `superL_split`.  The machine steps split the same way
(`superT_split`).

The bottom becomes periodic, and `c/superrun.c` skips over its periods with a table: for each super step in which the
bottom sends something to `U`, the number of super steps since the last one, the event, and the machine steps the
bottom accounts for.  Here:

* `Rep B T tl`: the table `T` with tail `tl` is one period of the bottom `B` (it comes back to `B`);
* `pass_sound`: running only `U` on the table follows the super orbit of `B ++ U` over a whole period;
* `build_rep`: if level `p` comes back to `p` after `L` periods of `Rep B T tl`, the table that `build` computes is a
  period of `B ++ [p]`;
* `drive_sound`: a plan of passes and table builds, evaluated, gives a point of the timed orbit `orbitT` of
  `WaveTime.lean`, so a bound on the machine (`runs_of_orbitT`).

Every table is checked as it is built (`build` must bring the level back), so nothing about periodicity is assumed.
-/

namespace BB6b

open TM

/-! ## The cascade -/

/-- What a level passes to the next level (further left) in one super step. -/
inductive Ev where
  | none
  | add (a : Nat)
  | wave (h : Nat)
  deriving DecidableEq, Repr

/-- A level with block `p` receiving `e`: its new block, what it passes on, and the machine steps it accounts for
(the terms of `waveTime`: `oddT d 0` where the wave turns, `evenT d` and the sweep's `d / 2 + 1` where it passes). -/
def lev (p : Nat) : Ev → Nat × Ev × Nat
  | .none => (p, .none, 0)
  | .add a => (p + a, .none, 0)
  | .wave h =>
    if (p + h) % 2 = 1 then ((p + h + 5) / 2, .add ((p + h - 1) / 2), oddT (p + h) 0)
    else ((p + h) / 2, .wave ((p + h) / 2), evenT (p + h) + (p + h) / 2 + 1)

/-- The levels `B` (nearest first) receiving `e`: the new levels, what the last passes on, and the steps. -/
def low : List Nat → Ev → List Nat × Ev × Nat
  | [], e => ([], e, 0)
  | p :: B, e =>
    match lev p e with
    | (p', e', c) =>
      match low B e' with
      | (B', e'', c') => (p' :: B', e'', c + c')

/-- The levels `U`, the last of them the leftmost block, receiving `e`: `wave` and `leftEnd` of `Wave.lean`. -/
def push : Ev → List Nat → Option (List Nat)
  | .none, U => some U
  | .add a, [] => some [a]
  | .add a, p :: U => some ((p + a) :: U)
  | .wave h, [] => leftEnd h h
  | .wave h, p :: U => wave (p + h) U

/-- The machine steps of `push` (`waveTime` without the sweep's start). -/
def pushT : Ev → List Nat → Nat
  | .wave h, [] => leftTime h h 0
  | .wave h, p :: U => waveTime (p + h) U 0
  | _, _ => 0

theorem low_none : ∀ B, low B .none = (B, .none, 0)
  | [] => rfl
  | p :: B => by simp only [low, lev, low_none B, Nat.add_zero]

theorem superL_push (L : List Nat) (h : L ≠ []) : superL L = push (.wave 10) L := by
  match L, h with
  | p :: L, _ => rfl

/-- **The bottom runs on its own**: the levels `U` see only what `B` passes on. -/
theorem push_split : ∀ (B U : List Nat) (e : Ev), U ≠ [] →
    push e (B ++ U) = (push (low B e).2.1 U).map ((low B e).1 ++ ·) := by
  intro B
  induction B with
  | nil => intro U e _; simp [low]
  | cons p B ih =>
    intro U e hU
    obtain ⟨q, R, hqR⟩ : ∃ q R, B ++ U = q :: R := by
      cases B with
      | nil => cases U with
        | nil => exact absurd rfl hU
        | cons q R => exact ⟨q, R, rfl⟩
      | cons q R => exact ⟨q, R ++ U, rfl⟩
    cases e with
    | none => simp [push, low, lev, low_none]
    | add a => simp [push, low, lev, low_none]
    | wave h =>
      show wave (p + h) (B ++ U) = (push (low (p :: B) (.wave h)).2.1 U).map ((low (p :: B) (.wave h)).1 ++ ·)
      rw [hqR]
      by_cases hd : (p + h) % 2 = 1
      · have ih' := ih U (.add ((p + h - 1) / 2)) hU
        rw [hqR] at ih'
        simp only [wave, hd, ↓reduceIte, low, lev]
        rcases ho : push (low B (.add ((p + h - 1) / 2))).2.1 U with _ | x
        · rw [ho] at ih'; cases ih'
        · rw [ho] at ih'; simp only [push, Option.map_some, Option.some.injEq] at ih'; simp [ih']
      · have ih' := ih U (.wave ((p + h) / 2)) hU
        rw [hqR] at ih'
        simp only [wave, hd, ↓reduceIte, low, lev]
        rw [show push (.wave ((p + h) / 2)) (q :: R) = wave (q + (p + h) / 2) R from rfl] at ih'
        rw [ih']
        rcases push (low B (.wave ((p + h) / 2))).2.1 U with _ | x <;> rfl

/-! ## The steps split the same way -/

theorem leftTime_lin : ∀ (f d A : Nat), leftEnd f d ≠ none → leftTime f d A = leftTime f d 0 + A := by
  intro f
  induction f with
  | zero => intro d A h; exact absurd rfl h
  | succ f ih =>
    intro d A h
    by_cases h1 : d ≤ 1
    · simp [leftEnd, h1] at h
    by_cases h2 : d % 2 = 1
    · simp only [leftTime, h2, ↓reduceIte, oddT] <;> omega
    · by_cases h4 : d = 4
      · subst h4
        rw [leftEnd_even f 4 (by omega) (by omega), show 4 / 2 = 2 from rfl, leftEnd_two f] at h
        exact absurd rfl h
      · rw [leftEnd_even f d (by omega) (by omega)] at h
        have h' : leftEnd f (d / 2) ≠ none := by intro e; rw [e] at h; exact h rfl
        simp only [leftTime, h2, h4, ↓reduceIte]
        rw [ih _ (A + d / 2 + 1) h', ih _ (0 + d / 2 + 1) h']
        omega

theorem waveTime_lin : ∀ (L : List Nat) (d A : Nat), wave d L ≠ none → waveTime d L A = waveTime d L 0 + A := by
  intro L
  induction L with
  | nil => intro d A h; exact leftTime_lin d d A h
  | cons p L ih =>
    intro d A h
    by_cases h2 : d % 2 = 1
    · simp only [waveTime, h2, ↓reduceIte, oddT] <;> omega
    · simp only [wave, h2, ↓reduceIte] at h
      have h' : wave (p + d / 2) L ≠ none := by intro e; rw [e] at h; exact h rfl
      simp only [waveTime, h2, ↓reduceIte]
      rw [ih _ (A + d / 2 + 1) h', ih _ (0 + d / 2 + 1) h']
      omega

theorem pushT_split : ∀ (B U : List Nat) (e : Ev), U ≠ [] → push e (B ++ U) ≠ none →
    pushT e (B ++ U) = (low B e).2.2 + pushT (low B e).2.1 U := by
  intro B
  induction B with
  | nil => intro U e _ _; simp [low]
  | cons p B ih =>
    intro U e hU hn
    obtain ⟨q, R, hqR⟩ : ∃ q R, B ++ U = q :: R := by
      cases B with
      | nil => cases U with
        | nil => exact absurd rfl hU
        | cons q R => exact ⟨q, R, rfl⟩
      | cons q R => exact ⟨q, R ++ U, rfl⟩
    cases e with
    | none => simp [pushT, low, lev, low_none]
    | add a => simp [pushT, low, lev, low_none]
    | wave h =>
      simp only [List.cons_append, push] at hn
      rw [hqR] at hn
      show waveTime (p + h) (B ++ U) 0 = (low (p :: B) (.wave h)).2.2 + pushT (low (p :: B) (.wave h)).2.1 U
      rw [hqR]
      by_cases hd : (p + h) % 2 = 1
      · have ih' := ih U (.add ((p + h - 1) / 2)) hU (by rw [hqR]; simp [push])
        rw [hqR, show pushT (.add ((p + h - 1) / 2)) (q :: R) = 0 from rfl] at ih'
        simp only [waveTime, hd, ↓reduceIte, low, lev]
        generalize low B (.add ((p + h - 1) / 2)) = X at ih' ⊢
        obtain ⟨_, _, _⟩ := X
        simp only at ih' ⊢
        omega
      · simp only [wave, hd, ↓reduceIte] at hn
        have hn' : wave (q + (p + h) / 2) R ≠ none := by intro e; rw [e] at hn; exact hn rfl
        have ih' := ih U (.wave ((p + h) / 2)) hU (by rw [hqR]; exact hn')
        rw [hqR, show pushT (.wave ((p + h) / 2)) (q :: R) = waveTime (q + (p + h) / 2) R 0 from rfl] at ih'
        simp only [waveTime, hd, ↓reduceIte, low, lev]
        rw [waveTime_lin R _ _ hn', ih']
        generalize low B (.wave ((p + h) / 2)) = X
        obtain ⟨_, _, _⟩ := X
        simp only
        omega

/-- One super step of the bottom: what it becomes, what it passes on, and the steps it accounts for (with the 203
steps that every super step takes before and after its wave). -/
def bstep (B : List Nat) : List Nat × Ev × Nat := ((low B (.wave 10)).1, (low B (.wave 10)).2.1, 203 + (low B (.wave 10)).2.2)

theorem superL_split (B U : List Nat) (hU : U ≠ []) :
    superL (B ++ U) = (push (bstep B).2.1 U).map ((bstep B).1 ++ ·) := by
  rw [superL_push _ (by cases B <;> simp_all), push_split B U _ hU]; rfl

theorem superT_split (B U : List Nat) (hU : U ≠ []) (h : superL (B ++ U) ≠ none) :
    superT (B ++ U) = (bstep B).2.2 + pushT (bstep B).2.1 U := by
  obtain ⟨p, L, hpL⟩ : ∃ p L, B ++ U = p :: L := by
    cases B with
    | nil => cases U with
      | nil => exact absurd rfl hU
      | cons q R => exact ⟨q, R, rfl⟩
    | cons q R => exact ⟨q, R ++ U, rfl⟩
  have hw : wave (p + 10) L ≠ none := by rw [hpL] at h; exact h
  have hs := pushT_split B U (.wave 10) hU (by rw [← superL_push _ (by rw [hpL]; simp)]; exact h)
  rw [hpL] at hs ⊢
  simp only [superT, pushT] at hs ⊢
  rw [waveTime_lin L _ 3 hw, hs]
  simp only [bstep]
  omega

theorem leftEnd_ne : ∀ (f d : Nat) (W : List Nat), leftEnd f d = some W → W ≠ []
  | 0, _, _, h => by cases h
  | f + 1, d, W, h => by
    simp only [leftEnd] at h
    split at h
    · cases h
    · split at h
      · cases h; simp
      · cases e : leftEnd f (d / 2) <;> rw [e] at h <;> cases h; simp

theorem wave_ne : ∀ (L : List Nat) (d : Nat) (W : List Nat), wave d L = some W → W ≠ []
  | [], d, W, h => leftEnd_ne d d W h
  | p :: L, d, W, h => by
    simp only [wave] at h
    split at h
    · cases h; simp
    · cases e : wave (p + d / 2) L <;> rw [e] at h <;> cases h; simp

theorem push_ne : ∀ (e : Ev) (U U' : List Nat), U ≠ [] → push e U = some U' → U' ≠ []
  | .none, U, U', hU, h => by cases h; exact hU
  | .add a, [], U', hU, _ => absurd rfl hU
  | .add a, p :: U, U', _, h => by cases h; simp
  | .wave h, [], U', hU, _ => absurd rfl hU
  | .wave h, p :: U, U', _, e => wave_ne U (p + h) U' e

/-! ## Tables -/

/-- An entry: super steps since the last entry (at least 1), the event passed on at the last of them, and the steps
the bottom accounts for in them. -/
abbrev Entry := Nat × Ev × Nat

/-- `n` super steps of the bottom from `B` that pass nothing on, take `c` steps and end at `B'`. -/
def Quiet : Nat → List Nat → Nat → List Nat → Prop
  | 0, B, c, B' => c = 0 ∧ B' = B
  | n + 1, B, c, B' => (bstep B).2.1 = .none ∧ ∃ c', c = (bstep B).2.2 + c' ∧ Quiet n (bstep B).1 c' B'

/-- The entries `T` are what the bottom passes on from `B` to `B'`. -/
def Chain : List Nat → List Entry → List Nat → Prop
  | B, [], B' => B' = B
  | B, (dt, e, c) :: T, B'' => ∃ n c₁ Bm, dt = n + 1 ∧ Quiet n B c₁ Bm ∧ (bstep Bm).2.1 = e ∧
      c = c₁ + (bstep Bm).2.2 ∧ Chain (bstep Bm).1 T B''

/-- **The table `T` with tail `tl` is one period of the bottom `B`.** -/
def Rep (B : List Nat) (T : List Entry) (tl : Nat × Nat) : Prop := ∃ B', Chain B T B' ∧ Quiet tl.1 B' tl.2 B

theorem low_append : ∀ (B : List Nat) (p : Nat) (e : Ev),
    low (B ++ [p]) e = ((low B e).1 ++ [(lev p (low B e).2.1).1], (lev p (low B e).2.1).2.1,
      (low B e).2.2 + (lev p (low B e).2.1).2.2)
  | [], p, e => by simp [low]
  | q :: B, p, e => by
    simp only [List.cons_append, low, low_append B p]
    simp [Nat.add_assoc]

theorem bstep_append (B : List Nat) (p : Nat) :
    bstep (B ++ [p]) = ((bstep B).1 ++ [(lev p (bstep B).2.1).1], (lev p (bstep B).2.1).2.1,
      (bstep B).2.2 + (lev p (bstep B).2.1).2.2) := by
  simp only [bstep, low_append]
  simp [Nat.add_assoc]

/-! ### Quiet stretches -/

theorem quiet_trans : ∀ (a : Nat) (B : List Nat) (c : Nat) (B₁ : List Nat) (b c' : Nat) (B₂ : List Nat),
    Quiet a B c B₁ → Quiet b B₁ c' B₂ → Quiet (a + b) B (c + c') B₂ := by
  intro a
  induction a with
  | zero => intro B c B₁ b c' B₂ h₁ h₂; obtain ⟨rfl, rfl⟩ := h₁; simpa using h₂
  | succ a ih =>
    intro B c B₁ b c' B₂ h₁ h₂
    obtain ⟨hn, c₀, rfl, h₁⟩ := h₁
    rw [show a + 1 + b = (a + b) + 1 by omega]
    exact ⟨hn, c₀ + c', by omega, ih _ _ _ _ _ _ h₁ h₂⟩

theorem quiet_one (B : List Nat) (h : (bstep B).2.1 = .none) : Quiet 1 B (bstep B).2.2 (bstep B).1 :=
  ⟨h, 0, rfl, rfl, rfl⟩

/-- A quiet stretch of the bottom leaves the next level as it is. -/
theorem quiet_lift : ∀ (n : Nat) (B : List Nat) (c : Nat) (B' : List Nat) (p : Nat),
    Quiet n B c B' → Quiet n (B ++ [p]) c (B' ++ [p]) := by
  intro n
  induction n with
  | zero => intro B c B' p h; obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
  | succ n ih =>
    intro B c B' p h
    obtain ⟨hn, c₀, rfl, h⟩ := h
    have hb := bstep_append B p
    rw [hn] at hb
    simp only [lev, Nat.add_zero] at hb
    refine ⟨by rw [hb], c₀, by rw [hb], ?_⟩
    rw [hb]
    exact ih _ _ _ p h

theorem orbitT_succ {L W : List Nat} (j t : Nat) (h : superL L = some W) :
    orbitT (j + 1) L t = orbitT j W (t + superT L) := by
  simp [orbitT, h]

/-- A quiet stretch is a stretch of the orbit in which only the bottom changes. -/
theorem quiet_orbit : ∀ (n : Nat) (B : List Nat) (c : Nat) (B' U : List Nat) (t : Nat), U ≠ [] →
    Quiet n B c B' → orbitT n (B ++ U) t = some (B' ++ U, t + c) := by
  intro n
  induction n with
  | zero => intro B c B' U t _ h; obtain ⟨rfl, rfl⟩ := h; rfl
  | succ n ih =>
    intro B c B' U t hU h
    obtain ⟨hn, c₀, rfl, h⟩ := h
    have hs := superL_split B U hU
    rw [hn] at hs
    simp only [push, Option.map_some] at hs
    rw [orbitT_succ n t hs, superT_split B U hU (by rw [hs]; simp), hn, ih _ _ _ _ _ hU h]
    simp [pushT, Nat.add_assoc]

/-! ### A pass of the table -/

/-- The levels `U` over one pass of the table: each entry's event, and its steps with those of `U`. -/
def pass : List Entry → Nat × Nat → List Nat → Nat → Option (List Nat × Nat)
  | [], tl, U, t => some (U, t + tl.2)
  | (_, e, c) :: T, tl, U, t =>
    match push e U with
    | none => none
    | some U' => pass T tl U' (t + c + pushT e U)

/-- The super steps of a table. -/
def lenT (T : List Entry) : Nat := (T.map (·.1)).sum

theorem pass_sound : ∀ (T : List Entry) (tl : Nat × Nat) (B B' B₀ U U' : List Nat) (t t' : Nat), U ≠ [] →
    Chain B T B' → Quiet tl.1 B' tl.2 B₀ → pass T tl U t = some (U', t') →
    orbitT (lenT T + tl.1) (B ++ U) t = some (B₀ ++ U', t') := by
  intro T
  induction T with
  | nil =>
    intro tl B B' B₀ U U' t t' hU hc hq hp
    cases hc
    simp only [pass, Option.some.injEq, Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    simpa [lenT] using quiet_orbit _ _ _ _ _ t hU hq
  | cons x T ih =>
    obtain ⟨dt, e, c⟩ := x
    intro tl B B' B₀ U U' t t' hU hc hq hp
    obtain ⟨n, c₁, Bm, rfl, hq₁, he, rfl, hc⟩ := hc
    simp only [pass] at hp
    cases hU₁ : push e U with
    | none => rw [hU₁] at hp; cases hp
    | some U₁ =>
      rw [hU₁] at hp
      have hs := superL_split Bm U hU
      rw [he, hU₁] at hs
      simp only [Option.map_some] at hs
      have h₁ := ih tl _ B' B₀ U₁ U' _ t' (push_ne e U U₁ hU hU₁) hc hq hp
      rw [show lenT ((n + 1, e, c₁ + (bstep Bm).2.2) :: T) + tl.1 = n + ((lenT T + tl.1) + 1) by
        simp only [lenT, List.map_cons, List.sum_cons]; omega, orbitT_add, quiet_orbit _ _ _ _ _ t hU hq₁]
      simp only [Option.bind_some]
      rw [orbitT_succ _ _ hs, superT_split Bm U hU (by rw [hs]; simp), he]
      rw [show t + c₁ + ((bstep Bm).2.2 + pushT e U) = t + (c₁ + (bstep Bm).2.2) + pushT e U by omega]
      exact h₁

/-- `r` passes. -/
def passes : Nat → List Entry → Nat × Nat → List Nat → Nat → Option (List Nat × Nat)
  | 0, _, _, U, t => some (U, t)
  | r + 1, T, tl, U, t =>
    match pass T tl U t with
    | none => none
    | some (U', t') => passes r T tl U' t'

theorem pass_ne : ∀ (T : List Entry) (tl : Nat × Nat) (U U' : List Nat) (t t' : Nat), U ≠ [] →
    pass T tl U t = some (U', t') → U' ≠ [] := by
  intro T
  induction T with
  | nil => intro tl U U' t t' hU h; simp only [pass, Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]; exact hU
  | cons x T ih =>
    obtain ⟨dt, e, c⟩ := x
    intro tl U U' t t' hU h
    simp only [pass] at h
    cases hU₁ : push e U with
    | none => rw [hU₁] at h; cases h
    | some U₁ => rw [hU₁] at h; exact ih tl U₁ U' _ t' (push_ne e U U₁ hU hU₁) h

theorem passes_sound : ∀ (r : Nat) (T : List Entry) (tl : Nat × Nat) (B U U' : List Nat) (t t' : Nat), U ≠ [] →
    Rep B T tl → passes r T tl U t = some (U', t') → ∃ j, orbitT j (B ++ U) t = some (B ++ U', t') := by
  intro r
  induction r with
  | zero => intro T tl B U U' t t' _ _ h; cases h; exact ⟨0, rfl⟩
  | succ r ih =>
    intro T tl B U U' t t' hU hR h
    simp only [passes] at h
    cases e : pass T tl U t with
    | none => rw [e] at h; cases h
    | some x =>
      obtain ⟨U₁, t₁⟩ := x
      rw [e] at h
      obtain ⟨B', hc, hq⟩ := hR
      have h₁ := pass_sound T tl B B' B U U₁ t t₁ hU hc hq e
      obtain ⟨j, hj⟩ := ih T tl B U₁ U' t₁ t' (pass_ne T tl U U₁ t t₁ hU e) ⟨B', hc, hq⟩ h
      exact ⟨_ + j, by rw [orbitT_add, h₁]; exact hj⟩

/-! ### Building the table for one more level -/

theorem chain_append : ∀ (T₁ T₂ : List Entry) (S S' S'' : List Nat), Chain S T₁ S' → Chain S' T₂ S'' →
    Chain S (T₁ ++ T₂) S'' := by
  intro T₁
  induction T₁ with
  | nil => intro T₂ S S' S'' h₁ h₂; cases h₁; exact h₂
  | cons x T₁ ih =>
    obtain ⟨dt, e, c⟩ := x
    intro T₂ S S' S'' h₁ h₂
    obtain ⟨n, c₁, Bm, h1, h2, h3, h4, h5⟩ := h₁
    exact ⟨n, c₁, Bm, h1, h2, h3, h4, ih T₂ _ S' S'' h5 h₂⟩

/-- One pass of the level with block `p` over the table: what it passes on (the entries `out`, newest first), the
super steps and machine steps since its last event (`acc`), and its block at the end. -/
def lvPass : List Entry → Nat × Nat → Nat → Nat × Nat → List Entry → List Entry × (Nat × Nat) × Nat
  | [], tl, p, acc, out => (out, (acc.1 + tl.1, acc.2 + tl.2), p)
  | (dt, e, c) :: T, tl, p, acc, out =>
    match lev p e with
    | (p', .none, c') => lvPass T tl p' (acc.1 + dt, acc.2 + c + c') out
    | (p', e', c') => lvPass T tl p' (0, 0) ((acc.1 + dt, e', acc.2 + c + c') :: out)

theorem lvPass_chain : ∀ (T : List Entry) (tl : Nat × Nat) (B Bend B₀ S₀ Sx : List Nat) (p : Nat) (acc : Nat × Nat)
    (out : List Entry), Chain B T Bend → Quiet tl.1 Bend tl.2 B₀ → Chain S₀ out.reverse Sx →
    Quiet acc.1 Sx acc.2 (B ++ [p]) →
    ∃ S', Chain S₀ (lvPass T tl p acc out).1.reverse S' ∧
      Quiet (lvPass T tl p acc out).2.1.1 S' (lvPass T tl p acc out).2.1.2 (B₀ ++ [(lvPass T tl p acc out).2.2]) := by
  intro T
  induction T with
  | nil =>
    intro tl B Bend B₀ S₀ Sx p acc out hc hq ho ha
    cases hc
    exact ⟨Sx, ho, quiet_trans _ _ _ _ _ _ _ ha (quiet_lift _ _ _ _ p hq)⟩
  | cons x T ih =>
    obtain ⟨dt, e, c⟩ := x
    intro tl B Bend B₀ S₀ Sx p acc out hc hq ho ha
    obtain ⟨n, c₁, Bm, rfl, hq₁, rfl, rfl, hc⟩ := hc
    have hb := bstep_append Bm p
    have hq₂ := quiet_trans _ _ _ _ _ _ _ ha (quiet_lift _ _ _ _ p hq₁)
    simp only [lvPass]
    cases hl : lev p (bstep Bm).2.1 with
    | mk p' r =>
      obtain ⟨e', c'⟩ := r
      rw [hl] at hb
      cases e' with
      | none =>
        simp only
        have hq₃ := quiet_trans _ _ _ _ _ _ _ hq₂ (quiet_one (Bm ++ [p]) (by rw [hb]))
        rw [hb] at hq₃
        exact ih tl _ Bend B₀ S₀ Sx p' _ out hc hq (by simpa using ho)
          (by simpa [Nat.add_assoc] using hq₃)
      | add a =>
        simp only
        refine ih tl _ Bend B₀ S₀ _ p' (0, 0) _ hc hq ?_ ⟨rfl, rfl⟩
        rw [List.reverse_cons]
        refine chain_append _ _ _ _ _ ho ⟨acc.1 + n, acc.2 + c₁, Bm ++ [p], by omega, hq₂, by rw [hb], ?_, ?_⟩
        · rw [hb]; simp only; omega
        · rw [hb]; rfl
      | wave h =>
        simp only
        refine ih tl _ Bend B₀ S₀ _ p' (0, 0) _ hc hq ?_ ⟨rfl, rfl⟩
        rw [List.reverse_cons]
        refine chain_append _ _ _ _ _ ho ⟨acc.1 + n, acc.2 + c₁, Bm ++ [p], by omega, hq₂, by rw [hb], ?_, ?_⟩
        · rw [hb]; simp only; omega
        · rw [hb]; rfl

/-- `L` passes of the level with block `p`. -/
def buildAux : Nat → List Entry → Nat × Nat → Nat → Nat × Nat → List Entry → List Entry × (Nat × Nat) × Nat
  | 0, _, _, p, acc, out => (out, acc, p)
  | L + 1, T, tl, p, acc, out =>
    match lvPass T tl p acc out with
    | (out', acc', p') => buildAux L T tl p' acc' out'

/-- **The table for one more level**: `L` passes of the level with block `p` over the table `T`; the new table, its
tail, and the block at the end, which must be `p` again for the table to be a period (`build_rep`). -/
def build (T : List Entry) (tl : Nat × Nat) (p L : Nat) : List Entry × (Nat × Nat) × Nat :=
  match buildAux L T tl p (0, 0) [] with
  | (out, acc, p') => (out.reverse, acc, p')

theorem buildAux_chain : ∀ (L : Nat) (T : List Entry) (tl : Nat × Nat) (B Bend S₀ Sx : List Nat) (p : Nat)
    (acc : Nat × Nat) (out : List Entry), Chain B T Bend → Quiet tl.1 Bend tl.2 B → Chain S₀ out.reverse Sx →
    Quiet acc.1 Sx acc.2 (B ++ [p]) →
    ∃ S', Chain S₀ (buildAux L T tl p acc out).1.reverse S' ∧
      Quiet (buildAux L T tl p acc out).2.1.1 S' (buildAux L T tl p acc out).2.1.2 (B ++ [(buildAux L T tl p acc out).2.2]) := by
  intro L
  induction L with
  | zero => intro T tl B Bend S₀ Sx p acc out _ _ ho ha; exact ⟨Sx, ho, ha⟩
  | succ L ih =>
    intro T tl B Bend S₀ Sx p acc out hc hq ho ha
    obtain ⟨S', h₁, h₂⟩ := lvPass_chain T tl B Bend B S₀ Sx p acc out hc hq ho ha
    simp only [buildAux]
    exact ih T tl B Bend S₀ S' _ _ _ hc hq h₁ h₂

theorem build_rep (B : List Nat) (T : List Entry) (tl : Nat × Nat) (p L : Nat) (hR : Rep B T tl)
    (hp : (build T tl p L).2.2 = p) : Rep (B ++ [p]) (build T tl p L).1 (build T tl p L).2.1 := by
  obtain ⟨Bend, hc, hq⟩ := hR
  obtain ⟨S', h₁, h₂⟩ := buildAux_chain L T tl B Bend (B ++ [p]) (B ++ [p]) p (0, 0) [] hc hq rfl ⟨rfl, rfl⟩
  simp only [build] at hp ⊢
  rw [hp] at h₂
  exact ⟨S', h₁, h₂⟩

/-! ## The plan -/

/-- Run a plan: for each `(r, L)`, `r` passes of the current table, then the table for one more level, built over
`L` passes of the first explicit level, which must come back.  At the end, the explicit levels and the machine step. -/
def drive : List (Nat × Nat) → List Entry → Nat × Nat → List Nat → Nat → Option (List Nat × Nat)
  | [], _, _, U, t => some (U, t)
  | (r, L) :: plan, T, tl, U, t =>
    match passes r T tl U t with
    | some (p :: q :: U', t') =>
      if (build T tl p L).2.2 = p then drive plan (build T tl p L).1 (build T tl p L).2.1 (q :: U') t' else none
    | _ => none

theorem drive_sound : ∀ (plan : List (Nat × Nat)) (B : List Nat) (T : List Entry) (tl : Nat × Nat) (U U' : List Nat)
    (t t' : Nat), U ≠ [] → Rep B T tl → drive plan T tl U t = some (U', t') →
    ∃ j W, orbitT j (B ++ U) t = some (W, t') := by
  intro plan
  induction plan with
  | nil => intro B T tl U U' t t' _ _ h; cases h; exact ⟨0, _, rfl⟩
  | cons x plan ih =>
    obtain ⟨r, L⟩ := x
    intro B T tl U U' t t' hU hR h
    simp only [drive] at h
    cases e : passes r T tl U t with
    | none => rw [e] at h; cases h
    | some y =>
      obtain ⟨V, t₁⟩ := y
      rw [e] at h
      match V, h with
      | p :: q :: U₂, h =>
        simp only at h
        split at h
        · rename_i hp
          obtain ⟨j₁, h₁⟩ := passes_sound r T tl B U _ t t₁ hU hR e
          obtain ⟨j₂, W, h₂⟩ := ih (B ++ [p]) _ _ (q :: U₂) U' t₁ t' (by simp) (build_rep B T tl p L hR hp) h
          refine ⟨j₁ + j₂, W, ?_⟩
          rw [orbitT_add, h₁]
          simpa using h₂
        · cases h

/-- The table of no levels: every super step, the first level receives the wave 10. -/
def T₀ : List Entry := [(1, .wave 10, 203)]

theorem rep₀ : Rep [] T₀ (0, 0) := ⟨[], ⟨0, 0, [], rfl, ⟨rfl, rfl⟩, rfl, rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-- **A plan that runs is a bound**: if the plan from `[1, 6, 5, 0]` (at step 136) runs to machine step `t`, the
machine does not halt in its first `t` steps. -/
theorem runs_of_drive (plan : List (Nat × Nat)) (U : List Nat) (t : Nat) (h : drive plan T₀ (0, 0) [6, 1] 136 = some (U, t)) :
    ∃ c, steps t init = some c := by
  obtain ⟨j, W, hj⟩ := drive_sound plan [] T₀ (0, 0) [6, 1] U 136 t (by simp) rep₀ h
  exact runs_of_orbitT t ⟨j, hj⟩ (Nat.le_refl t)

end BB6b
