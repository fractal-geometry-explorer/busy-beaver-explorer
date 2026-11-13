import Model

/-!
# The block model as a function, and the run from blank tape

`sweep` does one step of the block model (all rounds with `q ≥ 4` at once), `runE` follows sweeps until the next
`P`, a halt, or `fuel` runs out, and `orbit k n` does `k` rounds from `P n`.  Each comes with a soundness theorem
about the machine, so evaluating them proves statements like "no halt in the first 10^N steps".
-/

namespace H145825

open TM

/-- Steps of `j` rounds starting from `q + 2j + 2`, `r + 1`. -/
def bulk (q r j : Nat) : Nat := j * (8 * q + 4 * r + 17) + 10 * (j * j)

theorem bulk_succ (q r j : Nat) : bulk q r (j + 1) = (8 * (q + 2 * j) + 4 * r + 27) + bulk q (r + 1) j := by
  simp only [bulk, Nat.succ_mul, Nat.mul_succ, Nat.mul_add, Nat.add_mul]
  omega

theorem rounds (S : List Nat) (q : Nat) : ∀ j p r,
    steps (bulk q r j) (E S (p + 1) (q + 2 * j + 2) (r + 1)) = some (E S (p + 1 + 2 * j) (q + 2) (r + 1 + j)) := by
  intro j
  induction j with
  | zero => intro p r; simp [bulk]
  | succ j ih =>
    intro p r
    have h1 := round S p (q + 2 * j) r
    have h2 := ih (p + 2) (r + 1)
    rw [show q + 2 * j + 4 = q + 2 * (j + 1) + 2 by omega] at h1
    rw [show p + 2 + 1 = p + 3 by omega, show p + 3 + 2 * j = p + 1 + 2 * (j + 1) by omega,
      show r + 1 + 1 = r + 2 by omega, show r + 2 + j = r + 1 + (j + 1) by omega] at h2
    rw [bulk_succ]
    rw [show 8 * (q + 2 * j) + 4 * r + 27 = 8 * (q + 2 * j) + 4 * r + 27 by rfl]
    exact steps_seq trans h1 h2

/-- Result of one sweep. -/
inductive Sw where
  | e (S : List Nat) (p q r t : Nat)
  | toP (n t : Nat)
  | halt (t : Nat)
  | unknown

def Sw.Sound (c : Config) : Sw → Prop
  | .e S p q r t => steps t c = some (E S p q r)
  | .toP n t => steps t c = some (P n)
  | .halt t => ∃ c', steps t c = some c' ∧ step c' = none
  | .unknown => True

def sweep (S : List Nat) (p q r : Nat) : Sw :=
  if p = 0 then
    (if S = [] ∧ r = 1 ∧ 1 ≤ q then .toP q (3 * (q - 1) + 4) else .unknown)
  else if r = 0 then .unknown
  else if 4 ≤ q then
    .e S (p + 2 * ((q - 2) / 2)) ((q - 2) % 2 + 2) (r + (q - 2) / 2) (bulk ((q - 2) % 2) (r - 1) ((q - 2) / 2))
  else if q = 3 then .e S (p + 2) 1 (r + 1) (4 * (r - 1) + 19)
  else if q = 2 then
    (if r = 1 then .e S (p + 2) 3 1 31
     else if r = 2 then .halt 20
     else .e ((p + 2) :: S) 1 (r - 2) 1 (8 * (r - 3) + 24))
  else if q = 1 then
    (match S with
     | [] => .e [] 0 (p + r + 4) 1 (8 * (r - 1) + 30)
     | x :: S' => .e S' x (p + r + 4) 1 (8 * (r - 1) + 30))
  else .unknown

theorem sweep_sound (S : List Nat) (p q r : Nat) : (sweep S p q r).Sound (E S p q r) := by
  unfold sweep
  by_cases hp : p = 0
  · subst hp
    simp only [if_true]
    by_cases h : S = [] ∧ r = 1 ∧ 1 ≤ q
    · obtain ⟨rfl, rfl, hq⟩ := h
      rw [if_pos ⟨rfl, rfl, hq⟩]
      obtain ⟨v, rfl⟩ : ∃ v, q = v + 1 := ⟨q - 1, by omega⟩
      simpa [Sw.Sound] using to_P v
    · rw [if_neg h]; exact True.intro
  obtain ⟨p, rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  simp only [Nat.add_one_ne_zero, if_false]
  by_cases hr : r = 0
  · rw [if_pos hr]; exact True.intro
  rw [if_neg hr]
  obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  by_cases h4 : 4 ≤ q
  · rw [if_pos h4]
    have h := rounds S ((q - 2) % 2) ((q - 2) / 2) p r
    rw [show (q - 2) % 2 + 2 * ((q - 2) / 2) + 2 = q by omega] at h
    simp only [Sw.Sound, Nat.add_sub_cancel]
    rw [show p + 1 + 2 * ((q - 2) / 2) = p + 1 + 2 * ((q - 2) / 2) by rfl] at h
    rw [show r + 1 + (q - 2) / 2 = r + 1 + (q - 2) / 2 by rfl] at h
    exact h
  rw [if_neg h4]
  by_cases h3 : q = 3
  · subst h3; simp only [if_true, Sw.Sound, Nat.add_sub_cancel]; exact sweep_q3 S p r
  rw [if_neg h3]
  by_cases h2 : q = 2
  · subst h2
    simp only [if_true]
    by_cases r1 : r + 1 = 1
    · rw [if_pos r1]; obtain rfl : r = 0 := by omega
      simp only [Sw.Sound]; exact sweep_q2r1 S p
    rw [if_neg r1]
    by_cases r2 : r + 1 = 2
    · rw [if_pos r2]; obtain rfl : r = 1 := by omega
      simp only [Sw.Sound]; exact sweep_halt S p
    rw [if_neg r2]
    obtain ⟨r, rfl⟩ : ∃ r', r = r' + 2 := ⟨r - 2, by omega⟩
    simp only [Sw.Sound, show r + 2 + 1 - 2 = r + 1 by omega, show r + 2 + 1 - 3 = r by omega]
    exact sweep_push S p r
  rw [if_neg h2]
  by_cases h1 : q = 1
  · subst h1
    simp only [if_true]
    cases S with
    | nil =>
      simp only [Sw.Sound, Nat.add_sub_cancel]
      rw [show p + 1 + (r + 1) + 4 = p + r + 6 by omega]
      exact sweep_pop_nil p r
    | cons x S =>
      simp only [Sw.Sound, Nat.add_sub_cancel]
      rw [show p + 1 + (r + 1) + 4 = p + r + 6 by omega]
      exact sweep_pop x S p r
  rw [if_neg h1]; exact True.intro

/-- Result of following sweeps to the next `P`. -/
inductive Res where
  | p (n t : Nat)
  | halt (t : Nat)
  | unknown

def Res.Sound (c : Config) : Res → Prop
  | .p n t => steps t c = some (P n)
  | .halt t => ∃ c', steps t c = some c' ∧ step c' = none
  | .unknown => True

def Res.addT (s : Nat) : Res → Res
  | .p n t => .p n (s + t)
  | .halt t => .halt (s + t)
  | .unknown => .unknown

theorem Res.sound_addT {c c' : Config} {s : Nat} (h : steps s c = some c') :
    ∀ o : Res, o.Sound c' → (o.addT s).Sound c
  | .p _ _, ho => steps_seq trans h ho
  | .halt _, ⟨d, hd, hn⟩ => ⟨d, steps_seq trans h hd, hn⟩
  | .unknown, _ => True.intro

def runE : Nat → List Nat → Nat → Nat → Nat → Res
  | 0, _, _, _, _ => .unknown
  | f + 1, S, p, q, r =>
    match sweep S p q r with
    | .e S' p' q' r' t => (runE f S' p' q' r').addT t
    | .toP n t => .p n t
    | .halt t => .halt t
    | .unknown => .unknown

theorem runE_sound : ∀ f S p q r, (runE f S p q r).Sound (E S p q r) := by
  intro f
  induction f with
  | zero => intro S p q r; exact True.intro
  | succ f ih =>
    intro S p q r
    have hs := sweep_sound S p q r
    simp only [runE]
    revert hs
    cases sweep S p q r with
    | e S' p' q' r' t => intro hs; exact Res.sound_addT hs _ (ih S' p' q' r')
    | toP n t => intro hs; exact hs
    | halt t => intro hs; exact hs
    | unknown => intro _; exact True.intro

/-- One round from `P n` (with `fuel` sweeps at most). -/
def pround (fuel n : Nat) : Res :=
  if 4 ≤ n then (runE fuel [] 2 (n - 2) 2).addT (5 * (n - 4) + 14) else .unknown

theorem pround_sound (fuel n : Nat) : (pround fuel n).Sound (P n) := by
  unfold pround
  by_cases h : 4 ≤ n
  · rw [if_pos h]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    have h1 := from_P m
    rw [show m + 4 - 4 = m by omega, show m + 4 - 2 = m + 2 by omega]
    exact Res.sound_addT h1 _ (runE_sound fuel [] 2 (m + 2) 2)
  · rw [if_neg h]; exact True.intro

/-- `k` rounds from `P n`: the end `(n', t)`, or `none` if a round halts or runs out of fuel. -/
def orbit (fuel : Nat) : Nat → Nat → Option (Nat × Nat)
  | 0, n => some (n, 0)
  | k + 1, n =>
    match pround fuel n with
    | .p n' t => (orbit fuel k n').map (fun x => (x.1, t + x.2))
    | _ => none

theorem orbit_sound (fuel : Nat) : ∀ k n n' t, orbit fuel k n = some (n', t) → steps t (P n) = some (P n') := by
  intro k
  induction k with
  | zero => intro n n' t h; simp [orbit] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  | succ k ih =>
    intro n n' t h
    have hs := pround_sound fuel n
    unfold orbit at h
    revert h hs
    cases pround fuel n with
    | halt _ => intro _ h; cases h
    | unknown => intro _ h; cases h
    | p m t₁ =>
      intro hs h
      simp only at h
      cases e2 : orbit fuel k m with
      | none => rw [e2] at h; cases h
      | some x =>
        rw [e2] at h
        simp at h
        obtain ⟨rfl, rfl⟩ := h
        exact steps_seq trans hs (ih m x.1 x.2 (by rw [e2]))

/-- From blank tape the machine is at `P 5` after 51 steps. -/
theorem init_P5 : steps 51 init = some (P 5) := by
  have h := blank_reaches trans (q := St.A) (n := 51)
    (c := ⟨[], [false, false, true, true, true, true, true, false, true], .E⟩) (by decide +kernel)
  simpa [FCfg.toCfg, P, app, rep] using h

/-- No halt in the first `51 + t` steps if `k` rounds from `P 5` take `t` steps. -/
theorem no_halt_of_orbit {fuel k n t : Nat} (h : orbit fuel k 5 = some (n, t)) : ∃ c, steps (51 + t) init = some c :=
  ⟨_, steps_seq trans init_P5 (orbit_sound fuel k 5 n t h)⟩

/-- The steps of `k` rounds from `P 5` (0 if the evaluation fails). -/
def orbitT (fuel k : Nat) : Nat := match orbit fuel k 5 with | some x => x.2 | none => 0

theorem no_halt_of_orbitT (fuel k : Nat) (h : (orbit fuel k 5).isSome = true) :
    ∃ c, steps (51 + orbitT fuel k) init = some c := by
  cases e : orbit fuel k 5 with
  | none => rw [e] at h; cases h
  | some x => obtain ⟨n, t⟩ := x; simp only [orbitT, e]; exact no_halt_of_orbit e

/-- 80 rounds without a halt (more than 10^100 steps), evaluated by the kernel. -/
theorem orbit_kernel : (orbit 1000000 80 5).isSome = true := by decide +kernel

theorem no_halt_kernel : ∃ c, steps (51 + orbitT 1000000 80) init = some c := no_halt_of_orbitT _ _ orbit_kernel

theorem kernel_bound : 10 ^ 100 < orbitT 1000000 80 := by decide +kernel

/-- 650 rounds without a halt (more than 10^9700 steps), by compiled evaluation. -/
theorem orbit_native : (orbit 1000000000 650 5).isSome = true := by native_decide

theorem no_halt_native : ∃ c, steps (51 + orbitT 1000000000 650) init = some c := no_halt_of_orbitT _ _ orbit_native

theorem native_bound : 10 ^ 9700 < orbitT 1000000000 650 := by native_decide

end H145825
