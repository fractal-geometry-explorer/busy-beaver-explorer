import Rounds

/-!
# The machine halts iff the orbit of a two-variable map reaches its halting set

`K2 a c` is the round start `A>0 1^a 0 1^c` (blank elsewhere).  The run from blank tape reaches `K2 74 30` at step
6,998 (`init_reach`, by the kernel), and from `K2 a c` (`a` even) the machine reaches `K2 a' c'` or halts, as
`mapc` says (`round_ok`, `round_halt`):

* `c` even:  `c ≤ a + 8` → `(a + 12 - c, 3c - 6)`;  `c = a + 10, a + 12` → halt;  `c ≥ a + 14` → `(c - a - 10, 3a + 27)`;
* `c` odd:   `c + 5 ≤ a` → `(a - c - 1, 3c + 6)`;  `c = a - 1, a - 3` → halt;  `c > a` → `(c - a + 3, 3a)`;
* `.small`: the cases with a block too short for the rules here (`a < 4`, `a` odd, `c < 18` with `c` even,
  `a = 4` with `c` even, `c < 5`).  The orbit from `(74, 30)` never meets one in its first 10^6 steps (checked in
  `py/orbit.py`, not here).

`halts_iff`: as long as the orbit never meets a `.small` case, the machine halts from blank tape if and only if
the orbit reaches `.halt`.
-/

namespace H35366

open TM

/-- The round start with two blocks. -/
def K2 (a c : Nat) : Config := ⟨blank, cons false (rep a [true] (cons false (rep c [true] blank))), .A⟩

/-- The outcome of a round of two blocks. -/
inductive Out where
  | ok (a c : Nat)
  | halt
  | small
  deriving DecidableEq, Repr

/-- The map. -/
def mapc (a c : Nat) : Out :=
  if a % 2 = 1 ∨ a < 4 then .small
  else if c % 2 = 0 then
    if c < 18 ∨ a < 6 then .small
    else if c ≤ a + 8 then .ok (a + 12 - c) (3 * c - 6)
    else if c ≤ a + 12 then .halt
    else .ok (c - a - 10) (3 * a + 27)
  else
    if c < 5 then .small
    else if c + 5 ≤ a then .ok (a - c - 1) (3 * c + 6)
    else if c < a then .halt
    else .ok (c - a + 3) (3 * a)

theorem rep_two (g : Nat) (s : Tape) : rep (2 * g) [true] s = rep g [true, true] s := by
  induction g with
  | zero => rfl
  | succ g ih =>
    rw [show 2 * (g + 1) = 2 * g + 1 + 1 by omega, rep_succ, rep_succ, ih]; rfl

theorem K2_ev {a c P Q : Nat} (ha : a = 2 * P) (hc : c = 2 * Q) : K2 a c = K [.ev P, .ev Q] := by
  subst ha; subst hc
  simp only [K2, K, enc, Blk.tape, rep_two]

theorem K2_od {a c P Q : Nat} (ha : a = 2 * P) (hc : c = 2 * Q + 1) : K2 a c = K [.ev P, .od Q] := by
  subst ha; subst hc
  simp only [K2, K, enc, Blk.tape, rep_succ, rep_two]; rfl

theorem start_odd' (P Q : Nat) (hP : 2 ≤ P) (hQ : 2 ≤ Q) :
    ∃ n, 0 < n ∧ steps n (K [.ev P, .od Q]) = some (K [.ev (P - 1), .od (Q - 1), .ev 3]) := by
  by_cases hp : P = 2
  · subst hp
    obtain ⟨n, hn, h'⟩ := start_odd_four (Q - 2)
    rw [show Q - 2 + 2 = Q by omega, show Q - 2 + 1 = Q - 1 by omega] at h'
    exact ⟨n, hn, h'⟩
  · obtain ⟨n, hn, h'⟩ := start_odd (P - 3) (Q - 2)
    rw [show P - 3 + 3 = P by omega, show Q - 2 + 2 = Q by omega, show Q - 2 + 1 = Q - 1 by omega,
      show P - 3 + 2 = P - 1 by omega] at h'
    exact ⟨n, hn, h'⟩

theorem start_even' (P Q : Nat) (hP : 3 ≤ P) (hQ : 9 ≤ Q) :
    ∃ n, 0 < n ∧ steps n (K [.ev P, .ev Q]) = some (K [.ev (P - 1), .od (Q - 8), .od 16]) := by
  obtain ⟨n, hn, h'⟩ := start_even (P - 3) (Q - 9)
  rw [show P - 3 + 3 = P by omega, show Q - 9 + 9 = Q by omega, show P - 3 + 2 = P - 1 by omega,
    show Q - 9 + 1 = Q - 8 by omega] at h'
  exact ⟨n, hn, h'⟩

theorem round_ok {a c a' c' : Nat} (h : mapc a c = .ok a' c') : ∃ n, 0 < n ∧ steps n (K2 a c) = some (K2 a' c') := by
  unfold mapc at h
  split at h
  · cases h
  next ha =>
  obtain ⟨P, rfl⟩ : ∃ P, a = 2 * P := ⟨a / 2, by omega⟩
  split at h
  next hc =>
    obtain ⟨Q, rfl⟩ : ∃ Q, c = 2 * Q := ⟨c / 2, by omega⟩
    split at h
    · cases h
    next hs =>
    obtain ⟨n₁, hn₁, h₁⟩ := start_even' P Q (by omega) (by omega)
    rw [K2_ev rfl rfl]
    split at h
    next h1 =>
      cases h
      obtain ⟨n₂, h₂⟩ := phase_lt (P - 1) (Q - 8) (by omega) (.od 16)
      rw [K2_ev (P := P - 1 - (Q - 8) - 1) (Q := 16 + 3 * (Q - 8) + 5) (by omega) (by omega)]
      exact ⟨n₁ + n₂, by omega, steps_seq trans h₁ h₂⟩
    next h1 =>
    split at h
    · cases h
    next h2 =>
      cases h
      obtain ⟨n₂, h₂⟩ := phase_ge (P - 1) (Q - 8) (by omega) (by omega) (.od 16)
      rw [K2_od (P := Q - 8 + 2 - (P - 1)) (Q := 16 + 3 * (P - 1)) (by omega) (by omega)]
      exact ⟨n₁ + n₂, by omega, steps_seq trans h₁ h₂⟩
  next hc =>
    obtain ⟨Q, rfl⟩ : ∃ Q, c = 2 * Q + 1 := ⟨c / 2, by omega⟩
    split at h
    · cases h
    next hs =>
    obtain ⟨n₁, hn₁, h₁⟩ := start_odd' P Q (by omega) (by omega)
    rw [K2_od rfl rfl]
    split at h
    next h1 =>
      cases h
      obtain ⟨n₂, h₂⟩ := phase_lt (P - 1) (Q - 1) (by omega) (.ev 3)
      rw [K2_od (P := P - 1 - (Q - 1) - 1) (Q := 3 + 3 * (Q - 1) + 4) (by omega) (by omega)]
      exact ⟨n₁ + n₂, by omega, steps_seq trans h₁ h₂⟩
    next h1 =>
    split at h
    · cases h
    next h2 =>
      cases h
      obtain ⟨n₂, h₂⟩ := phase_ge (P - 1) (Q - 1) (by omega) (by omega) (.ev 3)
      rw [K2_ev (P := Q - 1 + 2 - (P - 1)) (Q := 3 + 3 * (P - 1)) (by omega) (by omega)]
      exact ⟨n₁ + n₂, by omega, steps_seq trans h₁ h₂⟩

theorem round_halt {a c : Nat} (h : mapc a c = .halt) : ∃ n c', steps n (K2 a c) = some c' ∧ step c' = none := by
  unfold mapc at h
  split at h
  · cases h
  next ha =>
  obtain ⟨P, rfl⟩ : ∃ P, a = 2 * P := ⟨a / 2, by omega⟩
  split at h
  next hc =>
    obtain ⟨Q, rfl⟩ : ∃ Q, c = 2 * Q := ⟨c / 2, by omega⟩
    split at h
    · cases h
    next hs =>
    split at h
    · cases h
    next h1 =>
    split at h
    next h2 =>
      obtain ⟨n₁, -, h₁⟩ := start_even' P Q (by omega) (by omega)
      obtain ⟨n₂, c', h₂, hc'⟩ := phase_halt (P - 1) (Q - 8) (by omega) (by omega) (.od 16)
      rw [K2_ev rfl rfl]
      exact ⟨n₁ + n₂, c', steps_seq trans h₁ h₂, hc'⟩
    · cases h
  next hc =>
    obtain ⟨Q, rfl⟩ : ∃ Q, c = 2 * Q + 1 := ⟨c / 2, by omega⟩
    split at h
    · cases h
    next hs =>
    split at h
    · cases h
    next h1 =>
    split at h
    next h2 =>
      obtain ⟨n₁, -, h₁⟩ := start_odd' P Q (by omega) (by omega)
      obtain ⟨n₂, c', h₂, hc'⟩ := phase_halt (P - 1) (Q - 1) (by omega) (by omega) (.ev 3)
      rw [K2_od rfl rfl]
      exact ⟨n₁ + n₂, c', steps_seq trans h₁ h₂, hc'⟩
    · cases h

/-! ## From blank tape -/

/-- Step 6,998 from blank tape is the round start `(74, 30)` (kernel evaluation of the list simulator). -/
theorem init_reach : steps 6998 init = some (K2 74 30) :=
  blank_reaches trans (c := ⟨[], [false] ++ List.replicate 74 true ++ [false] ++ List.replicate 30 true, .A⟩)
    (by decide +kernel)

/-- The orbit of the map from `(74, 30)`; `.halt` and `.small` are final. -/
def orbit : Nat → Out
  | 0 => .ok 74 30
  | k + 1 => match orbit k with
    | .ok a c => mapc a c
    | o => o

theorem orbit_reach : ∀ k a c, orbit k = .ok a c → ∃ n, k ≤ n ∧ steps n init = some (K2 a c) := by
  intro k
  induction k with
  | zero => intro a c h; cases h; exact ⟨6998, by omega, init_reach⟩
  | succ k ih =>
    intro a c h
    cases hk : orbit k with
    | ok a₀ c₀ =>
      simp only [orbit, hk] at h
      obtain ⟨n, hn, hr⟩ := ih a₀ c₀ hk
      obtain ⟨n', hn', hr'⟩ := round_ok h
      exact ⟨n + n', by omega, steps_seq trans hr hr'⟩
    | halt => simp only [orbit, hk] at h; cases h
    | small => simp only [orbit, hk] at h; cases h

theorem orbit_halt : ∀ k, orbit k = .halt → ∃ j a c, orbit j = .ok a c ∧ mapc a c = .halt := by
  intro k
  induction k with
  | zero => intro h; cases h
  | succ k ih =>
    intro h
    cases hk : orbit k with
    | ok a c => simp only [orbit, hk] at h; exact ⟨k, a, c, hk, h⟩
    | halt => exact ih hk
    | small => simp only [orbit, hk] at h; cases h

/-- If the orbit stays in `.ok`, the machine never halts. -/
theorem not_halts_of_orbit (h : ∀ k, ∃ a c, orbit k = .ok a c) : ¬ HaltsFromBlank := by
  apply not_halts_of_forall
  apply forall_of_unbounded trans (fun m => ∃ c', steps m init = some c')
  · intro n
    obtain ⟨a, c, hk⟩ := h n
    obtain ⟨m, hm, hr⟩ := orbit_reach n a c hk
    exact ⟨m, hm, _, hr⟩
  · intro m hm; exact hm

/-- If the orbit reaches `.halt`, the machine halts. -/
theorem halts_of_orbit (k : Nat) (h : orbit k = .halt) : HaltsFromBlank := by
  obtain ⟨j, a, c, hj, hh⟩ := orbit_halt k h
  obtain ⟨n, -, hr⟩ := orbit_reach j a c hj
  obtain ⟨n', c', hr', hc⟩ := round_halt hh
  exact ⟨n + n', c', steps_seq trans hr hr', hc⟩

theorem orbit_cases (k : Nat) : (∃ a c, orbit k = .ok a c) ∨ orbit k = .halt ∨ orbit k = .small := by
  cases orbit k with
  | ok a c => exact Or.inl ⟨a, c, rfl⟩
  | halt => exact Or.inr (Or.inl rfl)
  | small => exact Or.inr (Or.inr rfl)

/-- **The reduction.**  If the orbit never meets a case too small for the rules, the machine halts from blank tape
exactly when the orbit reaches `.halt`. -/
theorem halts_iff (hs : ∀ k, orbit k ≠ .small) : HaltsFromBlank ↔ ∃ k, orbit k = .halt := by
  constructor
  · intro hb
    apply Classical.byContradiction
    intro hn
    apply not_halts_of_orbit _ hb
    intro k
    rcases orbit_cases k with h | h | h
    · exact h
    · exact absurd ⟨k, h⟩ hn
    · exact absurd h (hs k)
  · rintro ⟨k, hk⟩
    exact halts_of_orbit k hk

end H35366
