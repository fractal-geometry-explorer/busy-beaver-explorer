import ExitTab
import Orbit

/-!
# The map with the region closed for k < exitK: a halts-iff

`step2` extends the proved map `next` (Map.lean) to the region:

* Z_k at n = 2 goes to Z_(k+1) at n = 2 (`zw_zs2`, every k);
* Z_k with k odd and n = 12k + 9 halts (`zregion_halt`, every k);
* Z_0 with n ≥ 24 goes to the tail 1 or X_0 (`zw_zz0`, `zw_zz1`);
* every other start of the region with k < exitK has its fate in `exitTab` (checked in ExitTab.lean);
* anything else is `.stuck`: by `step2_stuck` only Z_k with k ≥ exitK and n < 12k + 12.

`halts_iff`: from any E-event whose orbit under `step2` never gets stuck, the machine halts exactly when the orbit
reaches `.halt`.  `halts_iff_blank` is the case of blank tape.
-/

namespace H70770

open TM

/-- The result of one extended E-step. -/
inductive Res where
  | ev (T : Tail) (n : Nat)
  | halt
  | stuck
  deriving DecidableEq, Repr

def step2 (T : Tail) (n : Nat) : Res :=
  match next T n with
  | some (T', n', _) => .ev T' n'
  | none =>
    match T with
    | .Z k =>
      if n = 2 then .ev (.Z (k + 1)) 2
      else if k % 2 = 1 ∧ n = 12 * k + 9 then .halt
      else if k = 0 ∧ 24 ≤ n then
        (if n % 2 = 0 then .ev .one (3 * ((n - 24) / 2) + 39) else .ev (.X 0) (3 * ((n - 25) / 2) + 38))
      else
        match lookup k n exitTab with
        | some .halt => .halt
        | some (.to n' T') => .ev T' n'
        | none => .stuck
    | _ => .stuck

theorem next_none {T : Tail} {n : Nat} (h : next T n = none) : ∃ k, T = .Z k ∧ (k = 0 ∨ n < 12 * k + 12) := by
  cases T with
  | one => simp [next] at h
  | X t => simp [next] at h
  | Y t => simp [next] at h
  | Z k =>
    simp only [next] at h
    split at h
    · rename_i hk; exact ⟨k, rfl, hk⟩
    · cases h

theorem step2_at {T : Tail} {n : Nat} {T' : Tail} {n' : Nat} (h : step2 T n = .ev T' n') :
    ∃ m, 1 ≤ m ∧ steps m (Ev n T) = some (Ev n' T') := by
  unfold step2 at h
  cases e : next T n with
  | some p =>
    obtain ⟨T₁, n₁, s⟩ := p
    rw [e] at h
    simp only [Res.ev.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨s, next_pos T n _ _ s e, next_sound T n _ _ s e⟩
  | none =>
    rw [e] at h
    simp only at h
    obtain ⟨k, rfl, _⟩ := next_none e
    simp only at h
    split at h
    · rename_i h2
      simp only [Res.ev.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      subst h2
      exact ⟨102, by omega, zw_zs2 k⟩
    split at h
    · cases h
    split at h
    · rename_i _ _ hz
      obtain ⟨rfl, hn⟩ := hz
      split at h
      · rename_i he
        simp only [Res.ev.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 24 := ⟨(n - 24) / 2, by omega⟩
        have := zw_zz0 m
        refine ⟨_, ?_, by rw [show (2 * m + 24 - 24) / 2 = m by omega]; exact this⟩
        omega
      · rename_i he
        simp only [Res.ev.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 25 := ⟨(n - 25) / 2, by omega⟩
        have := zw_zz1 m
        refine ⟨_, ?_, by rw [show (2 * m + 25 - 25) / 2 = m by omega]; exact this⟩
        omega
    · cases el : lookup k n exitTab with
      | none => rw [el] at h; cases h
      | some f =>
        rw [el] at h
        cases f with
        | halt => cases h
        | to n₁ T₁ =>
          simp only [Res.ev.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact entry_to exitTab_ok el

theorem step2_halt {T : Tail} {n : Nat} (h : step2 T n = .halt) : Halts trans (Ev n T) := by
  unfold step2 at h
  cases e : next T n with
  | some p => rw [e] at h; cases h
  | none =>
    rw [e] at h
    obtain ⟨k, rfl, _⟩ := next_none e
    simp only at h
    split at h
    · cases h
    split at h
    · rename_i hh; exact zregion_halt k n hh.1 hh.2
    split at h
    · split at h <;> cases h
    · cases el : lookup k n exitTab with
      | none => rw [el] at h; cases h
      | some f =>
        rw [el] at h
        cases f with
        | halt => exact entry_halt exitTab_ok el
        | to n₁ T₁ => cases h

/-- Where the extended map is undefined: only Z_k with k ≥ exitK, in the region. -/
theorem step2_stuck {T : Tail} {n : Nat} (h : step2 T n = .stuck) :
    ∃ k, T = .Z k ∧ exitK ≤ k ∧ n < 12 * k + 12 := by
  unfold step2 at h
  cases e : next T n with
  | some p => rw [e] at h; cases h
  | none =>
    rw [e] at h
    obtain ⟨k, rfl, hk⟩ := next_none e
    simp only at h
    split at h
    · cases h
    rename_i h2
    split at h
    · cases h
    rename_i h3
    split at h
    · split at h <;> cases h
    rename_i h4
    cases el : lookup k n exitTab with
    | some f => rw [el] at h; cases f <;> cases h
    | none =>
      have hK : exitK ≤ k := by
        apply Nat.le_of_not_lt
        intro hK
        have hs : special k n = false := by
          simp only [special, Bool.or_eq_false_iff, decide_eq_false_iff_not]; exact ⟨h2, h3⟩
        have := coverB_spec exitTab_cover hK (by omega) hs
        rw [el] at this; cases this
      refine ⟨k, rfl, hK, ?_⟩
      have : 0 < exitK := by decide
      omega

/-- `i` extended E-steps. -/
def orbit2 : Nat → Tail → Nat → Res
  | 0, T, n => .ev T n
  | i + 1, T, n =>
    match step2 T n with
    | .ev T' n' => orbit2 i T' n'
    | r => r

theorem orbit2_at : ∀ i T n T' n', orbit2 i T n = .ev T' n' → ∃ m, i ≤ m ∧ steps m (Ev n T) = some (Ev n' T')
  | 0, T, n, T', n', h => by
    simp only [orbit2, Res.ev.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨0, Nat.le_refl _, rfl⟩
  | i + 1, T, n, T', n', h => by
    simp only [orbit2] at h
    cases e : step2 T n with
    | ev T₁ n₁ =>
      rw [e] at h
      obtain ⟨a, ha, hs⟩ := step2_at e
      obtain ⟨b, hb, hs2⟩ := orbit2_at i T₁ n₁ T' n' h
      exact ⟨a + b, by omega, steps_seq trans hs hs2⟩
    | halt => rw [e] at h; cases h
    | stuck => rw [e] at h; cases h

theorem halts_back {a : Nat} {c c' : Config} (h : steps a c = some c') (hh : Halts trans c') : Halts trans c := by
  obtain ⟨b, d, h1, h2⟩ := hh
  exact ⟨a + b, d, steps_seq trans h h1, h2⟩

theorem orbit2_halt : ∀ i T n, orbit2 i T n = .halt → Halts trans (Ev n T)
  | 0, T, n, h => by simp [orbit2] at h
  | i + 1, T, n, h => by
    simp only [orbit2] at h
    cases e : step2 T n with
    | ev T₁ n₁ =>
      rw [e] at h
      obtain ⟨a, _, hs⟩ := step2_at e
      exact halts_back hs (orbit2_halt i T₁ n₁ h)
    | halt => exact step2_halt e
    | stuck => rw [e] at h; cases h

theorem steps_split : ∀ {a : Nat} {c c' : Config}, TM.steps trans a c = some c' →
    ∀ b, TM.steps trans (a + b) c = TM.steps trans b c'
  | 0, c, c', h, b => by simp [TM.steps] at h; subst h; simp
  | a + 1, c, c', h, b => by
    cases hs : TM.step trans c with
    | none => simp [TM.steps, hs] at h
    | some d =>
      have e : a + 1 + b = (a + b) + 1 := by omega
      rw [e, steps_succ_of_step trans _ hs]
      rw [steps_succ_of_step trans _ hs] at h
      exact steps_split h b

/-- **Halts iff the extended orbit halts**, for an E-event whose orbit never gets stuck. -/
theorem halts_iff (T : Tail) (n : Nat) (h : ∀ i, orbit2 i T n ≠ .stuck) :
    Halts trans (Ev n T) ↔ ∃ i, orbit2 i T n = .halt := by
  constructor
  · intro hh
    apply Classical.byContradiction
    intro hno
    apply not_halts_of_forall trans _ hh
    apply forall_of_unbounded trans (fun m => ∃ c, steps m (Ev n T) = some c)
    · intro i
      cases e : orbit2 i T n with
      | ev T' n' =>
        obtain ⟨m, hm, hs⟩ := orbit2_at i T n T' n' e
        exact ⟨m, hm, _, hs⟩
      | halt => exact absurd ⟨i, e⟩ hno
      | stuck => exact absurd e (h i)
    · intro m hm; obtain ⟨c, hc⟩ := hm; exact ⟨c, hc⟩
  · rintro ⟨i, hi⟩
    exact orbit2_halt i T n hi

/-- From blank tape: if the extended orbit never meets a Z_k with k ≥ exitK in the region, the machine halts
exactly when the extended orbit halts. -/
theorem halts_iff_blank (h : ∀ i, orbit2 i .one 0 ≠ .stuck) :
    HaltsFromBlank ↔ ∃ i, orbit2 i .one 0 = .halt := by
  rw [← halts_iff .one 0 h]
  constructor
  · rintro ⟨N, d, h1, h2⟩
    by_cases hN : 18 ≤ N
    · obtain ⟨b, rfl⟩ : ∃ b, N = 18 + b := ⟨N - 18, by omega⟩
      refine ⟨b, d, ?_, h2⟩
      rw [← steps_split init_E b]
      exact h1
    · exfalso
      obtain ⟨b, hb⟩ : ∃ b, 18 = N + (b + 1) := ⟨17 - N, by omega⟩
      have := steps_halt trans h1 h2 b
      rw [← hb] at this
      have e := init_E
      unfold steps at e
      rw [this] at e
      cases e
  · intro hh
    exact halts_back init_E hh

/-! ## Every exit of the region with k < exitK settles -/

/-- The E-event is one where the proved map applies, or a start n = 2 (which never halts, `zregion_two`). -/
def mapped (T : Tail) (n : Nat) : Bool := (next T n).isSome || (match T with | .Z _ => decide (n = 2) | _ => false)

/-- A start of the region beyond the table: Z_k with k ≥ exitK and n < 12k + 12. -/
def beyond (T : Tail) (n : Nat) : Bool := match T with | .Z k => decide (exitK ≤ k ∧ n < 12 * k + 12) | _ => false

/-- Where an exit has settled: a mapped E-event, or a start of the region beyond the table. -/
def settled (T : Tail) (n : Nat) : Bool := mapped T n || beyond T n

/-- Within `i` extended steps the orbit halts or reaches a settled E-event. -/
def settles : Nat → Tail → Nat → Bool
  | 0, _, _ => false
  | i + 1, T, n =>
    match step2 T n with
    | .halt => true
    | .stuck => false
    | .ev T' n' => settled T' n' || settles i T' n'

theorem settles_sound : ∀ i T n, settles i T n = true →
    Halts trans (Ev n T) ∨ ∃ m T' n', 1 ≤ m ∧ steps m (Ev n T) = some (Ev n' T') ∧ settled T' n' = true
  | 0, T, n, h => by simp [settles] at h
  | i + 1, T, n, h => by
    simp only [settles] at h
    cases e : step2 T n with
    | halt => exact .inl (step2_halt e)
    | stuck => rw [e] at h; cases h
    | ev T₁ n₁ =>
      rw [e] at h
      obtain ⟨a, ha, hs⟩ := step2_at e
      simp only [Bool.or_eq_true] at h
      rcases h with h | h
      · exact .inr ⟨a, T₁, n₁, ha, hs, h⟩
      · rcases settles_sound i T₁ n₁ h with h2 | ⟨b, T', n', hb, hs2, hm⟩
        · exact .inl (halts_back hs h2)
        · exact .inr ⟨a + b, T', n', by omega, steps_seq trans hs hs2, hm⟩

/-- Every start of the region in the table (every start with k < exitK other than n = 2 and the halting family),
followed by the extended map, halts or settles within 8 extended steps. -/
theorem exits_settle : exitTab.all (fun e => settles 8 (.Z e.1) e.2.1) = true := by native_decide

/-- **The exits of the region, for k < exitK**: every start `Ev n (.Z k)` of the region with k < exitK halts, or
reaches an E-event where `next` is defined (or a start n = 2, which never halts), or reaches a start Z_k' of the
region with k' ≥ exitK (the block of the tail can grow: for n = 7 mod 8 it is multiplied by 9/8). -/
theorem exit_reenters (k n : Nat) (hk : k < exitK) (hn : n < 12 * k + 12) :
    Halts trans (Ev n (.Z k)) ∨ ∃ m T' n', steps m (Ev n (.Z k)) = some (Ev n' T') ∧ settled T' n' = true := by
  by_cases h2 : n = 2
  · subst h2; exact .inr ⟨0, .Z k, 2, rfl, by simp [settled, mapped]⟩
  by_cases hh : k % 2 = 1 ∧ n = 12 * k + 9
  · exact .inl (zregion_halt k n hh.1 hh.2)
  have hs : special k n = false := by
    simp only [special, Bool.or_eq_false_iff, decide_eq_false_iff_not]; exact ⟨h2, hh⟩
  obtain ⟨f, hf⟩ := Option.isSome_iff_exists.mp (coverB_spec exitTab_cover hk (.inl hn) hs)
  have hm := lookup_mem k n f exitTab hf
  have := List.all_eq_true.mp exits_settle _ hm
  rcases settles_sound 8 (.Z k) n this with h | ⟨m, T', n', _, hs2, hm2⟩
  · exact .inl h
  · exact .inr ⟨m, T', n', hs2, hm2⟩

end H70770
