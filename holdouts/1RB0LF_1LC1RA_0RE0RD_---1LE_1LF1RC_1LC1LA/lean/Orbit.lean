import Reset

/-! # The orbit of `1^44` for the first resets (by evaluation)

`runOK N s` follows `F` for `N` resets from `s` and says whether none of them halts.  The kernel checks the first
300 resets of the orbit of `1^44`; compiled evaluation (`native_decide`) the first 10,000 (t then has about 3,900
bits).  This is a floor, not the way to the question. -/

namespace H165234

def runOK : Nat → Node → Bool
  | 0, _ => true
  | n + 1, s => match F s with
    | none => false
    | some s' => runOK n s'

theorem runOK_sound (N : Nat) : ∀ s : Node, runOK N s = true → ∀ n, n ≤ N → orbitFrom s n ≠ none := by
  induction N with
  | zero => intro s _ n hn; rw [Nat.le_zero.1 hn]; simp [orbitFrom]
  | succ N ih =>
    intro s h n hn
    cases n with
    | zero => simp [orbitFrom]
    | succ n =>
      simp only [runOK] at h
      cases hF : F s with
      | none => rw [hF] at h; cases h
      | some s' =>
        rw [hF] at h
        simp only [orbitFrom, hF, Option.bind]
        exact ih s' h n (by omega)

/-- No halting state among the first 300 resets after `1^44` (kernel). -/
theorem orbit_300 : ∀ n, n ≤ 300 → orbitFrom (.z 44) n ≠ none :=
  runOK_sound 300 _ (by decide +kernel)

/-- No halting state among the first 10,000 resets after `1^44` (compiled evaluation). -/
theorem orbit_10000 : ∀ n, n ≤ 10000 → orbitFrom (.z 44) n ≠ none :=
  runOK_sound 10000 _ (by native_decide)

end H165234
