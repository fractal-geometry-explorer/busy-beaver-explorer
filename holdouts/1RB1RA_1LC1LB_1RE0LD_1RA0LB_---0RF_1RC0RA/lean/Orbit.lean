import Map

/-! # The orbit of blank tape under `G`, for a while (by evaluation)

`runOK N x` follows `G` for `N` applications from `x` and says whether none of them halts.  The kernel checks the
first 20,000 applications from `s [] 3 []` (the configuration blank tape reaches after 8 steps); compiled
evaluation (`native_decide`) the first 10,000,000, which is about 4.5·10^14 steps of the machine.  This is a floor,
not the way to the question (the C program `c/gs.c` follows the same map much further). -/

namespace H139325

def runOK : Nat → Node → Bool
  | 0, _ => true
  | n + 1, x => match G x with
    | none => false
    | some x' => runOK n x'

theorem runOK_sound (N : Nat) : ∀ x : Node, runOK N x = true → ∀ n, n ≤ N → orbitFrom x n ≠ none := by
  induction N with
  | zero => intro x _ n hn; rw [Nat.le_zero.1 hn]; simp [orbitFrom]
  | succ N ih =>
    intro x h n hn
    cases n with
    | zero => simp [orbitFrom]
    | succ n =>
      simp only [runOK] at h
      cases hF : G x with
      | none => rw [hF] at h; cases h
      | some x' =>
        rw [hF] at h
        simp only [orbitFrom, hF, Option.bind]
        exact ih x' h n (by omega)

/-- No halt among the first 20,000 applications of `G` (kernel). -/
theorem orbit_kernel : ∀ n, n ≤ 20000 → orbitFrom (.s [] 3 []) n ≠ none :=
  runOK_sound 20000 _ (by decide +kernel)

/-- No halt among the first 10,000,000 applications of `G` (compiled evaluation). -/
theorem orbit_native : ∀ n, n ≤ 10000000 → orbitFrom (.s [] 3 []) n ≠ none :=
  runOK_sound 10000000 _ (by native_decide)

end H139325
