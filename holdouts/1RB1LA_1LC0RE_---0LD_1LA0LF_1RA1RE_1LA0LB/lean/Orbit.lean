import Map

/-! # The orbit of blank tape under `GA`, for a while (by evaluation)

`runOK N x` follows `GA` for `N` applications from `x` and says whether none of them halts.  The kernel checks the
first 20,000 applications from `v [1] []` (the configuration after the first step from blank tape); compiled
evaluation (`native_decide`) the first 10,000,000.  This is a floor, not the way to the question (the C program
`c/vsa.c` follows the same map much further, with step counts). -/

namespace H52677

def runOK : Nat → Node → Bool
  | 0, _ => true
  | n + 1, x => match GA x with
    | none => false
    | some x' => runOK n x'

theorem runOK_sound (N : Nat) : ∀ x : Node, runOK N x = true → ∀ n, n ≤ N → orbitA x n ≠ none := by
  induction N with
  | zero => intro x _ n hn; rw [Nat.le_zero.1 hn]; simp [orbitOf]
  | succ N ih =>
    intro x h n hn
    cases n with
    | zero => simp [orbitOf]
    | succ n =>
      simp only [runOK] at h
      cases hF : GA x with
      | none => rw [hF] at h; cases h
      | some x' =>
        rw [hF] at h
        simp only [orbitOf, hF, Option.bind]
        exact ih x' h n (by omega)

/-- No halt among the first 20,000 applications of `GA` (kernel). -/
theorem orbit_kernel : ∀ n, n ≤ 20000 → orbitA (.v [1] []) n ≠ none :=
  runOK_sound 20000 _ (by decide +kernel)

/-- No halt among the first 10,000,000 applications of `GA` (compiled evaluation). -/
theorem orbit_native : ∀ n, n ≤ 10000000 → orbitA (.v [1] []) n ≠ none :=
  runOK_sound 10000000 _ (by native_decide)

end H52677
