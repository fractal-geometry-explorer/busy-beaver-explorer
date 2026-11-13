import Blank

/-!
# The macro family, and three configurations of the run that are in it

`X(k, N, b)` is the configuration `C>0 1 0 1^(5k+3) 0 W_b(N)` with blank tape on both sides, where
`W_b(N) = 1 x₀ 1 x₁ … 1 x_(b-1)` writes N in binary, least significant bit first, each bit after a 1 (`xcells`).
The rules between these configurations are checked by simulation (`py/family.py`, `py/accel.py`); the single moves
they are made of (ticks of the counter, round start and end, the small restructure) are proved in `Rules.lean`:

* regular: `X(k, N, b) → X(k+1, N + 2^(k+1), b)` when `N + 2^(k+1) < 2^b`, in about `84·2^k` steps;
* small restructure: when `N` is odd and `N + 2^(k+1) ≥ 2^b`, with `M = N + 2^(k+1) − 2^b`,
  `X(k, N, b) → X(k, 2^(b+2) + 24 + (M − 1)/2, b + 3)`.

What is proved here is that the run from blank tape passes through `X(6, 215, 8)` at step 5,452 and through
`X(6, 1091, 11)` at step 9,079 (the small restructure with `M = 87`; kernel), and is `X(0, N₀, 64)` at step
3,145,810 with `N₀ = 9223585492820455065` (`native_decide`), the start of the epoch the run is still in at 10^11
steps.
-/

namespace H124655

open TM

/-- `W_b(N)`: the `b` low bits of `N`, least significant first, each after a 1. -/
def word : Nat → Nat → List Bool
  | 0, _ => []
  | b + 1, N => true :: (N % 2 == 1) :: word b (N / 2)

/-- The cells of `X(k, N, b)` from the head on. -/
def xcells (k N b : Nat) : List Bool :=
  [false, true, false] ++ List.replicate (5 * k + 3) true ++ [false] ++ word b N

/-- `X(k, N, b)` as a configuration. -/
def X (k N b : Nat) : Config := (⟨[], xcells k N b, .C⟩ : TM.FCfg St).toCfg

/-- At step 5,452 the run is `X(6, 215, 8)` (kernel). -/
theorem blank_X_5452 : steps 5452 init = some (X 6 215 8) :=
  blank_reaches trans (by decide +kernel)

/-- At step 9,079 the run is `X(6, 1091, 11)`: the small restructure from `X(6, 215, 8)` (kernel). -/
theorem blank_X_9079 : steps 9079 init = some (X 6 1091 11) :=
  blank_reaches trans (by decide +kernel)

/-- At step 3,145,810 the run is `X(0, 9223585492820455065, 64)` (`native_decide`). -/
theorem blank_X_epoch : steps 3145810 init = some (X 0 9223585492820455065 64) :=
  blank_reaches trans (by native_decide)

end H124655
