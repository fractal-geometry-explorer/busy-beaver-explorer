import Orbit

/-! # The map against the README's table (evaluated, not proved)

The first overflows of `orbit`, in the README's event terms (X = Y − 2, M, j = d + 1).  These lines run the map
with Lean's evaluator (`#guard`); they are a check of the transcription in `py/phasemap.py`, not part of any proof. -/

namespace H140108

/-- The overflow phases among the first `n` phases of the orbit: (X, M, j) after each. -/
def overflowsX (n : Nat) : List (Nat × Nat × Nat) := Id.run do
  let mut out := []
  let mut st := (0, 2, 2)
  for _ in [0:n] do
    let (d, M, Y) := st
    match phase d M Y with
    | some (d', M', Y') =>
      if M' ≠ M then out := out ++ [(Y' - 2, M', d' + 1)]
      st := (d', M', Y')
    | none => break
  return out

-- the README table: 0000 0011 0001 001 (15, 5), 0000000000010000101 (19, 13), ...
#guard (overflowsX 200).take 9 ==
  [(3, 3, 3), (104, 7, 2), (5, 8, 5), (0b000000110001001, 15, 5), (0b0000000000010000101, 19, 13),
   (0b00000000000111111110000011, 26, 16), (0b000000111111111110000001001000, 30, 25),
   (0b0111110111111111110000001001001, 31, 31), (0b00000001111101111111111100000111101, 35, 30)]

end H140108
