import Cascade

/-!
# The front of the cascade has no stream-independent speed law (machine-independent)

`Cascade.lean` turns the zone orbit into a cascade of one-bit cells.  The stranded block of the four F08 machines
is a run of cells with the bits `1 0 1` repeated (`blk36` takes 36 of them).  Fed the background, the stream
`P1 P1 P0` repeated, such a run passes every event on unchanged and comes back to its bits every three events
(`block_passes_background`): this is why the old zone sees exactly what it would see alone until the disturbance
from the new zone gets through.

How fast can a disturbance get through?  Measured on the real stream, the front moves about 3.3 cells per
doubling of the number of events, so it would need about `2^(k/3.3)` events to cross `k` cells.  A bound of that
kind cannot hold for every stream: `fast36` is a stream of 88 events that gets an `F`, which the background
never contains, out of 36 cells of the block, where the measured law asks for about 2,000.  The exhaustive search
of `c/worst.c` shows that 88 is the fewest for 36 cells (trusted); see the README.

Everything here is checked by Lean's kernel.
-/

namespace XS

/-- Read a stream: `F`, `0` for `P 0`, `1` for `P 1`. -/
def evOf : Char → Ev
  | 'F' => .F
  | '0' => .P false
  | _ => .P true

def evs' (s : String) : List Ev := s.toList.map evOf

/-- The background, one period. -/
def bg : List Ev := [.P true, .P true, .P false]

/-- 36 cells of the block, from its first cell (next to the new zone). -/
def blk36 : List Bool := (List.range 36).map (fun j => j % 3 != 1)

/-- Fed one period of the background, 36 cells of the block pass it on unchanged and are back to their bits. -/
theorem block_passes_background : run blk36 bg = (blk36, bg) := by decide

/-- The 88-event stream found by `c/worst.c`. -/
def fast36 : List Ev :=
  evs' "F100000011011001011100110001101101101101100010100110001100111101101101101101101101101100"

theorem fast36_length : fast36.length = 88 := by decide

/-- **A fast disturbance.** The 88 events of `fast36` get an `F` out of 36 cells of the block; the background
never does. -/
theorem fast36_gets_through : Ev.F ∈ (run blk36 fast36).2 := by decide

end XS
