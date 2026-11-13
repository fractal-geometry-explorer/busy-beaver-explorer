import Machine
import TM.ListFrame

/-!
# 1RB0LA_1RC---_0LD1RD_0RA0RE_0RF1RC_1LF0LA: the two sweeps of a pass, for every list of blocks

Between two visits to the wall the head crosses the list of blocks twice.  Both crossings are proved here for every
list (any number of blocks, any sizes) and any tape on both sides; the turn at the end of the list and the arrival
at the wall are not part of this file.

A block of size `j + 1` is `1^(3j+3) 0` on the tape.  With the head in state D on the cell before the last 1 of
the block to its left, the tape reads `D> 1 0 1 1 (111)^j` for the block (`blkR j`), then the next block.

* `rsweep`: `L D> blkR j1 ... blkR jn R` reaches `L blkL j1 ... blkL jn D> R`, where `blkL j` is `0 111 (011)^j`
  (the same cells, rewritten).
* `lsweep`: `L blkL j1 ... blkL jn A>0 000 R` reaches `L A>0 000 blkB j1 ... blkB jn R`, where `blkB j` is
  `0 1^(3j+3)`: every block is solid again, shifted four cells to the right.

Written by hand with `TM.cross_r`, `TM.cross_l` (one word) and `TM.seqR`, `TM.seqL'` (lists); kernel only.
-/

namespace H7846

open TM

/-- A block as state D meets it on the right: `1 0 1 1 (111)^j`. -/
def blkR (j : Nat) (R : Tape) : Tape := app [true, false, true, true] (rep j [true, true, true] R)

/-- A block after the rightward sweep, on the left of the head (nearest cell first): in tape order `0 111 (011)^j`. -/
def blkL (j : Nat) (L : Tape) : Tape := rep j [true, true, false] (app [true, true, true, false] L)

/-- A block after the leftward sweep, on the right of the head: `0 1^(3j+3)`. -/
def blkB (j : Nat) (R : Tape) : Tape := cons false (rep (j + 1) [true, true, true] R)

/-- D over `111`: it becomes `011`. -/
theorem d_unit (L R : Tape) :
    steps 3 ⟨app [] L, app [true, true, true] R, .D⟩ = some ⟨app [] (app [true, true, false] L), R, .D⟩ := rfl

/-- D over `1 0 1 1`: it becomes `0 1 1 1`. -/
theorem d_head (L R : Tape) :
    steps 6 ⟨L, app [true, false, true, true] R, .D⟩ = some ⟨app [true, true, true, false] L, R, .D⟩ := rfl

/-- D crosses one block. -/
theorem d_block (j : Nat) (L R : Tape) : ∃ n, steps n ⟨L, blkR j R, .D⟩ = some ⟨blkL j L, R, .D⟩ :=
  ⟨_, steps_seq trans (d_head L (rep j [true, true, true] R))
    (cross_r trans (u := []) d_unit j (app [true, true, true, false] L) R)⟩

/-- The rightward sweep over any list of blocks. -/
theorem rsweep (js : List Nat) (L R : Tape) :
    ∃ n, steps n ⟨L, sq blkR js R, .D⟩ = some ⟨sqr blkL js L, R, .D⟩ :=
  seqR trans blkR blkL (fun X => X) .D d_block js L R

/-- A at `0 000` with `011` on its left: the `011` becomes `111` on the right. -/
theorem a_unit (L R : Tape) :
    steps 11 ⟨app [true, true, false] L, app [false, false, false, false] R, .A⟩ =
      some ⟨L, app [false, false, false, false] (app [true, true, true] R), .A⟩ := rfl

/-- A at `0 000` with `0 111` on its left: the block is closed with a 0. -/
theorem a_head (L R : Tape) :
    steps 12 ⟨app [true, true, true, false] L, app [false, false, false, false] R, .A⟩ =
      some ⟨L, app [false, false, false, false] (cons false (app [true, true, true] R)), .A⟩ := rfl

/-- A crosses one block leftwards. -/
theorem a_block (j : Nat) (L R : Tape) :
    ∃ n, steps n ⟨blkL j L, app [false, false, false, false] R, .A⟩ =
      some ⟨L, app [false, false, false, false] (blkB j R), .A⟩ :=
  ⟨_, steps_seq trans (cross_l trans a_unit j (app [true, true, true, false] L) R)
    (a_head L (rep j [true, true, true] R))⟩

/-- The leftward sweep over any list of blocks. -/
theorem lsweep (js : List Nat) (L R : Tape) :
    ∃ n, steps n ⟨sqr blkL js L, app [false, false, false, false] R, .A⟩ =
      some ⟨L, app [false, false, false, false] (sq blkB js R), .A⟩ :=
  seqL' trans blkL blkB (fun X => app [false, false, false, false] X) .A a_block js L R

end H7846
