import Machine

/-!
# The rightward sweep in state D is a block transducer

In state D, moving right, the head crosses each of the five blocks

    c = 1000,  bb = 100100,  bc = 1001000,  bab = 10010100,  bac = 100101000

in the same state, without looking past the block, and leaves `0` followed by `10`s behind
(`1000 ↦ 0100`, `100100 ↦ 010100`, `1001000 ↦ 0101010`, `10010100 ↦ 01010100`, `100101000 ↦ 010101010`).
So it crosses any word made of these blocks, in a number of steps that adds up block by block (`dsweep`).
These are the words of the "Q encoding" the leftward sweep leaves behind (`1000`, `100`, `10` separated tape).
Kernel only.
-/

namespace H32641

open TM

/-- The five blocks. -/
inductive Blk where
  | c | bb | bc | bab | bac
  deriving DecidableEq, Repr

/-- The cells of a block, left to right. -/
def Blk.w : Blk → List Bool
  | .c => [true, false, false, false]
  | .bb => [true, false, false, true, false, false]
  | .bc => [true, false, false, true, false, false, false]
  | .bab => [true, false, false, true, false, true, false, false]
  | .bac => [true, false, false, true, false, true, false, false, false]

/-- What the sweep leaves in its place, left to right. -/
def Blk.v : Blk → List Bool
  | .c => [false, true, false, false]
  | .bb => [false, true, false, true, false, false]
  | .bc => [false, true, false, true, false, true, false]
  | .bab => [false, true, false, true, false, true, false, false]
  | .bac => [false, true, false, true, false, true, false, true, false]

/-- Steps to cross a block. -/
def Blk.s : Blk → Nat
  | .c => 6 | .bb => 10 | .bc => 27 | .bab => 14 | .bac => 31

theorem blk_cross (b : Blk) (L R : Tape) :
    steps b.s ⟨L, app b.w R, .D⟩ = some ⟨app b.v.reverse L, R, .D⟩ := by
  cases b <;> rfl

/-- A word of blocks, its cells, its image and its cost. -/
def word : List Blk → List Bool
  | [] => []
  | b :: l => b.w ++ word l

def image : List Blk → List Bool
  | [] => []
  | b :: l => b.v ++ image l

def cost : List Blk → Nat
  | [] => 0
  | b :: l => b.s + cost l

/-- **The D sweep**: any word of blocks is crossed in state D, block by block. -/
theorem dsweep (l : List Blk) (L R : Tape) :
    steps (cost l) ⟨L, app (word l) R, .D⟩ = some ⟨app (image l).reverse L, R, .D⟩ := by
  induction l generalizing L with
  | nil => rfl
  | cons b l ih =>
    have h1 := blk_cross b L (app (word l) R)
    have h2 := ih (app b.v.reverse L)
    simp only [word, image, cost, List.reverse_append]
    rw [← app_app] at *
    rw [← app_app]
    exact steps_seq trans h1 h2

end H32641
