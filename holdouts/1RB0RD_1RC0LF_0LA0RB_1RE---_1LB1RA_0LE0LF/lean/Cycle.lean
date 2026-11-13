import Rules

/-!
# 1RB0RD_1RC0LF_0LA0RB_1RE---_1LB1RA_0LE0LF: the wall cycle `Z n R → Z (n + 3) R'`

Hand-written wrapper around the generated `Rules.lean`.  The tape is cut between cells 12 and 13 (cell 0 is the start
cell).  Left of the cut: blank tape, `n` words `1001111` (the wall), then `0100 111111 a b`.  Right of the cut: the
data.  `Z n R` has `a b = 0 1` and the head on the first data cell in state E.

* `reach_Z`: blank tape reaches `Z 7 R₀` in 2,035 steps.
* `cycle_B`, `cycle_F`: when the head comes back over the cut onto cell 12 in state B or F, with cells 11 and 12
  both 1, then `168 n + 575` steps later the configuration is `Z (n + 4) R` with the same data `R`
  (here the wall had `n + 1` words): seven sweeps of the wall, which never look at the data.

Between a `Z` and the next exit the machine works on the data and on cells 5..12 only (checked by `c/edge.c` on
every cycle it runs, not proved here: which exit a data word leads to is the open part).
-/

namespace H75248

open TM

/-- Left of the cut, read from the cut outwards: `b a 111111 0010`, then `n` wall words, then blank tape. -/
def wallL (a b : Bool) (n : Nat) : Tape :=
  cons b (cons a (app [true, true, true, true, true, true, false, false, true, false]
    (rep n [true, true, true, true, false, false, true] blank)))

/-- `Z n R`: wall of `n` words, `0 1` left of the cut, head on the first data cell in state E. -/
def Z (n : Nat) (R : Tape) : Config := ⟨wallL false true n, R, .E⟩

/-- The exit that starts a wall cycle: head on cell 12 (reading 1), cell 11 is 1, state `q` (B or F). -/
def Exit (q : St) (n : Nat) (R : Tape) : Config :=
  ⟨cons true (app [true, true, true, true, true, true, false, false, true, false]
    (rep n [true, true, true, true, false, false, true] blank)), cons true R, q⟩

/-- The tape the generated theorems end on is `wallL false true (n + 4)`. -/
theorem wall_end (n : Nat) :
    cons true (cons false (cons true (cons true (cons true (cons true (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons true (cons true (cons true (cons false (rep (n) [false, true, true, true, true, true, false] (cons false (cons true (cons true (cons true (cons true (cons true (cons false (cons false (cons true (cons true (cons true (cons true (cons true (cons false (cons false (cons true (cons true (cons true (cons true (cons true (cons false (cons false (cons true (blank)))))))))))))))))))))))))))))))))))))))))
      = wallL false true (n + 4) := by
  have h := rep_rotate n [true, true, true, true, false] [false, true, true, true, true, true, false]
    [true, true, true, true, false, false, true] rfl
    (app [false, true, true, true, true, true, false, false, true, true, true, true, true, false, false, true, true, true, true, true, false, false, true] blank)
  have h4 : app [true, true, true, true, false]
      (app [false, true, true, true, true, true, false, false, true, true, true, true, true, false, false, true, true, true, true, true, false, false, true] blank)
      = rep 4 [true, true, true, true, false, false, true] blank := rfl
  rw [h4, ← rep_add] at h
  exact congrArg (fun t => cons true (cons false (app [true, true, true, true, true, true, false, false, true, false] t))) h

/-- Blank tape reaches `Z 7 R₀`, `R₀ = 01010000010010001001`, in 2,035 steps. -/
theorem blank_reaches_Z :
    steps 2035 init = some (Z 7 (app [false, true, false, true, false, false, false, false, false, true, false,
      false, true, false, false, false, true, false, false, true] blank)) := reach_Z

/-- The wall cycle from an exit in state B. -/
theorem cycle_B (n : Nat) (R : Tape) : steps (168 * n + 575) (Exit .B (n + 1) R) = some (Z (n + 4) R) := by
  have h := wall_cycle_B n R
  rw [wall_end] at h
  exact h

/-- The wall cycle from an exit in state F. -/
theorem cycle_F (n : Nat) (R : Tape) : steps (168 * n + 575) (Exit .F (n + 1) R) = some (Z (n + 4) R) := by
  have h := wall_cycle_F n R
  rw [wall_end] at h
  exact h

end H75248
