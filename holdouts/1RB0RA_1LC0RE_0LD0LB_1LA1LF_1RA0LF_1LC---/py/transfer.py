"""Generate lean/Transfer.lean for 1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---: the shuttle of a transfer.

In a transfer the head shuttles between the right end of the run being moved and the right end of the tape.  Once
the runs in between are *saturated* (each is `1 (0101)^(a+1)`: starts with 1, length 1 mod 4, at least 5 cells) a
shuttle changes nothing in between: it takes two cells `1 0` from the left run and adds four cells to the last run.
The four pieces of one shuttle are proved along the symbolic run of tools/py/bbtools/symtm.py; the hand-written part
chains them by induction over the list of runs in between, and then over the number of shuttles.

usage (from the repo root): python3 holdouts/1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---/py/transfer.py > holdouts/1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---/lean/Transfer.lean
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "py"))
from bbtools.symtm import prove  # noqa: E402

M = "1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---"
NS = next(l.split()[1] for l in open(os.path.join(HERE, "..", "lean", "Machine.lean")) if l.startswith("namespace "))

PIECES = [
    ("sh_right", "L A> 1 (0101)^a+1 R", "L 0 (1010)^a+1 A> R",
     "Going right, A crosses a saturated run `1 (0101)^(a+1)` and flips it."),
    ("sh_end", "L A> 1 (0101)^z 0^inf", "L B> 0 (0101)^z 0 1 0^inf",
     "The last run `1 (0101)^z` (z = 0 allowed) before blank tape: A flips it, adds two cells and turns; B is back at "
     "the run's first cell."),
    ("sh_left", "L 0 (1010)^a+1 B> 0 R", "L B> 0 (0101)^a 0 1 1 0 1 R",
     "Going left over a flipped saturated run: the doubled cell at its right end moves two cells to the left."),
    ("sh_turn", "L 1 0 0 B> 0 R", "L 0 A> 1 0 1 R",
     "The turn at the left: two cells `1 0` of the run being moved are used up and A starts the next shuttle."),
]

LOCAL = [
    ("loc_pass0", "L A> (0101)^n 1 R", "L (1010)^n 0 A> R",
     "Run boundary, going right, 0 cells left over (the run counted from A on a 0 has length 0 mod 4): A takes the "
     "first cell of the next run (a 1) and goes on.  Every cell is flipped."),
    ("loc_pass3", "L A> (0101)^n 0 1 0 0 R", "L (1010)^n 1 0 1 A> 0 R",
     "Run boundary, going right, length 3 mod 4: A is on the first cell of the next run (a 0) and goes on."),
    ("loc_turn1", "L 0 A> (0101)^n+1 0 0 R", "L B> 0 (0101)^n+1 0 1 R",
     "Run boundary, going right, length 1 mod 4: the head turns.  Back at the cell before the run (here a 0) the "
     "run is one cell longer and the next run has lost its first cell."),
    ("loc_turn2", "L 0 A> (0101)^n+1 0 1 1 R", "L B> 0 (0101)^n+1 0 1 0 R",
     "Run boundary, going right, length 2 mod 4: the head turns; the next run has lost its first cell."),
    ("loc_cross", "L 0 1 0 1 0 B> 0 R", "L B> 0 0 1 1 0 1 R",
     "Going left onto a run that ends `0 1 0 1 0` before a `00`: the doubled cell moves two cells to the left."),
    ("loc_bounce", "L 1 C> 1 1 R", "L 0 1 0 A> R",
     "Going left onto a run that ends in 1 before a `11`: the head turns right (a bounce); that run loses its last cell."),
    ("loc_halt", "L 1 1 0 B> 0 R", "L F> 1 1 0 1 R",
     "Going left onto a run `1 0` of length 2 between a `11` and a `00`: three steps later F reads a 1."),
]

LOCALTAIL = r'''
/-- ... and F on a 1 is the halting transition: the pattern of `loc_halt` halts after 4 steps. -/
theorem loc_halt_stops (L R : Tape) : step ⟨L, cons true R, .F⟩ = none := rfl

'''

TAIL = r'''
/-! ## One shuttle and m shuttles, for every list of saturated runs

`runs as R` is the right stream `1 (0101)^(a1+1) 1 (0101)^(a2+1) ... R` (run lengths `4a+5`), `passed as L` the
left stream once A has crossed and flipped them. -/

def runs : List Nat → Tape → Tape
  | [], R => R
  | a :: as, R => cons true (rep (a + 1) [false, true, false, true] (runs as R))

def passed : List Nat → Tape → Tape
  | [], L => L
  | a :: as, L => passed as (cons false (rep (a + 1) [true, false, true, false] L))

/-- What the way back leaves to the right of the head (after its cell). -/
def back : List Nat → Tape → Tape
  | [], R => R
  | a :: as, R => cons false (rep a [true, false, true, false] (cons true (cons true (cons false (cons true
      (back as R))))))

def rcst : List Nat → Nat
  | [] => 0
  | a :: as => (4 * a + 5) + rcst as

theorem right_chain : ∀ (as : List Nat) (L R : Tape),
    steps (rcst as) ⟨L, runs as R, .A⟩ = some ⟨passed as L, R, .A⟩
  | [], L, R => rfl
  | a :: as, L, R => by
    have h1 := sh_right a L (runs as R)
    have h2 := right_chain as (cons false (rep (a + 1) [true, false, true, false] L)) R
    exact steps_seq trans h1 h2

theorem sh_left' (a : Nat) (L R : Tape) :
    steps (4 * a + 5) ⟨cons false (rep (a + 1) [true, false, true, false] L), cons false R, .B⟩ =
      some ⟨L, cons false (cons false (rep a [true, false, true, false] (cons true (cons true (cons false
        (cons true R)))))), .B⟩ := by
  have h : cons false (rep (a + 1) [true, false, true, false] L) = rep (a + 1) [false, true, false, true] (cons false L) :=
    rep_rotate (a + 1) [false] [true, false, true, false] [false, true, false, true] rfl L
  rw [h]
  exact sh_left a L R

theorem left_chain : ∀ (as : List Nat) (L R : Tape),
    steps (rcst as) ⟨passed as L, cons false R, .B⟩ = some ⟨L, cons false (back as R), .B⟩
  | [], L, R => rfl
  | a :: as, L, R => by
    have h1 := left_chain as (cons false (rep (a + 1) [true, false, true, false] L)) R
    have h2 := sh_left' a L (back as R)
    exact steps_congr trans (by simp only [rcst]; omega) (steps_seq trans h1 h2)

/-- Re-bracketing `0 1 0 (1010)^n 1 = (0101)^(n+1)`. -/
theorem rot (n : Nat) (s : Tape) :
    cons false (cons true (cons false (rep n [true, false, true, false] (cons true s)))) =
      rep (n + 1) [false, true, false, true] s := by
  have h := rep_rotate n [false, true, false] [true, false, true, false] [false, true, false, true] rfl (cons true s)
  have h2 := rep_app_comm n [false, true, false, true] s
  rw [← h2]
  exact h

/-- After the way back and the turn the runs are as before, the last one four cells longer. -/
theorem back_runs : ∀ (as : List Nat) (z : Nat),
    cons true (cons false (cons true (back as (cons false (rep z [true, false, true, false] (cons true blank)))))) =
      runs as (cons true (rep (z + 1) [false, true, false, true] blank))
  | [], z => by
    show cons true (cons false (cons true (cons false (rep z [true, false, true, false] (cons true blank))))) =
      cons true (rep (z + 1) [false, true, false, true] blank)
    rw [rot]
  | a :: as, z => by
    show cons true (cons false (cons true (cons false (rep a [true, false, true, false] (cons true (cons true
      (cons false (cons true (back as (cons false (rep z [true, false, true, false] (cons true blank)))))))))))) =
      cons true (rep (a + 1) [false, true, false, true] (runs as (cons true (rep (z + 1) [false, true, false, true] blank))))
    rw [rot, back_runs as z]

/-- One shuttle over the saturated runs `as`: the left run loses `1 0`, the last run `1 (0101)^z` gains four
cells, nothing else changes.  `2 * rcst as + 8 * z + 8` steps. -/
theorem shuttle (as : List Nat) (z : Nat) (L : Tape) :
    steps (2 * rcst as + 8 * z + 8)
      ⟨cons false (cons false (cons true L)), runs as (cons true (rep z [false, true, false, true] blank)), .A⟩ =
      some ⟨cons false L, runs as (cons true (rep (z + 1) [false, true, false, true] blank)), .A⟩ := by
  have h1 := right_chain as (cons false (cons false (cons true L))) (cons true (rep z [false, true, false, true] blank))
  have h2 := sh_end z (passed as (cons false (cons false (cons true L))))
  have h3 := left_chain as (cons false (cons false (cons true L))) (cons false (rep z [true, false, true, false] (cons true blank)))
  have h4 := sh_turn L (back as (cons false (rep z [true, false, true, false] (cons true blank))))
  rw [back_runs as z] at h4
  exact steps_congr trans (by omega) (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 h4)))

def scst (as : List Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | m + 1, z => (2 * rcst as + 8 * z + 8) + scst as m (z + 1)

/-- m shuttles: `L (10)^m 0 A> 1 (0101)^(a1+1) ... 1 (0101)^z 0^inf` becomes
`L 0 A> 1 (0101)^(a1+1) ... 1 (0101)^(z+m) 0^inf`: 2m cells leave the left run, 4m arrive at the right end. -/
theorem shuttles (as : List Nat) : ∀ (m z : Nat) (L : Tape),
    steps (scst as m z)
      ⟨cons false (rep m [false, true] L), runs as (cons true (rep z [false, true, false, true] blank)), .A⟩ =
      some ⟨cons false L, runs as (cons true (rep (z + m) [false, true, false, true] blank)), .A⟩
  | 0, z, L => rfl
  | m + 1, z, L => by
    have h1 := shuttle as z (rep m [false, true] L)
    have h2 := shuttles as m (z + 1) L
    have e : z + 1 + m = z + (m + 1) := by omega
    rw [e] at h2
    exact steps_seq trans h1 h2

/-- The step count of m shuttles in closed form. -/
theorem scst_eq (as : List Nat) : ∀ (m z : Nat), scst as m z = m * (2 * rcst as + 8 * z + 8) + 4 * m * (m - 1)
  | 0, _ => by simp [scst]
  | m + 1, z => by
    rw [scst, scst_eq as m (z + 1)]
    cases m with
    | zero => simp
    | succ k =>
      simp only [Nat.add_sub_cancel]
      generalize rcst as = r
      have e1 : (k + 1) * (2 * r + 8 * (z + 1) + 8) = (k + 1) * (2 * r + 8 * z + 8) + 8 * (k + 1) := by
        rw [show 2 * r + 8 * (z + 1) + 8 = (2 * r + 8 * z + 8) + 8 by omega, Nat.mul_add, Nat.mul_comm (k + 1) 8]
      have e2 : (k + 1 + 1) * (2 * r + 8 * z + 8) = (k + 1) * (2 * r + 8 * z + 8) + (2 * r + 8 * z + 8) := by
        rw [Nat.add_mul, Nat.one_mul]
      have e3 : 4 * (k + 1) * k = 4 * (k * k) + 4 * k := by
        rw [Nat.mul_assoc, Nat.add_mul, Nat.one_mul, Nat.mul_add]
      have e4 : 4 * (k + 1 + 1) * (k + 1) = 4 * (k * k) + 12 * k + 8 := by
        rw [Nat.mul_assoc, show (k + 1 + 1) * (k + 1) = k * k + 3 * k + 2 by
          rw [Nat.add_mul, Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega]
        omega
      rw [e1, e2, e3, e4]
      omega

'''


def main():
    out = ["import Machine", "",
           f"/-! The shuttle of a transfer of {M}, generated by `py/transfer.py`; do not edit by hand. -/", "",
           f"namespace {NS}", "", "open TM", ""]
    for name, a, b, doc in PIECES:
        th, _ = prove(M, name, a, b, doc=doc, rotate=True, count_first=True, max_seg=40)
        out.append(th)
        out.append("")
    out.append(TAIL)
    out.append("/-! ## The events at a run boundary (for every surrounding tape) -/\n")
    for name, a, b, doc in LOCAL:
        th, _ = prove(M, name, a, b, doc=doc, rotate=True, count_first=True, max_seg=40)
        out.append(th)
        out.append("")
    out.append(LOCALTAIL)
    out.append(f"end {NS}")
    sys.stdout.write("\n".join(out) + "\n")


if __name__ == "__main__":
    main()
