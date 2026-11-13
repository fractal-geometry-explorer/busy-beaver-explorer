import Phases

/-!
# The growth cycle of 1RB0RC_0RC1RC_0LD0RA_1LE0LF_0LA1LC_---1LA, and what it implies

`cyc r` is the configuration

    E> 0 (1011001)^59 1011 00000 1101100110110 (011)^16 001101100110 (011)^r

on an otherwise blank tape (state E at the left end).  The accelerated simulator `py/closure/accel.py` finds, by an
exact symbolic run (`py/closure/cycle.py check`), that for every x

    cyc (65 + 2 x)  reaches  cyc (65 + 2 (x + 160521464))

in 650373336347246654 + 8765861712 x steps (116,320,154 arrivals of state E at the left end), and that the run from
blank tape reaches `cyc 16797709` (16797709 = 65 + 2 * 8398822) after 1,818,198,163,340,705 steps.  What is proved
here, by the kernel, is that those two facts imply that the machine never halts.  The two facts themselves (without
the step counts) are proved in `Replay.lean` by a verified symbolic executor (`Exec.lean`).
-/

namespace H65826

open TM

/-- The configuration the run comes back to, with r words `011` in the block at the right end. -/
def cyc (r : Nat) : Config :=
  ⟨blank, cons false (rep 59 W (app [true, false, true, true, false, false, false, false, false, true, true, false, true, true, false, false, true, true, false, true, true, false]
    (rep 16 [false, true, true] (app [false, false, true, true, false, true, true, false, false, true, true, false] (rep r [false, true, true] blank))))), .E⟩

/-- If the run from blank tape reaches some `cyc (65 + 2 x)`, and every `cyc (65 + 2 x)` reaches
`cyc (65 + 2 (x + 160521464))` in at least one step, then the machine does not halt from blank tape. -/
theorem nonhalting_of_growth_cycle
    (reach : ∃ n x, steps n init = some (cyc (65 + 2 * x)))
    (grow : ∀ x, ∃ n, 0 < n ∧ steps n (cyc (65 + 2 * x)) = some (cyc (65 + 2 * (x + 160521464)))) :
    ¬ HaltsFromBlank := by
  have far : ∀ j, ∃ m, j ≤ m ∧ ∃ x, steps m init = some (cyc (65 + 2 * x)) := by
    intro j
    induction j with
    | zero =>
      obtain ⟨n, x, h⟩ := reach
      exact ⟨n, Nat.zero_le n, x, h⟩
    | succ j ih =>
      obtain ⟨m, hm, x, h⟩ := ih
      obtain ⟨n, hn, h'⟩ := grow x
      exact ⟨m + n, by omega, x + 160521464, steps_seq trans h h'⟩
  exact not_halts_of_forall trans
    (forall_of_unbounded trans (fun m => ∃ x, steps m init = some (cyc (65 + 2 * x))) far
      (fun m ⟨x, h⟩ => ⟨_, h⟩))

end H65826
