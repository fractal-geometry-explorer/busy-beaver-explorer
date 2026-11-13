import Machine
import Rules

/-!
# Where a halt would come from

In item terms (see `README.md`): a sweep whose signal passes item 0 (odd) and meets item 1 even with separator 1,
followed by an item `(0, 1)` and a further 1, halts.  This is one of the configurations the item model never
produces in the run simulated so far; the theorem only says that the halting transition is reachable from such a
sweep start, for all lengths.
-/

namespace H37988

open TM

theorem halt_case (a b : Nat) (R : Tape) :
    Halts trans ⟨blank, cons false (cons false (rep (a) [true, false, true, false] (cons true (cons false (cons false (rep (b) [true, false, true, false] (cons true (cons true (cons true (R)))))))))), .D⟩ :=
  ⟨_, _, to_halt a b R, rfl⟩

end H37988
