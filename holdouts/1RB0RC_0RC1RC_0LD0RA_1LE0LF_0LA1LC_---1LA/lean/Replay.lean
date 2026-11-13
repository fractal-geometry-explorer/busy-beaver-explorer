import Cycle
import Arrive
import Period

/-!
# 1RB0RC_0RC1RC_0LD0RA_1LE0LF_0LA1LC_---1LA does not halt

The two computed facts that `Cycle.lean` asks for, obtained from two runs of the verified executor of `Exec.lean`
(`arrive_run`, `period_run`: compiled evaluation, `native_decide`) through its soundness theorem `run_sound`:

* `reach_cyc`: the run from blank tape reaches `cyc 16797709`;
* `grow_cyc`: for every `x`, `cyc (65 + 2 x)` reaches `cyc (65 + 2 (x + 160521464))` in at least one step;

and with `nonhalting_of_growth_cycle` (kernel): `nonhalt`.

Trust: the Lean kernel, plus the Lean compiler and interpreter for the `native_decide` evaluations (the two runs
here and the twelve cycle rules in `ExecData.lean`); the executor itself is not trusted, it is proved sound.
-/

namespace H65826

open TM

/-- The tokens of `cycToks n` stand for `cyc`, with `n` copies of `011` in the last block. -/
theorem den_cyc (ρ : Nat → Nat) (n : Cnt) : den ρ ⟨[], cycToks n, .E⟩ = cyc (n.eval ρ) := by
  simp only [den, cycToks, dn, Cnt.eval, dot, Nat.add_zero, cons_false_blank]
  rfl

/-- The run from blank tape reaches `cyc 16797709`. -/
theorem reach_cyc : ∃ n x, steps n init = some (cyc (65 + 2 * x)) := by
  obtain ⟨n, hn⟩ := run_sound T_ok _ arrive_run (fun _ => 0)
  rw [den_cyc] at hn
  exact ⟨n, 8398822, hn⟩

/-- One period of the growth cycle, for every value of the free count. -/
theorem grow_cyc (x : Nat) : ∃ n, 0 < n ∧ steps n (cyc (65 + 2 * x)) = some (cyc (65 + 2 * (x + 160521464))) := by
  obtain ⟨n, hpos, hn⟩ := run_pos T_ok 5581713 rfl period_run (fun _ => x)
  rw [den_cyc, den_cyc] at hn
  have e1 : Cnt.eval (fun _ => x) ⟨65, [2]⟩ = 65 + 2 * x := by simp [Cnt.eval, dot]
  have e2 : Cnt.eval (fun _ => x) ⟨321042993, [2]⟩ = 65 + 2 * (x + 160521464) := by
    simp only [Cnt.eval, dot]; omega
  rw [e1, e2] at hn
  exact ⟨n, hpos, hn⟩

/-- **The machine does not halt from blank tape.** -/
theorem nonhalt : ¬ HaltsFromBlank := nonhalting_of_growth_cycle reach_cyc grow_cyc

end H65826
