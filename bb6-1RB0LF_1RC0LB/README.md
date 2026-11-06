# The six-state machine 1RB0LF_1RC0LB_1RD1RB_1RE1RF_1LA---_0RC1LA

Whether this machine halts from blank tape is open. This folder holds its work; the shared tools are in
[`../tools`](../tools). Its pages are the explainer [`../pages/1RB0LF_1RC0LB/explainer.html`](../pages/1RB0LF_1RC0LB/explainer.html)
and the proof status [`../pages/1RB0LF_1RC0LB/proof-status.html`](../pages/1RB0LF_1RC0LB/proof-status.html), both
built from [`status.json`](status.json). The log is [`notes/LAB_NOTES.md`](notes/LAB_NOTES.md).

## What is established

**Proved in Lean, kernel only** (`lean/Blank.lean`): the machine halts exactly when it is in E on a 1, and
`D>0 1` halts on the next step (`step_none_iff`, `halt_shape`); the tape after 63 steps (`blank_at_63`); no halt in
the first 20,000 steps (`blank_runs_20000`).

**Proved in Lean, kernel only** (`lean/Pass.lean`): which passes halt. A pass starts when F or B reads the first 0 of
a gap (a run of 0s between two 1s) and moves right; C crosses every gap of length 1 or 2, and the first gap of another
length ends the pass: 3 halts, 4 or more turns left at E, two 1s side by side turn left at B or F (`pass`,
`pass_outcome`). Also the leftward pieces: `sweep`, `erase` and how they end.

**Proved in Lean, kernel only** (`lean/Macro.lean`): the macro machine. At every pass start the tape is a stack of
even blocks, a head gap and a word of segments `(0 1)^m` and gaps `0^(2g) 1`; `mstep` maps one such configuration to
the next, and the machine follows it for all values of the parameters (`mstep_sound`). The rules fail in only two
cases (a gap `g = 0` next to an empty segment), so if the macro machine never gets stuck from the configuration after
12 steps, the machine never halts (`no_halt_of_macro`).

**Proved in Lean, kernel only** (`lean/Counter.lean`): a counter. Φ = (sum of the stack) + h + Σ(m + g − 1) is
kept by a pass that ends inside the word and by a B step with a nonempty stack, goes up by 2 or 1 when a pass runs into the last segment, and down
by 1 when B has an empty stack (`phi_interior`, `phi_end`, `phi_bottom`). Read as a recursive program (the two-stack
form's right stack is a call stack), Φ/2 counts the turns of the outermost loop, up to the rare
steps at the left end. It does not rule out getting stuck by itself.

**Proved in Lean, kernel only** (`lean/Parity.lean`): odd numbers are the only danger and come only from the left
end. A configuration whose stack entries, segments and gaps n = g − 1 are all even (the last segment is free) is never
stuck, and stays so until B has an empty stack (`even_not_stuck`, `even_step`, `even_run`). The number of odd
numbers goes up only when B has an empty stack, by exactly 1; a B step otherwise keeps it and a pass from F keeps it,
takes 2 off (two odd numbers cancel), or loses 1 at the last segment (`oddc_B`, `oddc_bottom`, `oddc_F`, `oddc_le`). So
after t steps there are at most 1 + (visits to the left end) odd numbers (`oddc_run`); in the first 3·10⁶ macro
steps there are 38 such visits and never more than 3 odd numbers.

**Proved in Lean with `native_decide`**: no halt in the first 10,000,000 steps (`blank_runs_10M`); the macro machine does not get stuck in its first 10⁸ steps, so no halt in the first 10⁸ machine steps
(`macro_runs_100M`, `blank_runs_macro_100M`, `lean/MacroRun.lean`).

**Computed** (trusted C/Python, tested): no halt in the first 10¹⁰ steps (`tools/c/tmrun.c`, 313 ones, 642 cells);
every one of the 344,806,676 pass starts in the first 10¹⁰ steps is the macro configuration `mstep` predicts, and
none is stuck (`c/macro.c`, `py/macro.py`); no conserved a·ones + b·pos + W[state] modulo 2 to 12 (`tools/py/bbtools/invariants.py`). At every pass start in the first
10¹⁰ steps no pass has a gap of 3 ahead of it, and every run of 0s or 1s of length 3 or more between cells of the
other symbol has even length: the parity invariant (`c/passes.c`, `py/passes.py`). No closed language of the simplest kinds exists: a pushdown
reduction that keeps one side of the tape exact and abstracts the other by a DFA fails for every DFA with at most
7 states, on either side (`c/pds.c`, `py/pds.py`).

**Observed only**: the width grows very slowly (199 cells at 10⁶ steps, 642 at 10¹⁰); D reading a 0 has had a 0
to its right every time so far; pass endings look like a binary counter, a gap of 4j + 2 about half as often as
4j − 2 (`notes/LAB_NOTES.md`).

**Computed** (trusted C, tested against Python): the two-stack form of the macro machine does not get stuck in its
first 5.1·10¹² steps (`c/fastrun.c`, about 4 s per 10⁹ steps; `c/twostack.c` to 2·10¹¹); it has two near misses (a
frame flipped down to 0), at steps 204,719,421 and 2,084,922,784, both harmless, and none after. Memoizing frames on
the inputs they inspect (`py/accel.py`) is exact but gives no real speed-up: the memo grows like steps^0.86.

**Observed only**: configurations that differ from the run's in one even entry can get stuck (`py/perturb.py`,
`c/twostack.c perturb`), so non-stuckness depends on exact values. But the run is no safer than these perturbed
copies: per flip it has the same statistics and a near-miss rate like theirs, and at their stuck rate (1.6·10⁻⁴ per
flip, 20 of 1,500 copies) its 1,181 flips in 10¹¹ steps would have got it stuck with probability only about 0.17.
Perturbed copies stay risky for as long as they run (10⁸ to 10⁹ steps), their risk falls at most slowly with the
run's age, and the run's flips do not thin out (about 200 per decade). So no structural reason for the run to stay
unstuck has shown up; if it behaves like its copies it halts with chance 2 to 3 % per decade of steps (`notes/LAB_NOTES.md`, 5 November).

**Open**: a proof that the macro machine never gets stuck, and the
question itself. Only odd numbers in the macro configuration can get it stuck, and in the first 10¹⁰ steps there
have never been more than 4 of them at once.

## Layout

| path | what it is |
|---|---|
| `lean/Machine.lean` | the machine, generated by `tools/py/bbtools/leangen.py` (namespace `BB6e`) |
| `lean/Blank.lean` | bounded runs from blank tape and the halting configurations |
| `lean/Pass.lean` | the pass and which passes halt, the leftward sweep and erase (kernel) |
| `lean/Macro.lean` | the macro machine: encoding, `mstep`, `mstep_sound`, `no_halt_of_macro` (kernel) |
| `lean/Counter.lean` | the counter Φ: kept by interior steps, changed only at the ends of the tape (kernel) |
| `lean/Parity.lean` | all-even configurations are safe; odd numbers are born only at the left end (kernel) |
| `lean/MacroRun.lean` | the macro machine run 10⁸ steps from M0 (`native_decide`), with the tail-recursive check proved equal to `mrun` |
| `lean/Axioms.lean` | prints what each theorem rests on |
| `lean/check.sh` | compiles the shared library, then the files above |
| `py/blank.py` | the run from blank tape on the shared simulator: summary, records, D reading a 0 |
| `py/passes.py` | pass starts, the predicted ending of each pass checked against the machine, the parity check |
| `c/passes.c` | the same checks in C, for billions of steps |
| `py/macro.py` | the macro machine as in Lean, checked against the run from blank tape; `show`, `stats` |
| `py/twostack.py` | the two-stack form of the macro machine (rules R1, R2) |
| `py/perturb.py` | configurations of the run with a few even numbers changed by 2, run on: some get stuck |
| `c/twostack.c` | the two-stack form in C, frames followed by identity (flips, near misses); `perturb` runs the control |
| `c/fastrun.c` | the two-stack form in plain C without frame identities, about twice as fast; saved states, near misses with their rows |
| `py/accel.py` | the two-stack form with frames memoized on their inspected inputs: exact, but the memo grows almost as fast as the run |
| `tests/test_accel.py` | `fastrun.c` and `accel.py` against `twostack.zstep` step by step, and against each other |
| `py/callstack.py` | the two-stack form read as a recursive program; the counter Φ by kind of step; flips at the caller |
| `c/macro.c` | the run and the macro machine side by side, the whole tape compared at every pass start |
| `py/pds.py` | the pushdown reduction: one side of the tape as a DFA, the other exact, post* saturation |
| `c/pds.c` | the same in C, enumerating every DFA up to a size |
| `tests/test_pds.py` | the reduction is sound on random small machines, Python against C |
| `tests/test_macro.py` | `mstep` against the machine on all small configurations, the run, Python against C |
| `tests/test_passes.py` | the pass rule against the machine on all short passes, Python against C |
| `tests/test_machine.py` | generated files and both pages current, C against Python, the facts in the notes |
| `status.json` | the source of both pages (`tools/pages/build_status.py`, `tools/pages/build_explainer.py`) |

Scripts for this machine go in `py/` (importing `bbtools` from `../../tools/py`), Lean files in `lean/` (added to
`check.sh` and `Axioms.lean`), tests in `tests/` (added to `.github/workflows/tests.yml`). Hand-written explainer
sections go in the `explainer.sections` list of `status.json`, so the page stays generated.

## Check

```sh
bash scripts/setup-lean.sh && . /etc/profile.d/lean.sh
bb6-1RB0LF_1RC0LB/lean/check.sh
python3 bb6-1RB0LF_1RC0LB/tests/test_machine.py
python3 bb6-1RB0LF_1RC0LB/tests/test_passes.py
# after editing status.json:
python3 tools/pages/build_status.py bb6-1RB0LF_1RC0LB/status.json pages/1RB0LF_1RC0LB/proof-status.html
python3 tools/pages/build_explainer.py bb6-1RB0LF_1RC0LB/status.json pages/1RB0LF_1RC0LB/explainer.html
```
