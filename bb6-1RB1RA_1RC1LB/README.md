# The six-state machine 1RB1RA_1RC1LB_1LD0RA_---0LE_1LC0LF_1RE0LB

Whether this machine halts from blank tape is open. This folder holds its work; the shared tools are in
[`../tools`](../tools), the proof-status page is [`../pages/1RB1RA_1RC1LB/proof-status.html`](../pages/1RB1RA_1RC1LB/proof-status.html)
(built from [`status.json`](status.json)), and the log is [`notes/LAB_NOTES.md`](notes/LAB_NOTES.md). Two more pages
explain the run: [`reduction.html`](../pages/1RB1RA_1RC1LB/reduction.html), the reduction to the number N with what
each link rests on, and [`explainer.html`](../pages/1RB1RA_1RC1LB/explainer.html), which runs the machine in the browser
at each level.

## What is established

**Proved in Lean, kernel only** (`lean/`):
- the macro step: with `X(ls, n, cs) = 0^∞ 1^{l_r} 0 … 0 1^{l_1} 0 A> 1^n 000 1^{c_1} 00 … 00 1^{c_s} 0^∞`, the
  machine goes from every `X` where the list function `next` says, in the steps it says (`next_sound`);
- **the machine halts from blank tape iff the macro run halts** (`halts_iff`), and a macro step halts iff `n` is odd
  and every left block, after `l_1 += n/2`, is 2 (`next_halt_iff`);
- **the machine halts from blank tape iff N = 10 + Σ p_l·2^(m−l) is a power of two at some super step**
  (`halts_iff_pow2'`, `lean/Wave.lean`): every fourth time A stands on the blank right of the tape, the tape is
  p₁ … pₘ then 5, 0, the next such tape is `superstep P` (a wave of halvings going left: `super_run`, for every list),
  and a super step halts iff N is a power of two (`superL_none_iff`); the orbit starts at (1, 6);
- **the step count of the super step** (`super_steps`, `lean/WaveTime.lean`): from the tape p₁ … pₘ 5 0 the machine
  reaches the next one in exactly `superT` steps (or halts right after that many): 200, then 2q² + q − 5 for each block
  the wave passes with even d = 2q, then 2q² + 4q + 17 + A where it turns at an odd d = 2q + 1 (A is 3 plus q + 1 per
  block passed; at the left end the wave goes on with p = 0, and a halt there costs 11);
- the block rules behind it (`transfer`, `empty_start`, `sweep_step`, `carry_*`) and the shift rules `a_sweep`,
  `b_sweep`, for every block length;
- **no halt in the first 1.4·10¹⁶ steps** (`blank_runs_1_4e16`, `lean/OrbitKernel.lean`: the first 10⁷ super steps,
  checked in 1,000 chunks by `check_orbit.sh`, about three CPU hours); within `check.sh`, no halt in the first 2·10¹⁰
  steps (`blank_runs_2e10`, 10⁵ macro steps) and in the first 20,000 step by step;
- **each level cycles, or the machine never halts** (`cycles_or_never_halts`, `lean/Cycles.lean`): from any state the
  last k blocks either cycle or go silent, and a silent bottom on the orbit means no halt; the cycles of the last 1 to
  6 blocks are checked on the orbit (`cycle₁`–`cycle₆`). Which case holds for larger k is not decided;
- **each level multiplies the period by 1, 2, 4 or 5** (`period_factor`, `lean/Periods.lean`): mod 5 a wave acts on a
  block as p ↦ 3(p + h), so over a period the next block moves mod 5 by r ↦ 3^W r + b (W the waves it receives), the
  blocks of a cycle are distinct mod 5, and the factor is the period of the residue under that affine map: 1 or 4 if W
  is odd, 1 or 2 if W ≡ 2 mod 4, 1 or 5 if W ≡ 0 mod 4.

**Proved in Lean with `native_decide`**: **no halt in the first 4.4·10³⁷ steps** (`blank_runs_4e37`,
`lean/CascadeRun.lean`, about 4 minutes), with the tables below, proved sound in Lean (`lean/Cascade.lean`, kernel only:
the last blocks run on their own, and a table built for one more level is checked to be a period). Independently, by
the plain orbit: no halt in the first 10²⁴ steps (`blank_runs_1e24`, `lean/OrbitNative.lean`: the first 9.9·10¹⁰
super steps, the kernel's 10⁷ and then 99 chunks, `check_orbit.sh all`). Within `check.sh` also 9·10¹³ steps
(`blank_runs_9e13`, 10⁷ macro steps) and 10,000,000 step by step (`blank_runs_10M`).

**Computed** (trusted C/Python, tested): the macro model `py/macro.py` (matches direct simulation at every macro
configuration of the first 1,000 macro steps); no conserved quantity a·ones + b·pos + W[state] modulo 2 to 12
(`tools/py/bbtools/invariants.py`).

**Computed, resting on the wave model** (`py/waves.py`, `c/blkrun.c`, `tests/test_waves.py`; checked against direct
simulation and against `py/macro.py`): the finer events (each time A is at the right end, four per super step) and
their step counts; the sum over a super step is the proved `superT`.
The wave goes v₂(N) + 1 blocks deep and reaches the left end of the tape when 2^(m−1) divides N (which is why the
head gets there so rarely: the next time after step 2,047,931 is step 26,618,972,322, confirmed by a direct run).

**Computed, by skipping over cycles** (`c/superrun.c`, `py/superrun.py`, `tests/test_superrun.py`; checked against
`c/blkrun.c`, a direct run and `py/waves.py`): read from the right end, the super step is a cascade in which each block
only passes something to the block on its left, so the last k blocks are a closed system, and they fall into exact
cycles (the last 44 repeat every 1.8·10²¹ super steps). Tabulating those cycles, the orbit runs 6·10²³ super steps
with no halt: **no halt in the first 2.7·10⁴⁹ steps** (the orbit is proved to decide halting and the step formula is
proved, `superT`; the run itself is C). With `-r` it prints the period rule for each level: all 44 factors are the ones the
mod-5 rule predicts (`runs/periods_rules.txt`), a settled level remembers only its block mod 5, and a wave passes the
last k blocks at the rate 1.2764·2^−k per super step (N's low bits lean towards 0 by that constant factor).

**Observed only**: no macro configuration up to 9·10¹³ steps comes near the halting shape (left blocks in the
hundreds of thousands); see the notes.

**No invariant found** (heuristic; `py/n_search.py`, resting on the wave model): nothing tried keeps N off the powers
of two. N takes every power-of-two residue mod each odd q ≤ 127, also jointly with its bit length; its binary digits
look random; block growth bounds cannot help since halting depends only on the sum N; and the super step from 3,600
small tapes halts at the rate a random deciding number predicts (217 against about 239). A proof has to use
something special about the blank-tape orbit.

## Prior work

It is an open holdout, unannotated in the community ledger's "Cubic Mess" class, and not a named cryptid. Google
DeepMind's [cryptids](https://github.com/google-deepmind/cryptids) repository lists it as an open problem with a Lean
reduction to a map on stacks of block lengths (27 October 2026), the level of `lean/Macro.lean`; nothing found goes
as far as the criterion on N. Its map is not Antihydra's or Hydra's. One machine merged into an equivalence class by
bbchallenge, `1RB1RA_1RC1LB_1LD0RA_1RA0LE_---0LF_0RD0LB`, runs through the same tapes. Details and sources:
[`notes/PRIOR_WORK.md`](notes/PRIOR_WORK.md).

## Layout

| path | contents |
|---|---|
| `lean/Machine.lean` | the machine, generated by `tools/py/bbtools/leangen.py` |
| `lean/rules.py` → `lean/Rules.lean` | rules proved along the symbolic run (generated; do not edit the `.lean`) |
| `lean/Blank.lean` | bounded runs from blank tape, step by step |
| `lean/Macro.lean` | the macro step on block lists, its soundness, and halting iff the macro run halts |
| `lean/MacroRun.lean` | bounded runs from blank tape by the macro step |
| `py/macro.py` | the same macro map in Python (`python3 py/macro.py 50` prints the run) |
| `lean/Wave.lean` | the super step proved from `next`, and halting iff N is a power of two |
| `lean/WaveTime.lean` | the super step's exact step count, and the timed super orbit `orbitT` |
| `lean/orbit_gen.py` → `lean/Orbit/`, `OrbitKernel.lean`, `OrbitNative.lean` | the orbit checked in chunks between checkpoints from `c/orbitck.c` (generated; do not edit) |
| `lean/check_orbit.sh` | checks those files in parallel (`kernel` or `all`) |
| `lean/Cascade.lean` | the last blocks run on their own (`superL_split`, `superT_split`), and the tables are sound (`build_rep`, `runs_of_drive`) |
| `lean/CascadeRun.lean` | no halt in the first 4.4·10³⁷ steps, by 35 levels of tables (`native_decide`) |
| `lean/Cycles.lean` | every level cycles or goes silent, and silent means no halt (`cycles_or_never_halts`); the last six blocks' cycles |
| `lean/Axioms.lean` | prints what each theorem rests on |
| `py/waves.py` | the wave model: the run in another cut, and the super step with N, exact step counts |
| `py/n_search.py` | the search for an invariant that keeps N off the powers of two |
| `py/sibling.py` | checks that `1RB1RA_1RC1LB_1LD0RA_1RA0LE_---0LF_0RD0LB`, merged by bbchallenge into an equivalence class, runs as this machine does |
| `c/blkrun.c` | the wave model in C, for runs far beyond direct simulation |
| `c/orbitck.c` | the super orbit with `superT`, for the checkpoints of `lean/Orbit/` (not trusted: Lean recomputes them) |
| `c/superrun.c`, `py/superrun.py` | the super orbit with the cycles of the last blocks tabulated and skipped (C, and the same in Python) |
| `py/cycles.py` | the cycles of the last 1 to k blocks: least period, where it starts, what they send left, machine steps per period (the table in the reduction page, §6) |
| `tests/test_machine.py` | the generated files are current, early facts of the run |
| `tests/test_waves.py` | the block model against `tmrun`, the reference simulator and `runs/` |
| `tests/test_superrun.py` | `superrun` against `waves.py`, `blkrun.c`, its direct mode and `py/superrun.py`; `py/cycles.py` against its tables |
| `tests/test_explainer.py` | the engine of `pages/1RB1RA_1RC1LB/explainer.html` against `py/macro.py`, `py/waves.py` and the reference simulator (needs Node) |
| `runs/` | outputs of long runs |
| `notes/PRIOR_WORK.md` | what the community and the literature knew about this machine (30 October 2026), with sources |

## Checking

```sh
bash scripts/setup-lean.sh && . /etc/profile.d/lean.sh
bb6-1RB1RA_1RC1LB/lean/check.sh                 # about 6 min (CascadeRun about 4)
bb6-1RB1RA_1RC1LB/lean/check_orbit.sh all       # the plain orbit in chunks, in parallel: about 9 CPU hours
python3 bb6-1RB1RA_1RC1LB/tests/test_machine.py
python3 bb6-1RB1RA_1RC1LB/tests/test_waves.py     # about 20 s
python3 bb6-1RB1RA_1RC1LB/tests/test_superrun.py  # about 20 s
python3 bb6-1RB1RA_1RC1LB/tests/test_explainer.py # the explainer page's engine (Node), a few seconds
```
