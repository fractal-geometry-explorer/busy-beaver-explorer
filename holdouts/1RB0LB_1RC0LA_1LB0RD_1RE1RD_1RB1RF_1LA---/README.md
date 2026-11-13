# 1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---

bbchallenge id 104106. One of the six-state holdouts whose halting from blank tape is open.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LB |
| B | 1RC | 0LA |
| C | 1LB | 0RD |
| D | 1RE | 1RD |
| E | 1RB | 1RF |
| F | 1LA | --- |

**Family:** Nested ternary counter with an exact regime law (segments drained by 3^j per event).

A nested ternary counter: the tape is a list of segments of 111-blocks; an exact three-step law drains the oldest segment by 9 per generation until it runs out at P_14 (step 2.5x10^18). An exact run confirms the law up to there, passes that collapse without a halt and continues to 2.29x10^20 steps; the next collapse is forecast near 10^46 steps and is not understood.

## Equivalence

`1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---` (b1, id 104106) and `1RB0LC_1LA0RD_1RA0LA_1RE1RD_1RA1RF_1LC---` (b2, id 44149) have the same table, started in different states: relabelling A->C, B->A, C->B turns b1's table
into b2's, so b2 from blank is b1 started in state B. That is another run of the same table, not the same run: the two share no configuration in 10^7 steps (see Related
machines). At the right records the right ends of their tapes agree (the rest of the tape differs), and the law below holds for both with one constant changed: c0 = 161 for b1, 38 for b2.
This analysis (and its scripts, in `holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/`) covers both.

## What it does

At each step where the head writes a new cell on the right in state D or F, the tape, written as lengths of runs of
1s (the single 0s between runs left out), is

    2 3^16 5 3 5  3^a1 5 3^a2 5 ... 5 3^am  TAIL

blocks `111` separated by single 0s, cut into segments by markers `11111`. The list L = [a1, ..., am] is the state.
Between two such events the head sweeps the whole tape (16 shift rules in `lean/Rules.lean`), so the far (left)
side grows like the square root of the time and the right side very slowly.

## The map

The events come in a cycle of three, P_n, Q_n, R_n (n = -1, 0, 1, ...). With k = n + 1:

    P_n = [g_n, y_n(n), ..., y_n(0), c_n]    g_n = 2*3^(n+5) - 28
                                             y_n(j) = 3^(j+2) * (17 - n + j) - 27
                                             c_n = c0 - 2n     (c0 = 161 for this machine)
    Q_n = [g, g - 3^(k+1) + 1, y_1 - 3^k, ..., y_k - 3, c]           from P_n = [g, y_1..y_k, c]
    R_n = [a + 2*3^(k+4), b - 3^(k+1), z_1 - 3^k, ..., z_k - 3, c - 1]  from Q_n = [a, b, z_1..z_k, c]
    P_(n+1) = the same step again, from R_n

So the segment with i segments on its right loses 3^(k+1-i) blocks per event, the first segment keeps growing, and
each generation adds a segment. A generation costs about 9 times the previous one: P_n is reached at step

| n | b1 step | n | b1 step |
|---|---|---|---|
| -1 | 223,281 | 7 | 526,388,511,969 |
| 0 | 505,965 | 8 | 4,734,432,301,285 |
| 1 | 1,881,665 | 9 | 42,600,703,431,937 |
| 2 | 11,227,329 | 10 | 383,378,775,170,313 |
| 3 | 86,702,753 | 11 | 3,450,326,315,986,929 |
| 4 | 740,547,553 | 12 | 31,052,688,869,335,161 |
| 5 | 6,549,323,129 | 13 | 279,473,455,907,952,089 |
| 6 | 58,601,296,349 | | (b2: P_13 at 279,473,455,907,774,113) |

The law holds while every count stays >= 0. The oldest segment y_n(0) = 9(17 - n) - 27 loses 9 per generation:
y_13(0) = 9, y_14(0) = 0, and Q_14 would need 0 - 3. **The regime ends at P_14.**

**The exact run through the collapse (13 November).** `c/msim.c` ran 55 minutes from blank tape, to step
229,416,990,524,183,704,810, without a halt (`data/b1_far.txt`). The events after P_13:

| event | step | end of the list |
|---|---|---|
| Q_13 | 627,262,429,067,109,861 | on the law |
| R_13 | 1,372,524,234,994,915,593 | on the law |
| P_14 | 2,515,258,871,431,441,221 | on the law: ..., 1431, 378, 81, 0, 133 |
| first new cell on the right after the collapse | 16,989,897,072,297,977,885 | ..., 1341, 348, 204 (second regime) |

(`py/bmap.py b1 saved data/b1_far.txt` checks every event before P_14 and then stops at P_14, because its parser
does not read a segment of length 0; P_14 was compared with the law separately. For b2 only the events that write a
new cell on the right are in the file, two per generation.)

So the law held to its last event, the collapse did not halt, and the second regime starts with the end counter
at 204, which is what the shortened runs below had forecast.

## Halting condition

Not known. Halting needs the head in state D on a 0 with `1 1` to its right (D0 → 1RE, E1 → 1RF, F1 halts), which the law never produces. The first collapse did not produce it either (exact run). Whether a later collapse can needs a rule for the collapses, which is not known yet.

## Beyond P_14 (forecast from shortened tapes; its first part is now confirmed)

The law is right-anchored (a segment's loss depends only on how many segments lie to its right), so the right end of
the real P_13 is also the right end of a short configuration: the m oldest segments y_13(m-1..0), the end counter
c_13, and the generator g = 2*3^(m+4) - 28 that belongs with m segments. `py/bcollapse.py` builds it and runs the
macro simulator. For m = 3, 4, 5 the run passes P_14 and the collapse without a halt; the right end (independent of
m) settles into a second regime of the same kind, e.g. for b1 and m = 4 `[78704 | 37881, 20628, 38529, 12096, 1341,
348 | 204]`, the end counter jumping 133 -> 204 (b2: 12 -> about 81). In that regime the oldest element (321) drops
about 9 per cycle, so the next collapse is about 36 generations later, near 1e46 steps; for b2 the end counter (-2
per cycle) runs out at about the same time, so which happens first is not clear.

## Reproduce

All scripts are in `holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/`:

```sh
python3 py/bmap.py b1 direct 1e9       # the law against every D/F right record of the direct run (c/evrun.c)
python3 py/bmap.py b1 saved data/b1_msim.txt   # against every snapshot of the saved macro run (to 2.8e17)
python3 py/bmap.py b1 macro 1e15       # a fresh macro run (c/msim.c), reaches P_10
python3 py/check_msim.py 2e9              # the macro simulator against tools/c/tmrun.c
python3 py/bcollapse.py b1 4 1e14      # the collapse at P_14 on a reduced configuration
```

`data/b1_msim.txt` and `data/b2_msim.txt` are `c/msim.c MACHINE 4 1e18 - 1`, stopped by hand at 2.8e17 steps;
`data/b1_far.txt` and `data/b2_far.txt` are `c/msim.c MACHINE 4 1e36 - 1 r 3300` (55 minutes, to 2.3e20 steps).

## Deep runs of the whole family (13 November)

`c/msim.c` is not specific to this machine. `py/deep.py run 240` ran it on the 45 machines of the family of block-list
countdown counters (the list is `data/deep.json`): for each one it tries blocks of 2 to 10 cells for 6 seconds, keeps
the size that gets furthest and runs it for 240 seconds from blank tape (this machine and its twin: 55 minutes).
**No machine halted.** `py/deep.py verify` compares the macro run with the direct simulator `tools/c/tmrun.c` after
2x10^9 steps for every machine at the block size used: state, head position and tape agree for all 45. These are
bounded runs and say nothing about later steps.

| machine | block | steps without a halt | seconds | ended |
|---|---|---|---|---|
| `1RB---_1LC0LC_1RD1LB_1LE1RD_0LA1LF_1LD0RF` | 6 | 2.48e+15 | 240 | ran out of room for runs |
| `1RB1LA_1RC1RE_1RD0RD_1LA1RC_1RF0LE_1RA---` | 6 | 7.72e+15 | 240 | ran out of room for runs |
| `1RB1LF_1LC1RB_1LE1LD_1LB0RD_1LF---_1LA0LA` | 6 | 6.60e+17 | 240 | still running |
| `1RB0RE_1LC0RD_1LD0LD_1RA0LC_1RA1RF_1RA---` | 6 | 8.95e+17 | 240 | still running |
| `1RB0RF_1LC0RA_0LD0LB_1RD1LE_0RC0RA_1RA---` | 4 | 9.31e+17 | 240 | still running |
| `1RB---_1RC0RA_1LD0RB_0LE0LC_1RE1LF_0RD0RB` | 4 | 1.24e+18 | 240 | still running |
| `1RB1LF_1LC1RB_1LF1LD_1LE0RD_1LB---_1LA0LA` | 6 | 2.17e+18 | 240 | still running |
| `1RB0LE_0RC0RA_1LC1RD_0LB0LE_1LA0LF_1LE---` | 6 | 2.46e+18 | 240 | still running |
| `1RB0LC_1RC0RC_1LD0RB_1LA0LE_1LD1LF_1LD---` | 4 | 2.49e+18 | 240 | still running |
| `1RB0RE_0RC1RE_1RD1LE_0LE---_1RA1LF_1RF0LC` | 4 | 5.11e+18 | 240 | still running |
| `1RB1LC_0LC---_1RE1LD_1RD0LA_1RF0RC_0RA1RC` | 6 | 5.93e+18 | 240 | still running |
| `1RB1RD_1RC1RB_1LD0RA_1RA0LE_1LF0LC_---1LE` | 6 | 6.65e+18 | 240 | still running |
| `1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD` | 4 | 7.06e+18 | 240 | still running |
| `1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RB---` | 4 | 7.11e+18 | 240 | still running |
| `1RB1LE_1LC1RE_1LE1LD_1LC0LA_1RF0LA_---0RA` | 6 | 7.19e+18 | 240 | still running |
| `1RB1LF_1RC0RA_0RD1RA_1RE1LA_0LA---_1RF0LD` | 6 | 7.45e+18 | 240 | still running |
| `1RB0LC_1LC0RE_1LD1LB_1LA1LD_1RF0RA_---1RE` | 6 | 7.59e+18 | 240 | still running |
| `1RB1RE_1LC0LD_1RA0LD_1LA1LB_0RC1RF_1RC---` | 8 | 1.11e+19 | 240 | still running |
| `1RB1RD_0LC0LB_0RE0LD_1LB0RB_1RF---_0RA0RC` | 6 | 1.24e+19 | 240 | still running |
| `1RB---_1RC1RF_1LD1RA_1LB0LE_1LF1LF_0RB0LD` | 6 | 1.29e+19 | 240 | still running |
| `1RB0LF_0RC0LC_1LA1LD_1RE1LC_---1RA_0LC0RD` | 7 | 1.54e+19 | 240 | still running |
| `1RB0RE_1LC1LF_1RA1LD_0LB---_1RF1LE_0LB0RA` | 6 | 1.68e+19 | 240 | still running |
| `1RB1RE_1LC0RF_1LA0LD_1LE1LC_0RA0LC_1RA---` | 6 | 1.73e+19 | 240 | still running |
| `1RB1LA_0LC0RE_1LD1LB_1RE1LF_1RC0RA_0RC---` | 6 | 1.77e+19 | 240 | still running |
| `1RB1RD_1LC0RF_0LA0RA_1LE1RA_---1LB_0RA0LD` | 7 | 1.97e+19 | 240 | still running |
| `1RB1LF_0RC1RC_1LD0RD_0LE0LA_1RA0LB_---1LD` | 6 | 2.00e+19 | 240 | still running |
| `1RB1LE_1RC1LF_0RD1RD_1LE0RE_0LA0LB_---1LE` | 6 | 2.00e+19 | 240 | still running |
| `1RB0LB_1LC1RE_1LA1LD_0RB1LF_1LA0RC_---1LC` | 6 | 2.04e+19 | 240 | still running |
| `1RB---_0RC0LA_1LD0RB_1LE0LF_1RC1LF_0LC0LB` | 8 | 2.11e+19 | 240 | still running |
| `1RB0RE_1LC0RE_1LA1LD_0LB1LF_1RC1RA_1LB---` | 8 | 2.12e+19 | 240 | still running |
| `1RB0LD_1RC1RE_1LA0LD_1LB1LC_0RA1RF_1RA---` | 8 | 2.12e+19 | 240 | still running |
| `1RB1RC_1LC1LE_1RD0RA_1LB0RA_0LD1LF_1LD---` | 4 | 2.59e+19 | 240 | still running |
| `1RB0RD_0LC0LF_1RD1LB_0RE---_1RA0LC_0LA1LF` | 6 | 2.72e+19 | 240 | still running |
| `1RB1LD_1LC0RE_1LA0LD_0LB0LE_0RB0LF_1RE---` | 8 | 2.78e+19 | 240 | still running |
| `1RB0RF_1LC1RF_1RA0LD_0LC0RE_1LD---_0RC0RD` | 8 | 3.06e+19 | 240 | still running |
| `1RB0LD_1RC0RF_0LD0LE_1RF1LC_0LB1LE_0RA---` | 6 | 3.84e+19 | 240 | still running |
| `1RB0LF_1LC0RC_1RA1LD_0RB0LE_1LC0LB_---1LA` | 6 | 4.49e+19 | 240 | still running |
| `1RB1LD_1RC1RE_1LA0RA_1RC0LB_0LA1RF_---1RB` | 6 | 4.97e+19 | 240 | still running |
| `1RB1LE_0RC---_1RD0LA_1RE0RB_0LA0LF_0LD1LF` | 6 | 5.10e+19 | 240 | still running |
| `1RB0LD_1LC1RE_1LA1RC_1RA0LC_0RF---_0LD1RB` | 9 | 5.31e+19 | 240 | still running |
| `1RB0LB_1RC1LD_1LD0RD_1LE0RC_1LF---_0LA1RF` | 10 | 5.32e+19 | 240 | still running |
| `1RB1LE_0LC1RE_---1LD_0RD1LA_0RF1RF_1RA0LB` | 10 | 6.00e+19 | 240 | still running |
| `1RB0LB_1RC0LA_1RD---_0RE1LD_1LF0RF_1LA1RB` | 10 | 8.13e+19 | 240 | still running |
| `1RB0LC_1LA0RD_1RA0LA_1RE1RD_1RA1RF_1LC---` | 4 | 2.28e+20 | 3300 | still running |
| `1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---` | 4 | 2.29e+20 | 3300 | still running |

## Further work

A rule for the collapses: what the right end looks like after a segment runs out, as a function of the counts. With
that, the run could be followed from regime to regime by computation (the second collapse near 1e46 steps); a
proof of the regime law for all n (one generation as a Lean theorem from the shift rules) would lift the trusted
part to the kernel level.

## What is proved, and how firmly

| level | claim | where |
|---|---|---|
| kernel | **The halting configurations.** The machine stops exactly when it reads the symbol of a halting transition (F1); the generated statement covers every configuration. | `step_none_iff`, `lean/Blank.lean` |
| kernel | **No halt in the first 10,000 steps.** The list simulator of the shared library, proved to agree with the machine's semantics, runs 10,000 steps from blank tape without a halt, evaluated by Lean's kernel. | `blank_runs_kernel`, `lean/Blank.lean` |
| native | **No halt in the first 10^7 steps.** The same run, evaluated by compiled code. | `blank_runs_native`, `lean/Blank.lean` |
| trusted | **No halt in the first 10^9 steps.** The C simulator `tools/c/triage.c` runs 10^9 steps without a halt; at the end 294,091 cells have been visited and 168,784 of them hold a 1. | `holdouts/triage.json` |
| heuristic | **Growth shape: exp/sqrt.** Left of the start, the visited part of the tape grows like the square root of the step count, the signature of a head sweeping back and forth across the whole tape and adding a cell or a few at the end of each sweep (a bouncer-like shape) (fitted exponent 0.512). Right of the start it grows like the logarithm of the step count: each new cell costs a roughly constant factor more time, the signature of a counter or of a Collatz-like map whose values are written on the tape (fitted exponent 0.028). | `tools/py/bbtools/triage.py` |
| kernel | **16 shift rules.** For every n, the head crosses n copies of a short word in a fixed number of steps per copy and leaves another word behind (for example A going left over `0111` leaves `0100`, 8 steps a copy; these are the moves that cross the 111-blocks of the counter). Generated and proved by `bbtools.symtm`, checked by Lean's kernel. | `lean/Rules.lean`, generated by `holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/rules.py` |
| trusted | **The regime law, every event to 10^9 steps.** From step 223,270 on, every new cell written on the right in state D or F (16 events up to 10^9 steps) has exactly the list of segment lengths that the law P_n, Q_n, R_n predicts, with g_n = 2*3^n+5-28, y_n(j) = 3^j+2(17-n+j)-27, c_n = 161-2n. | `python3 holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/bmap.py b1 direct 1e9` |
| trusted | **No halt in the first 2.29x10^20 steps, through the first collapse.** The macro simulator (blocks of 4 cells, crossing long runs of equal blocks in one go; exact, and it agrees with the direct simulator at 2x10^9 steps) ran 55 minutes from blank tape to step 229,416,990,524,183,704,810 without a halt. Every right-end event up to P_14 lies on the law, and P_14, at step 2,515,258,871,431,441,221, is exactly the predicted list: the oldest segment is down to 0 and the end counter is 133. The run then leaves the law, as predicted, passes the collapse without halting, and the next new cell on the right comes at step 16,989,897,072,297,977,885 with the end counter at 204; 3 such events are recorded after the collapse. | `holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/c/msim.c MACHINE 4 1e36 - 1 r 3300`; output in `holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/data/b1_far.txt`; `py/check_msim.py` |
| heuristic | **After the collapse: the next one (forecast).** The law only looks at a segment's distance from the right end, so the right end of P_13 was simulated beforehand from a shortened tape with 3, 4 or 5 kept segments. That forecast said the run would pass the collapse at P_14 without halting and that the end counter would jump from 133 to 204; the full exact run has now done exactly that (previous claim). The same shortened runs say that in the second regime the oldest segment (321 blocks) loses about 9 per cycle, so the next collapse would be some 36 generations later, near 10^46 steps. The second regime has no law yet, and nothing is known about that second collapse. | `python3 holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/bcollapse.py b1 4` |
| open | **Does it halt from blank tape?.** Not known. Halting needs the head in state D on a 0 with `1 1` to its right (D0 → 1RE, E1 → 1RF, F1 halts), which the law never produces. The first collapse did not produce it either (exact run). Whether a later collapse can needs a rule for the collapses, which is not known yet. |  |

## Lean

`lean/Rules.lean` is generated by `holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/rules.py` (one script for all eight machines of this worker;
`--check` compares the files instead of writing them) and is listed in `lean/check.sh` after `Blank.lean`:

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/lean/check.sh
python3 holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/rules.py --check
```

## Pages

- [`pages/holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/explainer.html`](../../pages/holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/explainer.html)
- [`pages/holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/proof-status.html`](../../pages/holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/proof-status.html)

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0LC_1LA0RD_1RA0LA_1RE1RD_1RA1RF_1LC---`](../1RB0LC_1LA0RD_1RA0LA_1RE1RD_1RA1RF_1LC---/README.md): rename A→C, B→A, C→B, D→D, E→E, F→F; it is this table started in state B

<!-- end of related machines -->
