# 1RB0LC_1LA0RD_1RA0LA_1RE1RD_1RA1RF_1LC---

bbchallenge id 44149. One of the six-state holdouts whose halting from blank tape is open.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LC |
| B | 1LA | 0RD |
| C | 1RA | 0LA |
| D | 1RE | 1RD |
| E | 1RA | 1RF |
| F | 1LC | --- |

**Family:** Nested ternary counter with an exact regime law (segments drained by 3^j per event).

A nested ternary counter: the tape is a list of segments of 111-blocks; an exact three-step law (verified on every event to 10^9 steps and on macro snapshots to 2.8x10^17) drains the oldest segment by 9 per generation until it runs out at P_14 (about 2.5x10^18 steps); what happens after that is not proved.

## Equivalence

`1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---` (b1, id 104106) and `1RB0LC_1LA0RD_1RA0LA_1RE1RD_1RA1RF_1LC---` (b2, id 44149) are the same machine: relabelling A->C, B->A, C->B turns b1's table
into b2's, so b2 from blank is b1 started in state B. Their tapes at the right records are identical to 1e8 steps
(the start-up differs), and the law below holds for both with one constant changed: c0 = 161 for b1, 38 for b2.
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
                                             c_n = c0 - 2n     (c0 = 38 for this machine)
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
y_13(0) = 9, y_14(0) = 0, and Q_14 would need 0 - 3. **The regime ends at P_14, near 2.5e18 steps.**

## Halting condition

Not known. Halting needs the head in state D on a 0 with `1 1` to its right (D0 -> 1RE, E1 -> 1RF, F1 halts), which the law never produces; whether a collapse can produce it needs a rule for the collapses, which is not known yet.

## Beyond P_14 (heuristic)

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
python3 py/bmap.py b2 direct 1e9       # the law against every D/F right record of the direct run (c/evrun.c)
python3 py/bmap.py b2 saved data/b2_msim.txt   # against every snapshot of the saved macro run (to 2.8e17)
python3 py/bmap.py b2 macro 1e15       # a fresh macro run (c/msim.c), reaches P_10
python3 py/check_msim.py 2e9              # the macro simulator against tools/c/tmrun.c
python3 py/bcollapse.py b2 4 1e14      # the collapse at P_14 on a reduced configuration
```

`data/b1_msim.txt` and `data/b2_msim.txt` are `c/msim.c MACHINE 4 1e18 - 1`, stopped by hand at 2.8e17 steps.

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
| trusted | **No halt in the first 10^9 steps.** The C simulator `tools/c/triage.c` runs 10^9 steps without a halt; at the end 293,599 cells have been visited and 133,391 of them hold a 1. | `holdouts/triage.json` |
| heuristic | **Growth shape: exp/sqrt.** Left of the start, the visited part of the tape grows like the square root of the step count, the signature of a head sweeping back and forth across the whole tape and adding a cell or a few at the end of each sweep (a bouncer-like shape) (fitted exponent 0.514). Right of the start it grows like the logarithm of the step count: each new cell costs a roughly constant factor more time, the signature of a counter or of a Collatz-like map whose values are written on the tape (fitted exponent 0.042). | `tools/py/bbtools/triage.py` |
| kernel | **16 shift rules.** For every n, the head crosses n copies of a short word in a fixed number of steps per copy and leaves another word behind (for example A going left over `0111` leaves `0100`, 8 steps a copy; these are the moves that cross the 111-blocks of the counter). Generated and proved by `bbtools.symtm`, checked by Lean's kernel. | `lean/Rules.lean`, generated by `holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/rules.py` |
| trusted | **The regime law, every event to 10^9 steps.** From step 103,844 on, every new cell written on the right in state D or F (16 events up to 10^9 steps) has exactly the list of segment lengths that the law P_n, Q_n, R_n predicts, with g_n = 2*3^n+5-28, y_n(j) = 3^j+2(17-n+j)-27, c_n = 38-2n. | `python3 holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/bmap.py b2 direct 1e9` |
| trusted | **No halt in the first 2.79x10^17 steps.** A macro simulator (blocks of 4 cells, crossing long runs of equal blocks in one go; it agrees with the direct simulator at 2x10^9 steps) runs to P_13 at step 279,473,455,907,774,113 without a halt, and every snapshot on the way lies on the law. | `holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/c/msim.c`; `py/bmap.py b2 saved data/b2_msim.txt`; `py/check_msim.py` |
| heuristic | **The collapse at P_14 and after.** The law needs every count to stay non-negative; the oldest segment y_n(0) = 9(17-n)-27 loses 9 per generation and reaches 0 at P_14 (about 2.5x10^18 steps). The law only looks at a segment's distance from the right end, so the right end of P_13 can be simulated from a shortened tape: with 3, 4 or 5 kept segments the run passes P_14 and the collapse without halting, and the right end settles into a second regime (the end counter jumps from 12 to about 81). There the oldest segment (321 blocks) loses about 9 per cycle, so the next collapse is some 36 generations later, near 10^46 steps; the end counter (-2 per cycle) runs out at about the same time, so the outcome of that second collapse is unclear. | `python3 holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/bcollapse.py b2 4` |
| open | **Does it halt from blank tape?** Not known. Halting needs the head in state D on a 0 with `1 1` to its right (D0 -> 1RE, E1 -> 1RF, F1 halts), which the law never produces; whether a collapse can produce it needs a rule for the collapses, which is not known yet. |  |

## Lean

`lean/Rules.lean` is generated by `holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/rules.py` (one script for all eight machines of this worker;
`--check` compares the files instead of writing them) and is listed in `lean/check.sh` after `Blank.lean`:

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LC_1LA0RD_1RA0LA_1RE1RD_1RA1RF_1LC---/lean/check.sh
python3 holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/rules.py --check
```

## Pages

- [`pages/holdouts/1RB0LC_1LA0RD_1RA0LA_1RE1RD_1RA1RF_1LC---/explainer.html`](../../pages/holdouts/1RB0LC_1LA0RD_1RA0LA_1RE1RD_1RA1RF_1LC---/explainer.html)
- [`pages/holdouts/1RB0LC_1LA0RD_1RA0LA_1RE1RD_1RA1RF_1LC---/proof-status.html`](../../pages/holdouts/1RB0LC_1LA0RD_1RA0LA_1RE1RD_1RA1RF_1LC---/proof-status.html)
