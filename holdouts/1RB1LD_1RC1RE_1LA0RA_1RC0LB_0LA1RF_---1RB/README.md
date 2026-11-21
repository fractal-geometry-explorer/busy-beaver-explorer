# 1RB1LD_1RC1RE_1LA0RA_1RC0LB_0LA1RF_---1RB

bbchallenge id 12692. One of the six-state holdouts whose halting from blank tape is open. Its registers of 011101 units form a cascade whose rules have not been decoded.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LD |
| B | 1RC | 1RE |
| C | 1LA | 0RA |
| D | 1RC | 0LB |
| E | 0LA | 1RF |
| F | --- | 1RB |

## What it does

Read left to right, the tape is a list of registers: runs of the word `011101` separated by short separators
(`11`, `01`, `1101`, ...). At the left end, at a few moments (r1, r2, ... the lengths of the runs, separators left
out):

```
step 12,547,595:   670   87  144   21
step 14,175,202:   136  652   75  140   21
step 53,840,380:    11 1019  509  430   19  127   17
step 99,822,398:  1370  680  425  409   12  124   15
```

Between the samples the first register grows while the second shrinks, about four units gained for each unit lost;
when the second runs low the list shifts (step 14,175,202: the old first register, 670 at the sample before, is now second at 652,
a new first register starts small, and the others shift along). The number of registers grows slowly, the first two registers
hold most of the tape, and the visited width grows like the square root of the step count (the left side; the right
side grows like a logarithm). The units are crossed by shift rules (for example A moving right turns `011101` into
`111110`, D moving left turns it into `111011`).

The machine halts only in F reading 0: E reads a 1, keeps it, and moves right onto a 0.

## Does it halt?

Unknown. The registers look like a cascade of counters, each feeding the one to its left, but the transfer rule
and what happens at a shift have not been extracted. Direct simulation: no halt in 10^11 steps. **Open.**

## For later

Stopped at: the shape (above) only. Next steps:

1. Write a tokenizer for the register list (runs of `011101` and its rotations, with the separators kept as
   symbols) and record it at every left-end turn; find the rule for one transfer (r1 grows, r2 shrinks) as a
   symbolic run with contexts, and the rule for the shift.
2. Turn those rules into a map on register lists, check it against direct simulation, and iterate it far.
3. Prove the rules with `bbtools.symtm` and chain them in Lean.

## Status

Open. Lean (`lean/Blank.lean`): the halting configurations (`step_none_iff`), no halt in 10,000 steps by the
kernel, in 10,000,000 by `native_decide`. C (`tools/c/tmrun.c`): no halt in 10^11 steps.

## Deep exact run

No halt in the first 4.96x10^19 steps: the macro simulator `holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/c/msim.c` with blocks of 6 cells ran
from blank tape to step 49,671,575,971,845,881,180. It is exact, and at this block size it agrees with the
direct simulator after 2,000,037,093 steps (`python3 holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/deep.py run 240`, then `verify`).

## Countdown hunt: through two top-level resets to 4.06·10^9138 steps (21 November 2026)

**No halt in the first 4.05609256814·10^9138 steps** (trusted computation; the bound of 20 November was
3.86·10^5137). `py/ratrack.py run` runs the region-memo accelerator `tools/py/bbtools/regaccel.py` (blocks of 6,
exact, step counts included), checkpoints it, and logs the block list each time the head is at the right end
(runs of `111110` between separators of 7 ones, the end of 8 ones). `py/ratrack.py test` checks the decoded
snapshots against a direct run: 11 of 11 up to 2·10^9 steps agree. The list has the same shape as for
1RB1LD_1RC1RE_1LA0RA_1RC0LB_0LA1RF_---1RD: the last block is the far-end countdown, worn down by one per arrival.

| steps | event |
|---|---|
| ~10^500 | the last block (19,879 at 10^500) runs out; 129,755 becomes the last block; end `8 0`; no halt |
| 10^500 to 10^5138 | it loses about 15.7 per decade (761 at 10^5091) |
| 3.8589218·10^5137 | **the last block runs out, no halt**; the 10^9 block in front of it becomes the last block. At the same time middle blocks of the list run out and the front is rebuilt from small timers, so the step count stays at 3.8589218·10^5137 for about 20 minutes of the run (this is where the 20-minute run of 18 November stopped: the same step count, 3.85892·10^5137) |
| 10^5138 to 10^9138 | the front regrows past the old blocks and the run speeds up again |

At the checkpoint the end of the list is `... [8] 10^35, 1,900,754,236 (last block), end 8 0`; the logged run went on
to about 5·10^11138 steps before it was stopped (the bound is the checkpoint, which is exact and can be resumed).
**Next deciding event:** that last block, losing about 16 per decade, runs out near 10^(1.2·10^8) steps (a
forecast from the rate, not a run).

```sh
python3 holdouts/1RB1LD_1RC1RE_1LA0RA_1RC0LB_0LA1RF_---1RB/py/ratrack.py test 1RB1LD_1RC1RE_1LA0RA_1RC0LB_0LA1RF_---1RB 6 2e9
python3 holdouts/1RB1LD_1RC1RE_1LA0RA_1RC0LB_0LA1RF_---1RB/py/ratrack.py run 1RB1LD_1RC1RE_1LA0RA_1RC0LB_0LA1RF_---1RB 6 3600 ckpt=/tmp/m3.pkl every=100 hb=60
```

## Pages

- [`pages/holdouts/1RB1LD_1RC1RE_1LA0RA_1RC0LB_0LA1RF_---1RB/explainer.html`](../../pages/holdouts/1RB1LD_1RC1RE_1LA0RA_1RC0LB_0LA1RF_---1RB/explainer.html)
- [`pages/holdouts/1RB1LD_1RC1RE_1LA0RA_1RC0LB_0LA1RF_---1RB/proof-status.html`](../../pages/holdouts/1RB1LD_1RC1RE_1LA0RA_1RC0LB_0LA1RF_---1RB/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LD_1RC1RE_1LA0RA_1RC0LB_0LA1RF_---1RB/lean/check.sh
gcc -O2 -o /tmp/tmrun tools/c/tmrun.c && /tmp/tmrun 1RB1LD_1RC1RE_1LA0RA_1RC0LB_0LA1RF_---1RB 100000000000     # running 100000000000 501961
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0LB_1LC1RE_1LA1LD_0RB1LF_1LA0RC_---1LC`](../1RB0LB_1LC1RE_1LA1LD_0RB1LF_1LA0RC_---1LC/README.md): rename A→B, B→C, C→A, D→E, E→D, F→F and exchange left and right; it is this table started in state C, in a mirror

<!-- end of related machines -->
