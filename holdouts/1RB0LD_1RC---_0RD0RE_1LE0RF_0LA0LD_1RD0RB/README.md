# 1RB0LD_1RC---_0RD0RE_1LE0RF_0LA0LD_1RD0RB

bbchallenge id 122390. One of the six-state holdouts whose halting from blank tape is open (group G13). Family: **counter epochs at the right end leaving a stack of records**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LD |
| B | 1RC | --- |
| C | 0RD | 0RE |
| D | 1LE | 0RF |
| E | 0LA | 0LD |
| F | 1RD | 0RB |

## What it does

Write a for the pair 1 0. Each time the head is at the right end in state D, the end of the tape reads like &hellip; 1^6903 0 a^13 1 0^2 1^5 0 a^2 1 0^2 1^4699 0 a^6110 1 D>1 (step 266,560,790): a working part 1^u 0 a^v 1 in which u falls and v rises by the same amount (u = 4,699, 3,199, 1,699, 199 and v = 6,110, 7,610, 9,110, 10,610 at four samples 1,500 apart), and to its left records 1^s 0 a^k 1 0^2 left by earlier epochs.

When u runs out the working part is rebuilt from the record below it, so the records act as a stack that is popped and pushed. The far left of the tape is frozen (1^8 0 a^5 1 0^2 1^25 0 a 1 0^2 &hellip;). The tape grows to the right like t0.66.

### Halting

The machine halts when it reads a 1 in state B (B1 is the halting transition). B is entered from A on a 0 (A0 = 1RB) and from F on a 1 (F1 = 0RB), so a halt needs A>0 1 or F>1 1.

## Phase 2 results

`lean/Rules.lean` proves the two counter cycles for every length (`cycA`, `cycB`, see the theorem docs).
`py/coverage.py 1000000000`: 0.9955 of the steps lie inside jumps of these shapes (cycA: 35 jumps / 24,712 cycles;
cycB: 72 / 38,028). The record-stack map that runs between counters is not found yet.

## Status

Open. Lean (`lean/Blank.lean`): the halting configurations, no halt in 10^4 steps (kernel) and 10^7 (`native_decide`). C: no halt in 10^9 steps. Lean (`lean/Rules.lean`, kernel): the two working-counter cycles `cycA` and `cycB`, for every length and any tape on the left. Trusted: they cover 99.55% of the first 10^9 steps (`py/coverage.py`). The record-stack map between counters is observed, not proved.

## Later

1. Prove the conversion of 1^u into 10 pairs (a shift rule) with `bbtools.symtm`.
2. Find what an epoch does when u reaches 0: how the record below is read and what new record is written.
3. Express the run as a stack machine on records and look for its invariant.
4. The whole-tape frame-map method (fit affine cases on a fixed set of frames, as for 1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC) does not apply as it is: the number of records grows (50 `1001` record markers at 10^8 steps, 86 at 10^9). Frames would need a left context (a window of the top records) with records moving between window and context.

## Pages

- [`pages/holdouts/1RB0LD_1RC---_0RD0RE_1LE0RF_0LA0LD_1RD0RB/explainer.html`](../../pages/holdouts/1RB0LD_1RC---_0RD0RE_1LE0RF_0LA0LD_1RD0RB/explainer.html)
- [`pages/holdouts/1RB0LD_1RC---_0RD0RE_1LE0RF_0LA0LD_1RD0RB/proof-status.html`](../../pages/holdouts/1RB0LD_1RC---_0RD0RE_1LE0RF_0LA0LD_1RD0RB/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LD_1RC---_0RD0RE_1LE0RF_0LA0LD_1RD0RB/lean/check.sh
python3 holdouts/1RB0LD_1RC---_0RD0RE_1LE0RF_0LA0LD_1RD0RB/py/coverage.py 1000000000
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB---_0RC0RD_1LD0RF_0LE0LC_1RA0LC_1RC0RA`](../1RB---_0RC0RD_1LD0RF_0LE0LC_1RA0LC_1RC0RA/README.md): rename A→E, B→A, C→B, D→C, E→D, F→F; it is this table started in state B
- [`1RB0RE_1LC0RA_0LD0LB_1RE0LB_1RF---_0RB0RC`](../1RB0RE_1LC0RA_0LD0LB_1RE0LB_1RF---_0RB0RC/README.md): rename A→D, B→E, C→F, D→B, E→C, F→A; it is this table started in state F

<!-- end of related machines -->
