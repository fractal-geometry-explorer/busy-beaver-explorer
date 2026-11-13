# 1RB0LC_0RC0RF_1RD0LE_1LA1RA_1LC1RB_0RB---

bbchallenge id 104920. Group G01. **A list of frozen blocks with one growing block**, analysis only begun. Open.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LC |
| B | 0RC | 0RF |
| C | 1RD | 0LE |
| D | 1LA | 1RA |
| E | 1LC | 1RB |
| F | 0RB | --- |

## What it does

Sample the run when the head is in state E at the left end of the tape. Since step 9.1·10⁶ the tape has been

    E> (10)^2 (0100)^189 (10)^3 (0010)^633 (01)^2 (0001)^n  tail

with a short tail (`0^5 1^2`, `(001)^2 1`, `0^2 1^2`, empty, …). Only n changes:

    n = 13, 159, 363, 649, 1050, 1612, 2398, 3499, 5039, 7197, 10215, 14443, 20361, 28645, 40230   (step 1.93·10¹⁰)

which is a factor of 1.44 falling to 1.40 per event. The frozen blocks are what is left of earlier levels: the block
of `0100` grew 2, 4, 7, 11, …, 135, 189 and froze at step 432,110; the block of `0010` grew 27, 66, …, 452, 633
and froze at step 9.1·10⁶. At the last event the tail is `0^2 (10)^2 (0010)^7 0^2 1^2`, which may be the start of
the next level.

During one E-to-E pass the head sweeps the whole tape, and blocks are moved 14 copies at a time. For example,
sampled at the right end, the middle block (written `(1110)^j` during the sweep) loses 14 copies per B-event while
the block to its left gains 14.

The ratio is not constant and the tail changes from event to event, so the event map has more structure than a
single number. Neither the map nor the halting condition is known yet.

## What is proved

| level | result | where |
|---|---|---|
| kernel | the halting configurations (F1); no halt in 10⁴ steps | `lean/Blank.lean` (generated) |
| native | no halt in 10⁷ steps | `lean/Blank.lean` |
| trusted | the shape of the E-events up to 1.93·10¹⁰ steps | `py/events.py 2e10` |

## Reproduce

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LC_0RC0RF_1RD0LE_1LA1RA_1LC1RB_0RB---/lean/check.sh
python3 holdouts/1RB0LC_0RC0RF_1RD0LE_1LA1RA_1LC1RB_0RB---/py/events.py 2e10      # about 3 min
```

## Further work

More than a day. The next steps:

- Find a finer sampling (the right-end B-events look regular) and the exact rule for one sweep, with the tail.
- Understand when a level freezes and a new word starts (0100, then 0010, then 0001, and now perhaps a fourth level),
  and how halting (F1 read) could happen.

## Third pass

The macro simulator `c/msim.c` (a copy of the one in holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---, in
`../1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA/c/`; blocks of 4 cells; checked against the direct simulator at 10⁹ steps by `check_msim.py check`) runs
10¹⁸ steps from blank tape without a halt: `python3 ../1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA/py/check_msim.py run 1RB0LC_0RC0RF_1RD0LE_1LA1RA_1LC1RB_0RB--- 1e18` (2 to 5 minutes).
The frozen prefix is still there at 10¹⁵ steps (`… (0100)^633-type block, then a block of 40,231 copies`): the block
that was growing in the first analysis (n = 40,230 at 1.9·10¹⁰ steps) froze at 40,231 and a new level grows behind
it, as the tail `(10)^2 (0010)^7` suggested. So the levels so far froze at 189, 633 and 40,231 copies. The community
tracker describes the machine as "a recursive counter: the last block grows 7/5 per sweep; a halt needs a small
cluster of blocks fed a wrong carry" (rules simulated there to 2·10³² steps); 7/5 is the 1.40 measured here.

No pushdown certificate with a small DFA exists: the reduction of `bb6-1RB0LF_1RC0LB/c/pds.c` (one side of the tape
exact, the other a DFA, post* saturation) reaches a halt for every DFA with at most 6 states, on either side
(`TM=1RB0LC_0RC0RF_1RD0LE_1LA1RA_1LC1RB_0RB--- ./pds 6 L`, then `R`; 1.5 minutes each).

## Pages

- [`pages/holdouts/1RB0LC_0RC0RF_1RD0LE_1LA1RA_1LC1RB_0RB---/explainer.html`](../../pages/holdouts/1RB0LC_0RC0RF_1RD0LE_1LA1RA_1LC1RB_0RB---/explainer.html)
- [`pages/holdouts/1RB0LC_0RC0RF_1RD0LE_1LA1RA_1LC1RB_0RB---/proof-status.html`](../../pages/holdouts/1RB0LC_0RC0RF_1RD0LE_1LA1RA_1LC1RB_0RB---/proof-status.html)

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB1LB_1LC0RE_0LE0LD_0LC---_1LA0RF_1RE1LC`](../1RB1LB_1LC0RE_0LE0LD_0LC---_1LA0RF_1RE1LC/README.md): rename A→B, B→C, C→E, D→A, E→F, F→D and exchange left and right; it is this table started in state D, in a mirror

<!-- end of related machines -->
