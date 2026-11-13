# 1RB1LA_1LA1RC_1RD0RB_1LE1LD_---1LF_1RA0LF

bbchallenge id 104840. One of the six-state holdouts whose halting from blank tape is open. It is a slow counter that grows a block at the right end by 10 cells per fourfold time, in epochs.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LA |
| B | 1LA | 1RC |
| C | 1RD | 0RB |
| D | 1LE | 1LD |
| E | --- | 1LF |
| F | 1RA | 0LF |

## Status

Open. Lean (`lean/Blank.lean`): the halting configurations (`step_none_iff`), no halt in 10,000 steps by the kernel, in 10,000,000 by `native_decide`. C (`tools/c/tmrun.c`): no halt in 10,000,000,000 steps.

## What it does

- **Right-end block.** At right-end records the tape ends `110 1^k 110 1 1 D>0`; k grows by 10 per burst, bursts about
  4 times further apart each time (k = 71, 81, ..., 131 at steps 403,611,844, 407,740,602, 424,255,680,
  490,315,950, 754,557,084, 1,811,521,682, 6,039,380,104). The word left of it (`10`, `110`, `1^j`) changes slowly.
- **Epochs.** The first series ended with `1^119` (step 378,784,004); around step 4.02*10^8 the tape grew by ~100 cells
  and a new series started. Width 153 / 292 / 312 cells at 10^8 / 10^9 / 10^10 steps.
- **Halting.** Only E0 halts; E is entered only from D0 (`1LE`), 4,761,903 times in 10^8 steps, always onto a 1.

## Later

- Identify the counter digits in the word and prove one burst symbolically; then the epoch change.

## First look

Growth class **fixed/power** (left: fixed, exponent 0.061; right: power,
exponent 0.172). After 1,000,000,000 steps: 293 cells visited (9 left of the
start, 273 right), 143 ones.

- right, step 578,396,324: `1^2 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1^5 0 1^15 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1^3 0 1 0 1^13 0 1 0 1 0 1 0 1^5 0 1^7 0 1 0 1 0 1 0 1^3 0 1^9 0 1 0 1 0 1 0 1 0 1^9 0 1^108 0 1 C>0`
- right, step 754,557,083: `1^2 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1^5 0 1^15 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1^3 0 1 0 1^13 0 1 0 1 0 1 0 1^13 0 1 0 1 0 1 0 1^3 0 1^9 0 1 0 1 0 1 0 1 0 1^9 0 1^113 0 1 C>0`

## Pages

- [`pages/holdouts/1RB1LA_1LA1RC_1RD0RB_1LE1LD_---1LF_1RA0LF/explainer.html`](../../pages/holdouts/1RB1LA_1LA1RC_1RD0RB_1LE1LD_---1LF_1RA0LF/explainer.html)
- [`pages/holdouts/1RB1LA_1LA1RC_1RD0RB_1LE1LD_---1LF_1RA0LF/proof-status.html`](../../pages/holdouts/1RB1LA_1LA1RC_1RD0RB_1LE1LD_---1LF_1RA0LF/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LA_1LA1RC_1RD0RB_1LE1LD_---1LF_1RA0LF/lean/check.sh
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB1LC_1LA1RB_1LD0LA_1RE1RD_---1RF_1LB0RF`](../1RB1LC_1LA1RB_1LD0LA_1RE1RD_---1RF_1LB0RF/README.md): rename A→B, B→A, C→C, D→D, E→E, F→F and exchange left and right; it is this table started in state B, in a mirror

<!-- end of related machines -->
