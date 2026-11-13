# 1RB1RD_1LC---_1RF0LD_0RE1LC_1RA1RF_1RE0LF

bbchallenge id 139327. One of the six-state holdouts whose halting from blank tape is open. Its run looks chaotic on a tape that grows roughly logarithmically.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RD |
| B | 1LC | --- |
| C | 1RF | 0LD |
| D | 0RE | 1LC |
| E | 1RA | 1RF |
| F | 1RE | 0LF |

## Status

Open. Lean (`lean/Blank.lean`): the halting configurations (`step_none_iff`), no halt in 10,000 steps by the kernel, in 10,000,000 by `native_decide`. C (`tools/c/tmrun.c`): no halt in 10,000,000,000 steps.

## What it does

The tape is a sequence of the words <code>110</code> and <code>1111</code> in no visible order (with an occasional stray 0 or 1), and the run keeps rewriting it. It grows mainly at the right end, by about 100 cells per tenfold increase in time.

- **Growth.** Cells visited: 218 (10^6), 292 (10^7), 405 (10^8), 491 (10^9), 652 (10^10) steps.
- **Halting.** Only B1 halts; B is entered only from A0 (`1RB`), 3,447,235 times in 10^8 steps, always onto a 0.
- **No structure found.** `bbtools.macro` with blocks of 3 / 6 cells needs one macro step per ~3 / ~6-7 steps
  over 10^7 steps; `bbtools.cycles` (k = 4) finds no linear cycle in 10^7 steps; CTL windows up to 8 cells do not close (group scan).

## Later

- Look for an invariant (a regular language of tapes, or a weighted count) that excludes the halting pattern;
  try CTL with word-based windows (the tape is made of a few words) instead of fixed cell windows.

## First look

Growth class **fixed/power** (left: fixed, exponent 0.13; right: power,
exponent 0.138). After 1,000,000,000 steps: 492 cells visited (46 left of the
start, 437 right), 245 ones.

- right, step 547,946,068: `0 1^2 0 1^2 0 1^6 0 1^2 0 1^2 0 1^22 0 1^10 0 1^2 0 1^6 0 1^10 0 1^6 0 1^18 0 1^10 0 1^14 0 1^6 0 1^6 0 1^10 0 1^10 0 1^6 0 1^6 0 1^10 0 1^10 0 1^2 0 1^2 0 1^2 0 1^10 0 1^6 0 1^10 0 1^2 0 1^2 0 1^6 0 1^54 0 1^22 0 1^6 0 1^34 0 1^10 0 1^14 0 1^6 0 1^30 0 1^4 0 1^6 0 1^10 0 1^27 F>0`
- right, step 588,948,032: `0 1^2 0 1^2 0 1^2 0 1^6 0 1^2 0 1^10 0 1^6 0 1^10 0 1^2 0 1^22 0 1^10 0 1^6 0 1^14 0 1^2 0 1^10 0 1^18 0 1^2 0 1^2 0 1^6 0 1^18 0 1^10 0 1^2 0 1^2 0 1^10 0 1^6 0 1^6 0 1^10 0 1^2 0 1^26 0 1^22 0 1^2 0 1^18 0 1^10 0 1^10 0 1^10 0 1^22 0 1^46 0 1^6 0 1^26 0 1^2 0 1^10 0 1^8 0 1^27 F>0`

## Pages

- [`pages/holdouts/1RB1RD_1LC---_1RF0LD_0RE1LC_1RA1RF_1RE0LF/explainer.html`](../../pages/holdouts/1RB1RD_1LC---_1RF0LD_0RE1LC_1RA1RF_1RE0LF/explainer.html)
- [`pages/holdouts/1RB1RD_1LC---_1RF0LD_0RE1LC_1RA1RF_1RE0LF/proof-status.html`](../../pages/holdouts/1RB1RD_1LC---_1RF0LD_0RE1LC_1RA1RF_1RE0LF/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RD_1LC---_1RF0LD_0RE1LC_1RA1RF_1RE0LF/lean/check.sh
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0LF_1RC0LB_1RD1RB_1RE1RF_1LA---_0RC1LA`](../../bb6-1RB0LF_1RC0LB/README.md): rename A→D, B→E, C→A, D→F, E→C, F→B; it is this table started in state C

<!-- end of related machines -->
