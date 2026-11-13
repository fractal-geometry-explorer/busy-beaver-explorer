# 1RB0LE_1LC0RE_0RA0LD_1LA0LF_0LC0RA_0RE---

bbchallenge id 43701. One of the six-state holdouts whose halting from blank tape is open. Its run looks chaotic on a tape that grows roughly logarithmically.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LE |
| B | 1LC | 0RE |
| C | 0RA | 0LD |
| D | 1LA | 0LF |
| E | 0LC | 0RA |
| F | 0RE | --- |

## Status

Open. Lean (`lean/Blank.lean`): the halting configurations (`step_none_iff`), no halt in 10,000 steps by the kernel, in 10,000,000 by `native_decide`. C (`tools/c/tmrun.c`): no halt in 10,000,000,000 steps.

## What it does

The tape is an irregular mixture of the words <code>10</code>, <code>1000</code> and <code>110</code>, with a wall of repeated <code>101</code>s at the left end. The wall's length wanders up and down (between 8 and 17 copies after 10<sup>8</sup> steps), and the visited region grows by only about 20 to 25 cells per tenfold increase in time. It is a close relative of 1RB0LE_1LC0RE_0RA0LD_1LA1LF, which differs in three transitions and behaves the same way.

- **Growth.** Cells visited: 163 (10^6), 174 (10^7), 221 (10^8), 238 (10^9), 257 (10^10) steps.
- **Halting.** Only F1 halts; F is entered only from D1 (`0LF`), 72 times in 10^8 steps, always with a 0 to the left.
- **No structure found.** `bbtools.macro` with blocks of 3 / 6 cells needs one macro step per ~3 / ~6-7 steps
  over 10^7 steps; `bbtools.cycles` (k = 4) finds no linear cycle in 10^7 steps; CTL windows up to 8 cells do not close (group scan).

## Later

- Look for an invariant (a regular language of tapes, or a weighted count) that excludes the halting pattern;
  try CTL with word-based windows (the tape is made of a few words) instead of fixed cell windows.

## First look

Growth class **fixed/fixed** (left: fixed, exponent 0.082; right: fixed,
exponent 0.056). After 1,000,000,000 steps: 239 cells visited (191 left of the
start, 47 right), 101 ones.

## Pages

- [`pages/holdouts/1RB0LE_1LC0RE_0RA0LD_1LA0LF_0LC0RA_0RE---/explainer.html`](../../pages/holdouts/1RB0LE_1LC0RE_0RA0LD_1LA0LF_0LC0RA_0RE---/explainer.html)
- [`pages/holdouts/1RB0LE_1LC0RE_0RA0LD_1LA0LF_0LC0RA_0RE---/proof-status.html`](../../pages/holdouts/1RB0LE_1LC0RE_0RA0LD_1LA0LF_0LC0RA_0RE---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LE_1LC0RE_0RA0LD_1LA0LF_0LC0RA_0RE---/lean/check.sh
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same tapes at another pace (observed, not proved).** Leave the states aside and compare only the tape and the place of the head. Then a large part of the first 10^7 configurations of this machine are configurations of the machines below, in the same order and up to the end of the run. The steps at which they occur differ, the tables are not renamings of each other, and equal tapes with different states may be continued differently, so this does not tie the halting questions together.

- [`1RB0LD_0LC0RE_1LA0RD_0RB0LF_1RC1LA_0RB---`](../1RB0LD_0LC0RE_1LA0RD_0RB0LF_1RC1LA_0RB---/README.md) (in a mirror): 9,285,736 configurations, the last at step 9,285,895 here and step 10,000,000 there

<!-- end of related machines -->
