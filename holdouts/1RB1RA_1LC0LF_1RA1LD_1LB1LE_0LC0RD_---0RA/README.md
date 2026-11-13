# 1RB1RA_1LC0LF_1RA1LD_1LB1LE_0LC0RD_---0RA

bbchallenge id 129887. One of the six-state holdouts whose halting from blank tape is open (group G07, family: **periodic block at the growing end, eaten by a disordered middle**).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RA |
| B | 1LC | 0LF |
| C | 1RA | 1LD |
| D | 1LB | 1LE |
| E | 0LC | 0RD |
| F | --- | 0RA |

## What it does

The tape has three parts. At the left (growing) end sits a **periodic block**, `(1^5 0 1^2 0)^k` (at other times
`(1^8 0)^k`, another word of 9 cells). Each visit of the left end adds three
cells to it, one copy every three visits. To its right lies a **disordered middle**, runs of 1s of lengths
divisible by 3 separated by `0` and `110`; it keeps changing and eats the periodic block from the inside: the
block grows steadily, then at rare moments is swallowed almost entirely (14 times in the first 10^9 steps, last
at step 401,140,791, when at least 749 copies went at once). At the right, a short end region stopped growing early.

Snapshot at step 999,899,483 (`a = 111110110`, `b = 110`): `0 1 b a^2938 b^4 a b^11 1^6 b 1^3 b 1^3 b 1^9 a ...`

## Status

Open. Lean: the halting configurations and 10^7 steps (`lean/Blank.lean`), and shift rules for the head crossing
the periodic block (in state D, and in state E) and runs of `110`, for any length (`lean/Shifts.lean`, kernel). Simulation: no
halt in 10^11 steps (`tmrun`, about 30 minutes).

## Second look: when the block collapses

Following the copies of `1^5 0 1^2 0` at the left end at every visit of the left end in state D (up to 10^9 steps):
the block grows by exactly one copy every three visits and then is swallowed at once. The block had, just before
each collapse, 11, 9, 84, 36, 135, 100, 36, 324, 36, 36, 260, 999 and 36 copies (steps 29,371 to 419,367,273). The
value **36 recurs five times**, so the collapses are not random: the middle region probably triggers a collapse when
a carry inside it arrives, and the block size at that moment is set by the region's own clock. After a collapse the
left end shows `(1^8 0)^k` for a while (another word of 9 cells) before `1^5 0 1^2 0` takes over again.

## Next steps

* Record the middle region at the collapses (especially the five collapses at 36 copies) and compare: a recurring
  middle shape would give the region's clock.
* A macro simulator with the block as one symbol would reach much further.

## First look

Growth class **fixed/sqrt** (left: sqrt, exponent 0.539; right: fixed,
exponent 0.433). After 1,000,000,000 steps: 63,728 cells visited (37,689 left of the
start, 9,934 right), 51,851 ones.

- left, step 975,564,704: `D>0 1 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 `
- left, step 991,221,611: `D>0 1 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 `

## Pages

- [`pages/holdouts/1RB1RA_1LC0LF_1RA1LD_1LB1LE_0LC0RD_---0RA/explainer.html`](../../pages/holdouts/1RB1RA_1LC0LF_1RA1LD_1LB1LE_0LC0RD_---0RA/explainer.html)
- [`pages/holdouts/1RB1RA_1LC0LF_1RA1LD_1LB1LE_0LC0RD_---0RA/proof-status.html`](../../pages/holdouts/1RB1RA_1LC0LF_1RA1LD_1LB1LE_0LC0RD_---0RA/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RA_1LC0LF_1RA1LD_1LB1LE_0LC0RD_---0RA/lean/check.sh
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0RF_1LC1RD_1LA1LC_1RA1RE_0RB0LD_---0LC`](../1RB0RF_1LC1RD_1LA1LC_1RA1RE_0RB0LD_---0LC/README.md): rename A→C, B→A, C→B, D→D, E→E, F→F and exchange left and right; it is this table started in state B, in a mirror

<!-- end of related machines -->
