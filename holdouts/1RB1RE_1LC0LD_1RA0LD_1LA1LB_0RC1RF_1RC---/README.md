# 1RB1RE_1LC0LD_1RA0LD_1LA1LB_0RC1RF_1RC---

bbchallenge id 139315. One of the six-state holdouts whose halting from blank tape is open (group G07, family: **two-representation block list (1^n blocks <-> (10)^k blocks) with an inner bouncer**).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RE |
| B | 1LC | 0LD |
| C | 1RA | 0LD |
| D | 1LA | 1LB |
| E | 0RC | 1RF |
| F | 1RC | --- |

## What it does

The tape is a list of blocks that the machine keeps in two spellings and flips between:

- **solid**, seen when the head reaches the right end: `1^n1 0 1^n2 0 1^n3 0 ...` (blocks of 1s, each followed by
  one 0), e.g. at step 7,302,364: `1^3061 0 1^125 0 1^1013 0 1^1173 0 1^337 0 1^645 0 1^865 0 1^385 0 1^73 0`;
- **sparse**, seen when the head reaches the left end soon after: `0 (10)^k1 1 (10)^k2 1 ...`, at step 7,310,065:
  `0 (10)^1531 1 (10)^63 1 (10)^507 1 (10)^587 1 (10)^169 1 (10)^323 1 (10)^433 1 (10)^193 1 (10)^37 1 10 1`.

The leftward pass rewrites each block `1^n 0` as `(10)^k 1` with k = floor(n/2) + 1 (so 1^3061 becomes (10)^1531;
checked at all 12 such pairs of records in the first 3·10^7 steps, for every block but the one next to the right
end, which is still being written). Between two flips the head bounces many times at the left end while a marker `00` travels right
through the `(10)` runs (three copies of `10` further per visit, early in the run), and this inner bouncer reorganizes the block lengths;
its exact effect on the list is not worked out. The left end grows like the square root of the steps; the right end
grows very slowly (from cell 25 at 10^5 steps to cell 36 at 3·10^6).

## Status

Open. Lean: the halting configurations and 10^7 steps (`lean/Blank.lean`), and two shift rules for runs of `110`
and `011` (`lean/Shifts.lean`, kernel). Simulation: no halt in 10^9 steps.

## Next steps

Write the inner bouncer as a rule on the sparse list (where the marker enters, what it does at each `1` separator),
which should give a map from one solid list to the next; then look for an invariant of that map that excludes the
halting transition F1.

## First look

Growth class **fixed/sqrt** (left: sqrt, exponent 0.477; right: fixed,
exponent 0.064). After 1,000,000,000 steps: 81,707 cells visited (60,742 left of the
start, 52 right), 42,934 ones.

- left, step 970,757,095: `D>0 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 `
- left, step 986,533,309: `D>0 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 `

## Pages

- [`pages/holdouts/1RB1RE_1LC0LD_1RA0LD_1LA1LB_0RC1RF_1RC---/explainer.html`](../../pages/holdouts/1RB1RE_1LC0LD_1RA0LD_1LA1LB_0RC1RF_1RC---/explainer.html)
- [`pages/holdouts/1RB1RE_1LC0LD_1RA0LD_1LA1LB_0RC1RF_1RC---/proof-status.html`](../../pages/holdouts/1RB1RE_1LC0LD_1RA0LD_1LA1LB_0RC1RF_1RC---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RE_1LC0LD_1RA0LD_1LA1LB_0RC1RF_1RC---/lean/check.sh
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB1RC_1LC1LE_1RD0RA_1LB0RA_0LD1LF_1LD---`](../1RB1RC_1LC1LE_1RD0RA_1LB0RA_0LD1LF_1LD---/README.md): rename A→B, B→C, C→D, D→A, E→E, F→F and exchange left and right; it is this table started in state D, in a mirror
- [`1RB0LD_1RC1RE_1LA0LD_1LB1LC_0RA1RF_1RA---`](../1RB0LD_1RC1RE_1LA0LD_1LB1LC_0RA1RF_1RA---/README.md): rename A→B, B→C, C→A, D→D, E→E, F→F; it is this table started in state C
- [`1RB0RE_1LC0RE_1LA1LD_0LB1LF_1RC1RA_1LB---`](../1RB0RE_1LC0RE_1LA1LD_0LB1LF_1RC1RA_1LB---/README.md): rename A→C, B→A, C→B, D→E, E→D, F→F and exchange left and right; it is this table started in state B, in a mirror

<!-- end of related machines -->
