# 1RB0RE_1LC0RA_0LD1LB_1LA1LF_0LB0RD_0LB---

bbchallenge id 71717. A bouncer over 8-cell words: going left the head turns v = 10100100 into u = 11111010; the u side carries separators whose spacings shrink by about half from one group to the next, like the digits of a counter; sibling of 1RB0RE_1LC0RA_0LD1LB_1LA1LE_0LB0LF_1LD---.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RE |
| B | 1LC | 0RA |
| C | 0LD | 1LB |
| D | 1LA | 1LF |
| E | 0LB | 0RD |
| F | 0LB | --- |

## What it does

Words `v = 10100100`, `u = 11111010`. Step 10^9:

    v^1269 0 1 0 v^392 1 0 [A0] 1 0 1 0 u^859 111 0 1 0 u^208 111 0 1 0 u^208 11 u^992 1^6 u^234 1^4 u 1 0 u^235
    11 u^437 1^6 u^151 1^6 u^152 11 u^198 ... u^98 111 0 1 0 u^44 111 0 1 0 u^44 11 u^46 ... u^23 11 u^23 ... 1^9

A run of `v` on the left (grows like sqrt(time)), then `u`-blocks split by short markers (`111 0 1 0`, `11`, `1^6`,
`1^4 u 1 0`). The block sizes come in groups of about three similar values, halving from group to group: a counter
stored in the gaps (observed).

**Proved** (`lean/Rules.lean`): going left, B, C, D, F turn runs of rotations of `v` into rotations of `u` (8 rules),
plus the sweeps over `(10)^n` / `(01)^n` shared with the sibling machine.

## Halting

Only F1 halts; F is entered only from D1 (1LF): halts iff `1 D> 1`. CTL K = 3..6: halts remain; n-gram CPS 3..7
fails; no invariant mod 2..12; no halt in 10^9 steps.

## Notes for later

- Derive how a pass rewrites the markers (sample at the turn at the v/u boundary), then the counter.
- Sibling: `1RB0RE_1LC0RA_0LD1LB_1LA1LE_0LB0LF_1LD---` (Collatz-like map, proved up to 1.68·10^14 steps).

## Pages

- [`pages/holdouts/1RB0RE_1LC0RA_0LD1LB_1LA1LF_0LB0RD_0LB---/explainer.html`](../../pages/holdouts/1RB0RE_1LC0RA_0LD1LB_1LA1LF_0LB0RD_0LB---/explainer.html)
- [`pages/holdouts/1RB0RE_1LC0RA_0LD1LB_1LA1LF_0LB0RD_0LB---/proof-status.html`](../../pages/holdouts/1RB0RE_1LC0RA_0LD1LB_1LA1LF_0LB0RD_0LB---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RE_1LC0RA_0LD1LB_1LA1LF_0LB0RD_0LB---/lean/check.sh
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0LD_0RC1RA_1RD1RF_1LA0LE_0RA0LC_0RA---`](../1RB0LD_0RC1RA_1RD1RF_1LA0LE_0RA0LC_0RA---/README.md): rename A→D, B→A, C→B, D→C, E→E, F→F and exchange left and right; it is this table started in state B, in a mirror

**Same tapes at another pace (observed, not proved).** Leave the states aside and compare only the tape and the place of the head. Then a large part of the first 10^7 configurations of this machine are configurations of the machines below, in the same order and up to the end of the run. The steps at which they occur differ, the tables are not renamings of each other, and equal tapes with different states may be continued differently, so this does not tie the halting questions together.

- [`1RB1RF_1LC0LF_1RD0LB_0RA1RE_1RD---_0RC0LA`](../1RB1RF_1LC0LF_1RD0LB_0RA1RE_1RD---_0RC0LA/README.md) (in a mirror): 9,999,977 configurations, the last at step 10,000,000 here and step 9,999,986 there

<!-- end of related machines -->
