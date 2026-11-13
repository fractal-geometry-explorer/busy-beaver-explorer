# 1RB0RE_1LC1RD_1LD0LD_0RE0LC_1RA1RF_0RA---

bbchallenge id 100684. A marker 0 drifts through a long alternating sea one cell per sweep while a base-3 counter at the right end counts the sweeps; when the marker reaches the far end a reset sweep starts the next round, one cell wider.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RE |
| B | 1LC | 1RD |
| C | 1LD | 0LD |
| D | 0RE | 0LC |
| E | 1RA | 1RF |
| F | 0RA | --- |

## What it does

Stop the run when the head reaches a new cell on the right. With `a = 10`, `c = 1110`:

    83,145,834  0 a^2 0 a^918 c a^16 c a^8 c a^4 c a E>0
    83,433,665  0 a^83 0 a^837 c a^16 c a^8 c a^4 c a 1^3 D>0
    84,139,705  0 a^326 0 a^594 c a^16 c a^8 c a^4 c a c 1^3 D>0
    84,874,121  D>0 a^940 0^3 a^8 0 a 0 a^4 ...                    (reset sweep)
    84,880,069  0 a^2 0 a^937 c a^10 0 a^3 c a c^2 1^3 D>0

The left part is an alternating sea `0 a^x 0 a^y` (x + y fixed within a round) with one marker 0 after x copies of
`10`. The head shuttles between the marker and the right end; each round trip moves the marker one cell and
updates a counter in the right tail; the tape grows on the right only
when the counter gains a digit. Between right growths the marker moves by powers of 3 (81 x77, 243 x76, 27 x36, 9, 729
in the first 10^8 steps): the tail counts sweeps in base 3. When the marker reaches the end of the sea a long sweep
resets it and the sea grows by one cell, so the width grows like t^(1/3).

The near-duplicate `1RB1RF_1RC0RA_1LD1RE_1LE0LE_0RA0LD_0RB---` behaves the same way.

## Halting

F1 halts; F is entered only from E1 (`1RF`), so a halt needs E on a 1 with a 1 to its right. In the first 10^8 steps F
was entered 75,569 times, always on a 0, 75,111 times at least 7 cells from both ends (`c/sstat.c`). Open.

## Status

Open. Lean (`lean/Blank.lean`): the halting configurations (`step_none_iff`), no halt in 10,000 steps by the kernel, in 10,000,000 by `native_decide`. C: no halt in 10^9 steps (`tools/c/triage.c`) and in 10^15 steps (`c/mrun.c`, exact macro simulation). The structure described here is observed, not proved.

## First look

Growth class **power/power** (left: power, exponent 0.309; right: power,
exponent 0.343). After 1,000,000,000 steps: 4,543 cells visited (258 left of the
start, 3,472 right), 2,266 ones.

- left, step 971,573,686: `D>0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 `
- left, step 991,556,168: `D>0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 `
- right, step 980,145,629: `0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 `
- right, step 997,475,423: `0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 `




## Pages

- [`pages/holdouts/1RB0RE_1LC1RD_1LD0LD_0RE0LC_1RA1RF_0RA---/explainer.html`](../../pages/holdouts/1RB0RE_1LC1RD_1LD0LD_0RE0LC_1RA1RF_0RA---/explainer.html)
- [`pages/holdouts/1RB0RE_1LC1RD_1LD0LD_0RE0LC_1RA1RF_0RA---/proof-status.html`](../../pages/holdouts/1RB0RE_1LC1RD_1LD0LD_0RE0LC_1RA1RF_0RA---/proof-status.html)




## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RE_1LC1RD_1LD0LD_0RE0LC_1RA1RF_0RA---/lean/check.sh
gcc -O2 -o mrun holdouts/1RB0RE_1LC1RD_1LD0LD_0RE0LC_1RA1RF_0RA---/c/mrun.c && ./mrun 1RB0RE_1LC1RD_1LD0LD_0RE0LC_1RA1RF_0RA--- 2 1000000000000000
gcc -O2 -I tools/c -o sstat holdouts/1RB0RE_1LC1RD_1LD0LD_0RE0LC_1RA1RF_0RA---/c/sstat.c && ./sstat 1RB0RE_1LC1RD_1LD0LD_0RE0LC_1RA1RF_0RA--- 100000000
```

## Later

- Decode the tail exactly: which words are the base-3 digits, and the rule for a carry.
- From that, the marker's start position after each reset, and whether E can ever meet `1 1` (the F1 halt).
- The twin `1RB1RF_1RC0RA_1LD1RE_1LE0LE_0RA0LD_0RB---` probably has the same proof.

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB1RF_1RC0RA_1LD1RE_1LE0LE_0RA0LD_0RB---`](../1RB1RF_1RC0RA_1LD1RE_1LE0LE_0RA0LD_0RB---/README.md): rename A→B, B→C, C→D, D→E, E→A, F→F; it is this table started in state E
- [`1RB0RB_0LC0RA_1LE1LD_0LE---_1LF0LC_1RA1LB`](../1RB0RB_0LC0RA_1LE1LD_0LE---_1LF0LC_1RA1LB/README.md): rename A→E, B→F, C→A, D→B, E→C, F→D and exchange left and right; it is this table started in state C, in a mirror

<!-- end of related machines -->
