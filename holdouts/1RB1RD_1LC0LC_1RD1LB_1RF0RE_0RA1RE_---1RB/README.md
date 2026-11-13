# 1RB1RD_1LC0LC_1RD1LB_1RF0RE_0RA1RE_---1RB

bbchallenge id 148224. One of the six-state holdouts whose halting from blank tape is open (group G07).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RD |
| B | 1LC | 0LC |
| C | 1RD | 1LB |
| D | 1RF | 0RE |
| E | 0RA | 1RE |
| F | --- | 1RB |

## What it does

The same mechanism as 1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---0RC (see that README), with longer words. At each
visit of the left end in state B the tape, read rightwards, is `B>0 111 (011111)^n R`: a block that grows each sweep,
then a region `R` transformed by a map independent of `n`: a busy, chaotic stretch of about a hundred cells next to
the block, a reservoir of `111101` words, and a short old region. One event so far, at visit 8,347 (step about
1.2e8): `R` jumps from about 90 to 16,724 cells (a reservoir of 2,758 words).

The halting transition is F0, reached only as `D>0 0` moving right.

## Status

Open.

- **Kernel / native_decide:** `lean/Blank.lean`.
- **Computed (trusted):** `resetsim` (in `holdouts/1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---0RC/c/`) with `PREFIX=111`
  and the block cut to 10 words agrees with the true run at all of the first 9,000 visits (one event, at 8,347); from
  visit 8,400 it runs 4e6 visits (about 3e13 steps) without a halt.
- **Open:** the counter's rule, and whether an event halts.

```sh
gcc -O2 -o resetsim holdouts/1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---0RC/c/resetsim.c -I tools/c
PREFIX=111 ./resetsim 1RB1RD_1LC0LC_1RD1LB_1RF0RE_0RA1RE_---1RB L B 011111 10 1 9000 check
PREFIX=111 T0=8400 ./resetsim 1RB1RD_1LC0LC_1RD1LB_1RF0RE_0RA1RE_---1RB L B 011111 10 1 4000000
```

## Next steps

Measure the counter's front speed (the block's phase wobbles by two cells between sweeps, so compare sweeps of the
same parity) and the size of the old region, as for the related machines.

## Pages

- [`pages/holdouts/1RB1RD_1LC0LC_1RD1LB_1RF0RE_0RA1RE_---1RB/explainer.html`](../../pages/holdouts/1RB1RD_1LC0LC_1RD1LB_1RF0RE_0RA1RE_---1RB/explainer.html)
- [`pages/holdouts/1RB1RD_1LC0LC_1RD1LB_1RF0RE_0RA1RE_---1RB/proof-status.html`](../../pages/holdouts/1RB1RD_1LC0LC_1RD1LB_1RF0RE_0RA1RE_---1RB/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RD_1LC0LC_1RD1LB_1RF0RE_0RA1RE_---1RB/lean/check.sh
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA`](../1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA/README.md): rename A→E, B→A, C→B, D→C, E→D, F→F and exchange left and right; it is this table started in state B, in a mirror

<!-- end of related machines -->
