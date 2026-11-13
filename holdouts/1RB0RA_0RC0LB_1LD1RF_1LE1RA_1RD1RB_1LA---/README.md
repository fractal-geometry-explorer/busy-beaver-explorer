# 1RB0RA_0RC0LB_1LD1RF_1LE1RA_1RD1RB_1LA---

bbchallenge id 97509. One of the six-state holdouts whose halting from blank tape is open; analyzed by hand (group G02). The pages are built from [`status.json`](status.json).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RA |
| B | 0RC | 0LB |
| C | 1LD | 1RF |
| D | 1LE | 1RA |
| E | 1RD | 1RB |
| F | 1LA | --- |

## What it does

Read in words `a = 11010`, `b = 10000`, `c = 10`, the tape at the start of every round is a short gadget at the
left end, then a list of blocks `b^n1 c 00 b^n2 c 00 ... b^nk`, and the head in C at the right end. For example at
step 10,278,686,777:

    1 c 1 a 00 b 1 a 00 b^6 1 a 00 b^7 c 00 b^4 c 00 b^12 c 00 b^26 c 00 b^49 c 00 b^287 c 00 b^387 c 00 b^780 c 00 b^1554 c 00 b^9306 c 00 b^12415 1 a 00 c 00 c C>

- **Inside a round (a bouncer).** The head bounces between the right end and the block it is working on. Each pair of
  sweeps turns the last `b` of the block into an `a` and adds an `a` to a tail at the right end (5 cells per two
  sweeps: the square-root side). Proved for all counts (`sweep`, `lean/Rules.lean`):
  `b^(n+1) 1 a^(m+1) 1 c 1 a^(k+1) 0000 c C>  ->  b^n 1 a^(m+2) 1 c 1 a^(k+2) 0000 c C>` in 50k + 50m + 287 steps.
- **End of a round.** When every block is a's, the head goes to the left end, steps the gadget (about 2 new cells:
  the logarithmic side), and a pass turns all a's back into b's; the tail becomes a new block.
- **Round rule (observed).** The new block is, up to a few cells, the sum of all the old blocks, so the total doubles
  each round: 3, 21, 61, 152, 341, 720, 1491, 3038, 6138, 12339, 24743, 49564, 99212 (to 6.5·10^11 steps). Worked
  example: the round from step 2,568,368,685 has blocks 11, 4, 12, 26, 49, 287, 387, 780, 1554, 9305 (sum 12,415)
  and the next round's new block is exactly 12,415. In some rounds (at 2·10^6 and 2.6·10^9 steps) the new block
  absorbs the previous largest instead of standing next to it. A round takes about 4 times as long as the last.

`py/rounds.py` prints the rounds from the shared cycle accelerator (`bbtools.cycles`, blocks of 5 cells).

## Status

Open. The only halt is F reading a 1. F is entered after C reads a 1, about once per 50 steps; in the first 2·10^8
steps (4,004,892 visits) it always had `0101` to its left and a 0 under the head. The block cycle never puts F on
a 1; a halt could only come from the irregular moments (the turn at the left end, merging blocks), which are not
understood. No probabilistic argument either way.

- Lean, kernel: the halting configurations, 10^4 steps from blank (`lean/Blank.lean`); the block cycle for all
  counts (`lean/Rules.lean`). `native_decide`: 10^7 steps.
- Computed: no halt in 10^9 steps (`tools/c/triage.c`), in 10^12 steps with the cycle accelerator (each jump a
  symbolically proved one-cycle rule); `bbtools.ctl` closes for K = 2..6 but allows F to read 1, no closed set at
  K = 7; n-gram CPS (widths 3..7, -H, -U) fails.

## Notes for later

- Find the exact round map, including the left-end gadget (it alternates between two shapes, `a 00 1 a 00 b^3 1 a
  00 b^x` and `1 c 1 a 00 b 1 a 00 b^6 1 a 00 b^y`) and the rule for when the new block merges with the largest.
- Then prove the round as a Lean rule (it is a composition of `sweep` and a few transitions) and look for an
  invariant that keeps F off a 1.

## Round map for the whole block list (observed)

`py/ctxmulti.py` in the folder of `1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---` samples the run at the left-end turn (state
B reading 0 with only 0s to the left), cuts the tape into runs of repeated words, and computes the next turn from small
instances (every long run short, then lengthened one at a time; new counts affine in the old; two check instances).
It predicts all 17 next turns of the direct run to 3e9 steps. Iterated beyond it: 40 more turns without a halt, about
50 blocks, largest count 69 bits; stopped by a time limit, not by the machine. An extrapolation, not a proof.

    python3 holdouts/1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---/py/ctxmulti.py 1RB0RA_0RC0LB_1LD1RF_1LE1RA_1RD1RB_1LA--- L B 0 check 3e9
    python3 holdouts/1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---/py/ctxmulti.py 1RB0RA_0RC0LB_1LD1RF_1LE1RA_1RD1RB_1LA--- L B 0 orbit 40

## Pages

- [`pages/holdouts/1RB0RA_0RC0LB_1LD1RF_1LE1RA_1RD1RB_1LA---/explainer.html`](../../pages/holdouts/1RB0RA_0RC0LB_1LD1RF_1LE1RA_1RD1RB_1LA---/explainer.html)
- [`pages/holdouts/1RB0RA_0RC0LB_1LD1RF_1LE1RA_1RD1RB_1LA---/proof-status.html`](../../pages/holdouts/1RB0RA_0RC0LB_1LD1RF_1LE1RA_1RD1RB_1LA---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RA_0RC0LB_1LD1RF_1LE1RA_1RD1RB_1LA---/lean/check.sh
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB1LF_1RC1LD_1LB1LE_1LE0LD_0LA0RE_1RD---`](../1RB1LF_1RC1LD_1LB1LE_1LE0LD_0LA0RE_1RD---/README.md): rename A→D, B→E, C→A, D→B, E→C, F→F and exchange left and right; it is this table started in state C, in a mirror
- [`1RB1LC_1LA1LD_1LD0LC_0LE0RD_1RA1LF_1RC---`](../1RB1LC_1LA1LD_1LD0LC_0LE0RD_1RA1LF_1RC---/README.md): rename A→C, B→D, C→E, D→A, E→B, F→F and exchange left and right; it is this table started in state D, in a mirror

<!-- end of related machines -->
