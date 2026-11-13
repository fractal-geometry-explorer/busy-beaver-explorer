# 1RB0RC_1LC0LD_1RA0LB_1LE0RA_1LB1LF_0LC---

bbchallenge id 95984. One of the six-state holdouts whose halting from blank tape is open; analyzed by hand (group G02). The pages are built from [`status.json`](status.json).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RC |
| B | 1LC | 0LD |
| C | 1RA | 0LB |
| D | 1LE | 0RA |
| E | 1LB | 1LF |
| F | 0LC | --- |

## What it does

With the head in B at the left end, the tape is a list of blocks of `a = 10` separated by `0 1 a 0` (`01100`).
Step 2,999,883,891 (width 116,432):

    B>0 a^3636 0 1 a 0 a^5830 0 1 a 0 a^16251 0 1 a 0 a^2626 ... a^113 0 1 a 0 a^369 (repeated) ... a^9 0 1 a 0 a^41 (repeated) ... a 0 1 a 0 a 0 1 a 0 1

- The first few blocks trade units, about one per round trip, in long phases (the leftmost block fell from 3,644 to
  3,636 over 8 round trips near 3·10^9 steps); the tape grows by about 2 cells per round trip on the left (square
  root of the steps).
- Further right the blocks repeat periodically (113, 369, ...; 9, 41, ...; 1, 1, ...): fossils of earlier phases.
- The head reaches the right end only in rare phases (932 times in 9·10^8 steps): the logarithmic side.
- Proved for every n (`lean/Rules.lean`): `A> (10)^n -> (01)^n A>` and `C> (01)^n -> (10)^n C>` (2n steps).

## Status

Open. The only halt is F reading a 1; F follows E reading a 1 after D read a 0, going left. In 10^9 steps F was
entered 626,994 times, always on a 0 with `11001` to its right. A halt needs a left-moving D to meet `1 1 0`.

- Lean, kernel: the shift rules (`lean/Rules.lean`); halting configurations, 10^4 steps (`lean/Blank.lean`).
  `native_decide`: 10^7 steps.
- Computed: no halt in 10^10 steps (`tools/c/tmrun.c`); `bbtools.ctl` K = 2..6 allows a halt, no closed set at K = 7; n-gram CPS fails;
  the cycle accelerator (`bbtools.cycles`, blocks of 2 and 7) finds no linear cycle at the tape ends.

## Notes for later

- Sample at the left end in B and write the first few block counts per round trip: find the transfer rule
  between blocks and what starts a phase reaching the right end.

## Pages

- [`pages/holdouts/1RB0RC_1LC0LD_1RA0LB_1LE0RA_1LB1LF_0LC---/explainer.html`](../../pages/holdouts/1RB0RC_1LC0LD_1RA0LB_1LE0RA_1LB1LF_0LC---/explainer.html)
- [`pages/holdouts/1RB0RC_1LC0LD_1RA0LB_1LE0RA_1LB1LF_0LC---/proof-status.html`](../../pages/holdouts/1RB0RC_1LC0LD_1RA0LB_1LE0RA_1LB1LF_0LC---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RC_1LC0LD_1RA0LB_1LE0RA_1LB1LF_0LC---/lean/check.sh
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0LE_1RC1RF_1RD0RA_1LE0RC_1LC0LD_0RD---`](../1RB0LE_1RC1RF_1RD0RA_1LE0RC_1LC0LD_0RD---/README.md): rename A→E, B→C, C→D, D→A, E→B, F→F and exchange left and right; it is this table started in state D, in a mirror
- [`1RB0LC_1RC0RA_1LA0LD_1LE0RB_1LC1LF_0LA---`](../1RB0LC_1RC0RA_1LA0LD_1LE0RB_1LC1LF_0LA---/README.md): rename A→B, B→C, C→A, D→D, E→E, F→F; it is this table started in state C
- [`1RB0RD_1LC0RA_1LA0LB_1RE0LC_1RA1RF_0RB---`](../1RB0RD_1LC0RA_1LA0LB_1RE0LC_1RA1RF_0RB---/README.md): rename A→C, B→A, C→B, D→D, E→E, F→F and exchange left and right; it is this table started in state B, in a mirror

<!-- end of related machines -->
