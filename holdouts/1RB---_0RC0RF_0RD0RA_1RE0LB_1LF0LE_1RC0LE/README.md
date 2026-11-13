# 1RB---_0RC0RF_0RD0RA_1RE0LB_1LF0LE_1RC0LE

bbchallenge id 21494.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | --- |
| B | 0RC | 0RF |
| C | 0RD | 0RA |
| D | 1RE | 0LB |
| E | 1LF | 0LE |
| F | 1RC | 0LE |

## Status

**Open.** A bouncer whose first block grows by one cell per sweep; behind it a region of defects in the 1010... background, moved one cell at a time by a zig-zagging head, grows about logarithmically and looks irregular.

## What it does

Read the tape as the gaps between consecutive 1s. The background is gap 1 (`1010...`), and the defects are gaps
of 2 (`00`, now and then 3). Each time the head, in state F, is at the left end of the tape with the background
there, the tape is

    1^n0  2  1^n1  2  1^n2  2 ...  2  1^nk          (gap list; 1^n = n gaps of 1, 2 = a defect)

and from one such moment to the next (a *round*, about 3,500 steps at n0 = 800) the first block grows by one
(`n0`: 801, 802, 803, ...). In a round the head runs across the first block, then zig-zags slowly (a few cells
forward, a few back) through the defect region, moving one or two defects by a cell, and returns. The first
blocks behind it barely move (7, 12, 24 then 6, 13, 25 and so on, a ±1 wobble), the later ones change at random
looking. The number of defects grows very slowly, about logarithmically: 16 at 10^5 steps, 21 at 10^6, 26 at
10^8, 28 at 10^9; the right end of the tape grows with it (a few hundred records in 10^8 steps, against 13,000 at
the left).

So the machine is a sweeping bouncer whose far end is a slowly growing, irregular region of defects. What the
defect region does over long times, and whether a defect pattern that halts (A reading 1) can form there, is not
understood.

## Results

- `py/view.py` (with `c/blocks.c`, `c/gaps.c`) prints the views of the run quoted above; `python3 py/view.py 1e9 3000` is the gap view at the left end.
- Lean (`lean/Blank.lean`): no halt in 10^7 steps; C (`tools/c/triage.c`): none in 10^9.
- No macro rule is proved yet. Next step: find the rule by which a sweep moves the defects (the zig-zag), then the induced map on the gap list.

## First look

Growth class **fixed/sqrt** (left: sqrt, exponent 0.528; right: fixed,
exponent 0.045). After 1,000,000,000 steps: 44,247 cells visited (31,864 left of the
start, 426 right), 22,110 ones.

- left, step 970,092,477: `E>0 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 `
- left, step 985,770,725: `E>0 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 `

## Deciders tried (F11, 13 November 2026)

None closes. Each reaches a halting configuration in its abstraction, which says nothing about halting.

- n-gram CPS (`tools/c/ngramcps.c`), equal widths on both sides: a halting local configuration is reached with plain up to width 24, history 1 up to width 20, history 2 up to width 20, history 3 up to width 20, LRU history up to width 10 (larger widths ran out of the 150 s or 60 million configuration budget).
- n-gram CPS with every cell tagged by its position mod p: fails for p = 2 up to width 16, p = 3 up to width 16, p = 4 up to width 16, p = 6 up to width 16.
- n-gram CPS where each side also carries the state of a small automaton that has read that side from the far end (every automaton with up to 3 states on both sides, or 4 states on one side), with position mod 1..4 and widths 4, 6, 8: no closed set without a halt in all 120 parameter sets.
- Run-length windows (the K nearest runs of equal macro cells on each side, run lengths kept exactly below T and mod M above): fails for all 72 parameter sets (cells of 1 to 4 bits, K = 2, 4, 6, T = 2, 4, M = 1, 2, 4).
- Two-automaton closed tape language by SAT (a deterministic automaton reading each side inward, n states each, CaDiCaL): no solution for n = 2..8; n = 9 not finished in 150 s.

## Where a halt can come from

`lean/Route.lean` (kernel, written by `py/route.py`): `halt_route`, two steps before any halt the machine is in one
of: B with 0 under the head, 1 right, 1 two right; F with 0 under the head, 1 right, 1 two right.

## Pages

- [`pages/holdouts/1RB---_0RC0RF_0RD0RA_1RE0LB_1LF0LE_1RC0LE/explainer.html`](../../pages/holdouts/1RB---_0RC0RF_0RD0RA_1RE0LB_1LF0LE_1RC0LE/explainer.html)
- [`pages/holdouts/1RB---_0RC0RF_0RD0RA_1RE0LB_1LF0LE_1RC0LE/proof-status.html`](../../pages/holdouts/1RB---_0RC0RF_0RD0RA_1RE0LB_1LF0LE_1RC0LE/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB---_0RC0RF_0RD0RA_1RE0LB_1LF0LE_1RC0LE/lean/check.sh
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0RA_1LC0RA_0LF0LD_1LE---_0LC0LB_1LA0RE`](../1RB0RA_1LC0RA_0LF0LD_1LE---_0LC0LB_1LA0RE/README.md): rename A→D, B→E, C→C, D→F, E→A, F→B and exchange left and right; it is this table started in state E, in a mirror

<!-- end of related machines -->
