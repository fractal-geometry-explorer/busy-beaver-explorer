# 1RB1RC_1RC1RB_1LD0RA_1LE1LD_1LF0LC_0LA---

bbchallenge id 144803. One of the six-state holdouts whose halting from blank tape is open. **It rewrites a long list
of blocks of 1s, almost all of length `4k + 3` with `k` spread like a fair coin's run lengths; each round multiplies
the length of the list by about 1.75.** No closed-form rule is found yet; this folder records what was seen.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RC |
| B | 1RC | 1RB |
| C | 1LD | 0RA |
| D | 1LE | 1LD |
| E | 1LF | 0LC |
| F | 0LA | --- |

## What it does (observed)

The visited part of the tape lies right of the start; its left end moves by a cell or two per round. At the moments
the head reaches a new cell at the left end (`D> 0 1^a 0 1^b 0 …`), the tape is a list of blocks of 1s separated by
single 0s. Apart from the first two blocks and the last one, **every block has length `4k + 3`** (checked at each of
these moments up to step 5.2·10⁸), and the values of `k` are spread like the run lengths of fair coin flips: at step
522,867,988 there are 5,366 blocks, 2,665 with `k = 0`, 1,336 with `k = 1`, 716, 315, 160, 88, 47, 22, … for
`k = 2, 3, …` (each count about half the one before).

Between those moments the head sweeps across the whole list. A sweep to the right rewrites each block `1^(4k+3)`
into a string of short runs (`1 0 1 0 …` with longer runs between), and the sweep back to the left rewrites it into
blocks again, so the list changes as a whole (`c/turns.c` prints the tape at every reversal of the head). Bursts of
short sweeps near the left end alternate with long full sweeps. The *rounds*, the long gaps between visits of the
left end, start at

    step           blocks   Σ(k+1)
    3,664          14       26
    45,100         54       97
    584,746        183      351
    5,887,250      574      1,136
    55,865,122     1,794    3,508
    522,867,988    5,366    10,746

so each round multiplies `Σ(k+1)` (the length of the list read as a word in which block `4k + 3` stands for `k`
ones and a zero) by about 1.75 and the step count by about 3.1. A round costs about the square of the tape length,
so the tape grows like the square root of the step count on the right and slowly on the left: the exp/sqrt shape
the triage saw.

## Does it halt?

Open. Proved (Lean): only the generated facts in `lean/Blank.lean` (the halting configurations; no halt in 10⁷
steps). Computed: no halt in 10⁹ steps (`tools/c/triage.c`, and `c/sim.c`). The rule of a round is not known, so
neither is where a halt (state F reading a 1) could come from; no heuristic is given. The coin-like spread of the
block lengths suggests that the list behaves like a pseudo-random word that the rounds rewrite, as in the
Collatz-like holdouts.

## For later

More than a day of work remains. (1) Read the list as the binary word above (block `4k + 3` ↦ `1^k 0`) and look for
the map a round applies to it: the ratio 1.75 is close to √3, so test whether two rounds multiply a number written
in that word by 3 (or by 3/2 and by 2), in some base and bit order. (2) Find the sweep rules (each block's image in
a right sweep, the carries in a left sweep) and prove them with `symtm`. (3) Find the configurations that reach F on
a 1, and what they mean for the word.

## Files

- `c/sim.c`: plain simulation from blank tape, printing the edge events.
- `c/turns.c`: the tape at every reversal of the head, between two step counts.

## Status

Open. The claims with what each rests on are in `status.json` and the proof-status page.

## Deciders tried (F11, 13 November 2026)

None closes. Each reaches a halting configuration in its abstraction, which says nothing about halting.

- n-gram CPS (`tools/c/ngramcps.c`), equal widths on both sides: a halting local configuration is reached with plain up to width 24, history 1 up to width 24, history 2 up to width 24, history 3 up to width 24, LRU history up to width 6 (larger widths ran out of the 150 s or 60 million configuration budget).
- n-gram CPS with every cell tagged by its position mod p: fails for p = 2 up to width 20, p = 3 up to width 20, p = 4 up to width 20, p = 6 up to width 20.
- n-gram CPS where each side also carries the state of a small automaton that has read that side from the far end (every automaton with up to 3 states on both sides, or 4 states on one side), with position mod 1..4 and widths 4, 6, 8: no closed set without a halt in all 120 parameter sets.
- Run-length windows (the K nearest runs of equal macro cells on each side, run lengths kept exactly below T and mod M above): fails for all 72 parameter sets (cells of 1 to 4 bits, K = 2, 4, 6, T = 2, 4, M = 1, 2, 4).
- Two-automaton closed tape language by SAT (a deterministic automaton reading each side inward, n states each, CaDiCaL): no solution for n = 2..7; n = 8 not finished in 150 s.

## Where a halt can come from

`lean/Route.lean` (kernel, written by `py/route.py`): `halt_route`, two steps before any halt the machine is in one
of: D with 1 two left, 0 left, 0 under the head.

## Pages

- [`pages/holdouts/1RB1RC_1RC1RB_1LD0RA_1LE1LD_1LF0LC_0LA---/explainer.html`](../../pages/holdouts/1RB1RC_1RC1RB_1LD0RA_1LE1LD_1LF0LC_0LA---/explainer.html)
- [`pages/holdouts/1RB1RC_1RC1RB_1LD0RA_1LE1LD_1LF0LC_0LA---/proof-status.html`](../../pages/holdouts/1RB1RC_1RC1RB_1LD0RA_1LE1LD_1LF0LC_0LA---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RC_1RC1RB_1LD0RA_1LE1LD_1LF0LC_0LA---/lean/check.sh
gcc -O2 -o sim holdouts/1RB1RC_1RC1RB_1LD0RA_1LE1LD_1LF0LC_0LA---/c/sim.c && ./sim 1RB1RC_1RC1RB_1LD0RA_1LE1LD_1LF0LC_0LA--- 1000000000 1 | grep ' LD '
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB1RA_1LC0RF_1LD1LC_1LE0LB_0LF---_1RA1RB`](../1RB1RA_1LC0RF_1LD1LC_1LE0LB_0LF---_1RA1RB/README.md): rename A→F, B→A, C→B, D→C, E→D, F→E; it is this table started in state B
- [`1RB0LE_1RC1RB_1RD0RA_0RE---_1LF1LA_1LA1LF`](../1RB0LE_1RC1RB_1RD0RA_0RE---_1LF1LA_1LA1LF/README.md): rename A→E, B→F, C→A, D→B, E→C, F→D and exchange left and right; it is this table started in state C, in a mirror
- [`1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF`](../1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF/README.md): rename A→C, B→D, C→E, D→F, E→A, F→B and exchange left and right; it is this table started in state E, in a mirror

**Same tapes at another pace (observed, not proved).** Leave the states aside and compare only the tape and the place of the head. Then a large part of the first 10^7 configurations of this machine are configurations of the machines below, in the same order and up to the end of the run. The steps at which they occur differ, the tables are not renamings of each other, and equal tapes with different states may be continued differently, so this does not tie the halting questions together.

- [`1RB0RB_1LC---_0LA1LD_1RE0LC_1RF1RE_1RA0RD`](../1RB0RB_1LC---_0LA1LD_1RE0LC_1RF1RE_1RA0RD/README.md) (in a mirror): 4,990,813 configurations, the last at step 6,660,591 here and step 10,000,000 there

<!-- end of related machines -->
