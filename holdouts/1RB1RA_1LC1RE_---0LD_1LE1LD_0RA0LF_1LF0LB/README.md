# 1RB1RA_1LC1RE_---0LD_1LE1LD_0RA0LF_1LF0LB

bbchallenge id 92364. One of the six-state holdouts whose halting from blank tape is open (group G07). Family: **unary visit counter fed to an irregular word** (mirror-image sibling of [`1RB1RA_0LC0RF_1LD1LC_1RE1LB_---0RA_1RF0RD`](../1RB1RA_0LC0RF_1LD1LC_1RE1LB_---0RA_1RF0RD/README.md)). Decision: **open**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RA |
| B | 1LC | 1RE |
| C | --- | 0LD |
| D | 1LE | 1LD |
| E | 0RA | 0LF |
| F | 1LF | 0LB |

## What it does

**It is the mirror image of `1RB1RA_0LC0RF_1LD1LC_1RE1LB_---0RA_1RF0RD`, started in another state.** Reflect this machine (swap L and R) and rename its
states A, B, C, D, E, F to C, D, E, A, B, F: the result is the table of `1RB1RA_0LC0RF_1LD1LC_1RE1LB_---0RA_1RF0RD`, entry by entry (`py/sibling.py`,
exact). So this machine from blank tape is the mirror image of `1RB1RA_0LC0RF_1LD1LC_1RE1LB_---0RA_1RF0RD` started on blank tape in *its* state C; and
`1RB1RA_0LC0RF_1LD1LC_1RE1LB_---0RA_1RF0RD` from blank tape is, after three steps, in state C on a blank cell with a single 1 on its right:
the same configuration with one 1 more. That 1 is the first cell of the run of 1s, the visit counter, and the irregular word W next to the run never sees how long the run is
(see the sibling's README). So the two machines stay in step for ever, unless one of them halts:

* at every visit of the far end the word W is the same, cell for cell (mirrored), and **this machine's run is one
  cell shorter** (`py/sibling.py`: checked at each of the first visits; `c/runsim.c ... 1` on both machines: equal W
  length, equal depth and eating statistics, run one shorter, at 3·10^7 visits);
* this machine has made 2 steps fewer per visit: visit 30,000,000 is at step 864,573,434,721,961 here (run
  28,822,305, W 1,178,039 cells) and at step 864,573,494,721,963 there.

Everything in the sibling's README about W and the run holds here, mirrored: the tape is `1^N W` with the run on
the left, D climbs the run (N steps, Lean `cross_ones_left`), adds a 1 at its end (D0 -> 1LE, E0 -> 0RA) and A
comes back (`cross_ones_right`); W eats the run from its foot. The halting transition C0 is the sibling's E0; the
closed tape language of windows of 3 cells (`python3 -m bbtools.ctl 1RB1RA_1LC1RE_---0LD_1LE1LD_0RA0LF_1LF0LB 3`) allows it only with blank tape left
of the head (in Lean: `halts_iff_left_edge`, `lean/Edge.lean`): **it halts iff W eats the whole run between two visits.** In 3·10^7 visits (8.6·10^14 steps) W eats at
most 14 cells in a visit (none in 68% of the visits, geometric tail), the run gains 0.961 cells a visit and the
head never goes more than 1,202 cells into W: it almost certainly never halts, and a proof for one machine is a
proof for the other except for the one cell of difference.

The block of 1s: N = 4,748 at step 2.6·10^7, 14,358 at 2.2·10^8, 28,334 at 8.7·10^8, 43,506 at 2·10^9.

## Status

Open.

* **Kernel**: the halting configurations and 10^4 steps (`lean/Blank.lean`; 10^7 by `native_decide`), the two
  crossings of the block of 1s for every length (`lean/Shifts.lean`).
* **Kernel**: `lean/Edge.lean`, `halts_iff_left_edge`: the machine halts from blank tape iff C reads a 0 with only
  blank tape on its left (closed tape language of 3-cell windows, `lean/EdgeCert.lean`, and the library lemma
  `TM.CTL.halt_left_blank`). Since the tape is `0^inf 1^N W`, that is: iff W eats the whole run.
* **Exact (script)**: the tables of the two machines are mirror images up to the renaming (`py/sibling.py`).
* **Trusted**: the two runs stay in step (same W, run one shorter) at 3·10^7 visits; no halt in 3·10^7 visits =
  864,573,434,721,961 steps (`c/runsim.c`, the run as a number, agrees with its cell-by-cell mode).
* **Trusted**: no halt in 3,000,000,000 visits = 8,645,095,534,069,998,883 steps (run 2,881,805,589, W 118,194,755 cells) (`c/wstats.c` 3000000000 100000000, about two hours: the same exact run with W in a ring
  buffer; agrees with `c/runsim.c` on every line it prints).
* **Heuristic**: it never halts.
* **Open**: W's dynamics, and so whether W ever eats the whole run.

## Next steps

* The same as for the sibling: a bound on what W can eat in one excursion (see its README).
* A rigid description of the chaotic engine next to the run, or a bound on what one excursion can eat for every
  reachable W (see the third look below).
* In Lean: the mirror-and-rename conjugacy between the two machines is a finite check of the tables plus a
  general lemma about reflected machines; the "one cell shorter" relation needs the statement that W's steps do not
  depend on the length of the run.

## Third look (20 November 2026): a chaotic engine with exponential tails

A block-compressed simulation finds no period in the tape for any block size (1-12 cells), and this pass says why:
**the word W is not a counter or any other regular structure; it behaves like a small chaotic engine that drifts
slowly into the run and leaves a random-looking trail behind.** All numbers below are from `c/wstats.c` (exact).

* **Only a short stretch of W is alive.** An excursion (from one visit to the next) reads at most a few hundred
  cells of W next to the run. The depth has an exponential tail with a constant ratio: each further 128 cells is
  about 4.7 times rarer (a decay length of about 83 cells). Over the first 10^8 visits:

  | depth at least | 16 | 64 | 256 | 512 | 768 | 1,024 | 1,280 | 1,408 |
  |---|---|---|---|---|---|---|---|---|
  | share of visits | 68% | 18.5% | 1.2% | 5.0·10^-4 | 2.2·10^-5 | 1.1·10^-6 | 2·10^-8 | 1·10^-8 |

  So the deepest excursion grows only like the logarithm of the number of visits (1,202 by 3·10^7 visits, 1,491 by
  10^8, 1,576 by 2·10^8, 1,582 by 3·10^9): there is no wall, only a steep tail.
* **The live stretch never repeats.** The 160 cells next to the run never take the same value twice in the first
  2·10^6 visits (`c/winrepeat.c`, a hash of the window at every visit). So the machine is
  not a translated cycler with a short period.
* **The trail is random-looking.** Behind the live stretch W is frozen for good. The frozen word has 59% ones and an
  entropy of about half a bit per cell (the conditional entropy given the previous 15 to 21 cells falls from 0.53 to
  0.48 bits; xz packs it to 0.70 bits a cell), with runs of 1s up to 8 cells and of 0s at most 2. No counter or
  substitution word has positive entropy; this one does.
* **Eating has an exponential tail too.** Cells of the run eaten in one excursion, over the first 10^8 visits (an
  excursion can also give back one cell, when a 1 of W next to the foot joins the run: 48.7% of the visits):

  | eaten | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 |
  |---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
  | visits | 19,410,273 | 23,907,202 | 1,738,934 | 2,896,924 | 1,787,036 | 170,365 | 853,731 | 422,149 | 42,843 | 19,420 | 1,199 | 520 | 64 | 9 | 21 | 2 |

  From 8 cells on each 2 more cells are about 10 to 40 times rarer. The record grows slowly with the number of
  visits: 14 by 3·10^7, 15 by 10^8, 17 by 2·10^8, 18 by 3·10^9 (one excursion in 3·10^9).
* **What a halt would need.** The run gains 0.961 cells a visit, so at visit v it holds about 0.96·v cells, and a
  halt needs one excursion to eat all of them (`halts_iff_left_edge`). With the tail above that is a chance of the
  order of 10^(-v/2) at visit v. The machine is, in all likelihood, a non-halter of the same kind as a random walk
  with a strong drift, and a proof would need either a rigid description of the chaotic engine (none is in sight)
  or a bound on what one excursion can eat that holds for every W the machine can make.

## Earlier look: the changes next to the block

Diffing consecutive visits of the left end (state E, `E>0 1^N ...`) **from the right**: the region changes only in
a prefix next to the block, and the far part stays fixed for long stretches, as the low digits of a counter whose
least significant end touches the block. Over the 17,520 visits up to 3·10^8 steps (N grew to 16,663, the region to
1,203 cells), the length of the changed prefix is at least 10 cells in 95% of the visits, at least 20 in 56%, 40 in
31%, 80 in 14%, 160 in 4%, 320 in 0.4% and 640 in 0.01%: deep "carries" are rare, as in a counter. The commonest
moves are a handful of fixed rewrites of the cells next to the block, each with its own change of N, e.g.

    0101010100           -> 010101011             N + 2   (3,337 times)
    01001110100          -> 010011011101          N + 0   (1,378 times)
    0101010111101110100  -> 010101010011011101    N + 2   (764 times)
    010101011110110100   -> 010101011110111101    N + 1   (597 times)

but unlike a counter the deep changes rewrite long stretches into contents that never recur, so the region is not
a fixed-word counter; N drifts (it also loses cells, e.g. 927 -> 919 in one visit at step 1,321,637).

## First look

Growth class **fixed/sqrt** (left: sqrt, exponent 0.512; right: fixed,
exponent 0.025). After 1,000,000,000 steps: 32,607 cells visited (23,545 left of the
start, 343 right), 31,699 ones.

- left, step 969,744,264: `E>0 1^29968 0 1 0 1 0 1 0 1^4 0 1^4 0 1 0 1 0 1^2 0 1 0 1 0 1 0 1^2 0 1 0 1 0 1^2 0 1 0 1 0 1^3 0 1 0^2 1^2 0 1^4 0 1 0^2 1 0 1 0 1 0 1 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1 0 1 0 1^2 0 1 0 1 0 1^2 0 1 0 1 0 1^2 0^2 1 0 1 0 1 0 1 0^2 1^3 0 1 0^2 1 0 1^2 0 1 0 1 0^2 1^2 0 1^3 0 1 0^2 1^2 0 1^3 0 1^3 `
- left, step 985,375,186: `E>0 1^30191 0 1 0 1 0 1 0 1^4 0 1^3 0 1 0 1 0 1 0 1^4 0 1^3 0 1^3 0 1^2 0 1 0^2 1^2 0 1^4 0 1^2 0 1^3 0 1^2 0 1^2 0 1 0^2 1 0 1 0 1 0 1 0 1^2 0^2 1^3 0 1 0^2 1 0 1 0 1 0 1^2 0 1 0 1^2 0^2 1^3 0 1 0 1 0 1 0 1 0^2 1^3 0 1 0^2 1^3 0 1^4 0 1 0^2 1 0 1 0 1 0 1 0 1^2 0^2 1 0 1^2 0 1 0 1 0 1^2 0 1 0 1 0 1 `

## Pages

- [`pages/holdouts/1RB1RA_1LC1RE_---0LD_1LE1LD_0RA0LF_1LF0LB/explainer.html`](../../pages/holdouts/1RB1RA_1LC1RE_---0LD_1LE1LD_0RA0LF_1LF0LB/explainer.html)
- [`pages/holdouts/1RB1RA_1LC1RE_---0LD_1LE1LD_0RA0LF_1LF0LB/proof-status.html`](../../pages/holdouts/1RB1RA_1LC1RE_---0LD_1LE1LD_0RA0LF_1LF0LB/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RA_1LC1RE_---0LD_1LE1LD_0RA0LF_1LF0LB/lean/check.sh
cd holdouts/1RB1RA_1LC1RE_---0LD_1LE1LD_0RA0LF_1LF0LB && python3 py/sibling.py 600                 # tables, and the two runs in step
gcc -O2 -o /tmp/runsim c/runsim.c && /tmp/runsim 1RB1RA_1LC1RE_---0LD_1LE1LD_0RA0LF_1LF0LB D A 1000000 1     # mirrored, D climbs, A returns: 10^6 visits
/tmp/runsim 1RB1RA_0LC0RF_1LD1LC_1RE1LB_---0RA_1RF0RD A C 1000000        # the sibling: same lines, run one longer
gcc -O3 -o /tmp/wstats c/wstats.c && /tmp/wstats 100000000 10000000         # the third look: 10^8 visits, about 12 min
gcc -O3 -o /tmp/winrepeat c/winrepeat.c && /tmp/winrepeat 2000000 160      # no repeat of the 160 cells next to the run
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB1RA_0LC0RF_1LD1LC_1RE1LB_---0RA_1RF0RD`](../1RB1RA_0LC0RF_1LD1LC_1RE1LB_---0RA_1RF0RD/README.md): rename A→C, B→D, C→E, D→A, E→B, F→F and exchange left and right; it is this table started in state D, in a mirror

<!-- end of related machines -->
