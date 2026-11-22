# 1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE---

bbchallenge id 71372. A hierarchy of frozen segments (10)^a 11 (01)^b whose sizes grow level by level (43, 403, 893, …); the active end eats the last run of pairs 01 at a steady rate, 400 pairs per sample, and turns it into a growing reservoir of the word 1010101 at the far left.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LC |
| B | 1LA | 1RF |
| C | 1LD | 0LE |
| D | 1RE | 0RA |
| E | 1LC | 0RD |
| F | 0RE | --- |

## What it does

The tape at step 987,150,465 (66,000 cells):

    C> (01)^4 (1010101)^6123 (01)^7 [(10)^11 11 (01)^43] x9 (10)^11 11 (01)^86
       [(10)^83 11 (01)^403] x6 (10)^83 11 (01)^187 (10)^162 11 (01)^893 (10)^565 11 (01)^893
       (10)^565 11 (01)^1162 (10)^6 11 (01)^3523

The middle is frozen: identical at steps 8.39e8, 9.11e8, 9.87e8. Only the reservoir r (5323, 5723, 6123) and the
last run m (4323, 3923, 3523) change, by 400 per sample, and the tape grows 2000 cells to the left (heuristic).
Segment sizes grow by level (43, 403, ~900): nested levels, each presumably built when a drain runs out. The head
crosses runs of pairs in one go (`lean/Rules.lean`, four rules, kernel).

## Status

Open. Kernel: halting configurations, no halt in 10^4 steps (10^7 native), the four crossing rules, and the walk of the
reflector Q (`lean/Walk.lean`). Halting needs F to read a 1, which happens only as `D> 1 0 1 1`. CTL (K = 2..5) and
NGramCPS (widths 2-8, -H, -U) fail. What happens when the last run is used up is decoded below.

## For later

1. Prove the drain step (one pair per round trip) as a rule with r and m as variables.
2. Done 22 November: the end of a drain starts a rebuild (see below).
3. Prove the collisions of Q (with a separator, a mover reaching the right end, a scar) with `bbtools.symtm`, and write
   the rebuild as an exact list-to-list map; then look for an invariant of the lists that keeps `D> 1 0 1 1` out.

## Reproduce

```sh
./tmrun 1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE--- 1000000000 records 100000000 | awk 'NR%2000==0' | tail -3
. /etc/profile.d/lean.sh && holdouts/1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE---/lean/check.sh
```

## Accelerated run (13 November 2026)

Observed, not proved: the accelerated simulator `rsim.py` ran 7.30x10^14 steps from blank tape without reaching a halting transition. Its tape, state and head position were equal to those of a plain C simulator at 6 checkpoints, the last at 1.75x10^10 steps. Of these steps, the part after the last checkpoint rests on the simulator alone, including 1,080 trip-level jumps: a jump applies many identical round trips at once after seeing the same tape shape recur with constant count changes, which is validated against direct simulation but not proved.

```sh
python3 holdouts/1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA1RF_0LC---/py/rsim_screen.py 1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE--- 400
```

## When the last run is used up (22 November 2026)

**Short answer.** A rebuild, not a halt, every time it has been watched: 5 drain ends in direct simulation (to
2.2·10^9 steps) and 3 more in the accelerated run (to 6.0·10^14). The rebuild is a particle system, decoded below.
Whether some rebuild can end in a halt is still open.

**The tape as a list.** Read from the left, the tape is `(10)^3` blocks (the reservoir, the words `1010101`) and
then a list of blocks `(10)^n` separated by single `1`s, `10, n_2, n_3, ..., m`. In the drain each round trip moves one
pair from the last block `m` to the reservoir. When `m` reaches 1, the next trip does not come back to the left end.

**What follows: a reflector walks left and triples what it passes.** The head now bounces between the right end of
the tape and a reflector `Q`, one extra cell in a background of pairs (`L (01)^c 0 (01)^a E>` or the same with an
extra `1`):

* one bounce moves Q two cells left and the right end two cells right (`lean/Walk.lean`: `bounce0`, `bounce1`,
  `bounce2`, and `walk` for k double bounces, kernel);
* when Q passes a separator of the list (`001100` in the phase the head leaves there), the separator turns into a
  *mover* `11` that the head carries four cells to the right on every bounce (observed);
* so stuff Q has passed moves away from it at 4 cells per bounce while Q moves 2: the part of the list Q passes comes
  out stretched three times. Block by block, `n` becomes `3n` (n even) or `3n - 4`, `3n + 4` (n odd, alternating),
  for example `(11 43)` becomes `(29 133)` and then `(83 403)`, and the reservoir's `3`s become `(5 13)` or `(19 35)`;
* the walk ends when the first mover reaches the right end (which grows only 2 cells per bounce): on the next
  bounce Q is left behind as a *scar*, a stationary `00` or `11`, and a new Q starts near the right end;
* a later Q passes a `00` scar (it becomes a mover) and stops at a `11` scar. In the event at 1.4·10^8 the walks
  stop at 10631, 15634 and again at 10631; in the event at 1.79·10^9 at 54482, 54321 and again at 54321.

When the walks are over the head runs back to the left end and the next drain starts with a new last block.
`c/sweeps.c` prints the turning points of the head; during a rebuild its left turns are the positions of Q.
`c/parts.c` prints, at those times, where the tape has `00` or `11`: these are exactly the particles.

**Three kinds of rebuild have been seen.**

| drain ends at step | last blocks before | after | source |
|---|---|---|---|
| 9,061 | `5 5 6 1` | `16 11 6 111` | direct |
| 272,814 | `16 11 6 1`, reservoir 128 | `10 (11 43)^16 11 19 18 (101 61)^2 130 541 269 821 2335`, reservoir 83 | direct |
| 142,359,375 | `... 130 541 269 821 1` | `... (11 43)^9 11 86 (83 403)^6 83 187 162 (893 565)^2 1162 6 7228` | direct |
| 1,793,526,413 | `... (893 565)^2 1162 6 1` | `... (893 565)^2 1552` | direct |
| 2,230,168,743 | whole list, reservoir 11,198 | `10 (5 13)^388 5 37 (19 35)^5209 19 90 (107 379)^9 107 774 739 24448 6659 5707 81162 (19709 98389)^2 19709 158069 468864`, reservoir about 0, at 1.79·10^12 | accelerated |
| 6.48·10^12 | `... 81162 (19709 98389)^2 19709 158069 1` | `... 5707 563005 177397 4764477 4737114`, at 1.26·10^14 | accelerated |
| 6.05·10^14 | `... 563005 177397 4764477 1`, reservoir 5,205,977 | a rebuild that reaches back to `(107 379)^9`; not finished at 7.3·10^14 | accelerated |

A *short* rebuild only touches the last few blocks (1.79·10^9: `1162 6 1` becomes `1552` in 562,000 steps). A
*partial* one re-makes the right part of the list (1.4·10^8 and 6.5·10^12). A *full* one reaches the left end and
turns the reservoir itself into blocks, so a new reservoir starts from nothing (2.7·10^5 partly, 2.2·10^9
completely: 11,198 copies of `3` became `(5 13)^388 5 37 (19 35)^5209`). So the "frozen levels" of the 13 November
picture are made by rebuilds: each block value is a reservoir `3` or an older block tripled a number of times.

**Where a halt could come from.** The machine halts only when F reads a 1. B is entered only from A reading 0
(moving right, writing 1), so B reading 0 goes back onto that 1; F is therefore entered only through `A>0 1 x`, and
the machine halts exactly when `x = 1`. A is entered from B (onto the 1 just written) or from D reading 1, and D
from C (which writes the 1 the next A reads) or from E reading 1. So **every halt is the head in D, moving right,
on `1 0 1 1`**: a block of a single pair `01` between two extra `1`s, crossed by D. In 3·10^9 steps F is entered
63,295,957 times, always on a 0, in 22 different 17-cell windows (`c/fwatch.c`). The drains never meet this word;
the place to look is the rebuilds, where the last run is down to one pair and Q, scars and movers sit close together.

**Open.** An exact list-to-list map for a rebuild (the offsets where Q is born and where scars sit are not yet
written down as rules), and with it a proof that no rebuild produces `D> 1 0 1 1`. The Lean walk theorem covers Q
in a clean background; the collisions with separators, movers and scars are only observed. The accelerated rows of
the table rest on `rsim`'s jumps (not proved); in the middle of the long rebuild, at step 107,877,479,194, rsim's
tape and state equal those of a plain C simulator (822,161 cells; `rsim ... dump 1e11` against a direct run).

```sh
gcc -O2 -o blkev holdouts/1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE---/c/blkev.c && ./blkev 1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE--- 3000000000 | grep -v mon
python3 holdouts/1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE---/py/rsim_events.py 2e14 > ev.txt && python3 holdouts/1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE---/py/drain_ends.py ev.txt
gcc -O2 -o sweeps holdouts/1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE---/c/sweeps.c && ./sweeps 1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE--- 142000000 407100000 200
gcc -O2 -o parts holdouts/1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE---/c/parts.c && ./parts 1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE--- $(./sweeps 1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE--- 1793600000 1793910000 40 | awk '$4=="min"{print $1}' | paste -sd,) 54200
gcc -O2 -o fwatch holdouts/1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE---/c/fwatch.c && ./fwatch 1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE--- 3000000000
python3 holdouts/1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE---/py/gen_walk.py     # writes lean/WalkRules.lean
```

## Pages

- [`pages/holdouts/1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE---/explainer.html`](../../pages/holdouts/1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE---/explainer.html)
- [`pages/holdouts/1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE---/proof-status.html`](../../pages/holdouts/1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE---/proof-status.html)

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0LC_1RC0RA_1LA0LD_1LE0RB_1RD1LF_0LA---`](../1RB0LC_1RC0RA_1LA0LD_1LE0RB_1RD1LF_0LA---/README.md): rename A→D, B→E, C→B, D→C, E→A, F→F and exchange left and right; it is this table started in state E, in a mirror
- [`1RB0RC_1LC0LD_1RA0LB_1LE0RA_1RD1LF_0LC---`](../1RB0RC_1LC0LD_1RA0LB_1LE0RA_1RD1LF_0LC---/README.md): rename A→D, B→E, C→A, D→B, E→C, F→F and exchange left and right; it is this table started in state C, in a mirror
- [`1RB0RD_1LC0RA_1LA0LB_1RE0LC_1LD1RF_0RB---`](../1RB0RD_1LC0RA_1LA0LB_1RE0LC_1LD1RF_0RB---/README.md): rename A→D, B→E, C→C, D→A, E→B, F→F; it is this table started in state D
- [`1RB1LC_1LA0RE_0LD---_1RE0LF_1RF0RD_1LD0LB`](../1RB1LC_1LA0RE_0LD---_1RE0LF_1RF0RD_1LD0LB/README.md): rename A→B, B→A, C→E, D→F, E→D, F→C and exchange left and right; it is this table started in state B, in a mirror

<!-- end of related machines -->
