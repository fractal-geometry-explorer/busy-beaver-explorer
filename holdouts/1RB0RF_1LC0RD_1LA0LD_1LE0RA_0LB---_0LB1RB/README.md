# 1RB0RF_1LC0RD_1LA0LD_1LE0RA_0LB---_0LB1RB

bbchallenge id 87181. One of the six-state holdouts. Analyzed by hand (group G02), partly: the sweep is understood, the macro rule is not.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RF |
| B | 1LC | 0RD |
| C | 1LA | 0LD |
| D | 1LE | 0RA |
| E | 0LB | --- |
| F | 0LB | 1RB |

## What it does (observed)

Almost all of the tape is left of the start and is made of the word x = `10111110`. At step 2,266,312,097 the
left part reads (from the far left) `1^2 0 1^3 0 x 1^13 0 x^218 1^5 0 x^206 (10)^2 x^205 (10)^2 x^209 ...`:
112 segments x^k, lengths falling from ~218 to 1 toward the start, separated mostly by `1010` or `(10)^4` and a
few longer markers (`1 0 1^9 0`, `1 0 1^13 0`). Right of the start is a small slowly growing structure (35 cells
after 7.8·10^8 steps; the triage fit calls it logarithmic).

One sweep (Lean, `lean/Rules.lean`):

* `left_end`:  `0^inf A> 0 1 x^(n+1) R  ->  0^inf 1 0 0 1 y^n 0 0 0 F> 1 1 0 R`  (26n + 7 steps), y = `10011001`;
* `right_pass`: `L 0 0 0 F> 1 1 0 x^n R  ->  L y^n 0 0 0 F> 1 1 0 R`  (26n steps);
* `left_pass`:  `L y^n B> 0 R  ->  L B> 0 (01111101)^n R`  (20n steps).

At the left end, `A> 0 1 x^k` (after `[A1] 1^2 0 1^3 0 x^(k-1)`) recurs one sweep later with k + 1: the leading
segment gains one word per sweep (about 148,000 steps a sweep at width 50,000).

## Halting

Only E1 halts. `bbtools.ctl` with K = 3, 4, 5 allows a halt (E reading 1 before `110`, `1101`, `11010`).
n-gram CPS (widths 3..7) fails. C simulator: no halt in 10^9 steps. `bbtools.cycles` (K = 2) makes little
progress (the separators break the regular regimes it accelerates). Open.

## Notes for later

* Decode the separators: how a marker between two segments changes when a sweep passes (they look like digits
  being carried), when the leading segment is cut off (~218 words), and how the right-end structure is fed.
* With that, write the macro configuration as a list of (segment length, marker) and find its rule; the halting
  question should then reduce to the right-end counter.

## Accelerated run (13 November 2026)

Observed, not proved: the accelerated simulator `rsim.py` ran 1.10x10^10 steps from blank tape without reaching a halting transition. Its tape, state and head position were equal to those of a plain C simulator at 6 checkpoints, the last at 1.00x10^10 steps. No trip-level jump was used in this run, only the shift rules over repeated words (exact by induction, but the program is not verified).

```sh
python3 holdouts/1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA1RF_0LC---/py/rsim_screen.py 1RB0RF_1LC0RD_1LA0LD_1LE0RA_0LB---_0LB1RB 400
```

## Pages

- [`pages/holdouts/1RB0RF_1LC0RD_1LA0LD_1LE0RA_0LB---_0LB1RB/explainer.html`](../../pages/holdouts/1RB0RF_1LC0RD_1LA0LD_1LE0RA_0LB---_0LB1RB/explainer.html)
- [`pages/holdouts/1RB0RF_1LC0RD_1LA0LD_1LE0RA_0LB---_0LB1RB/proof-status.html`](../../pages/holdouts/1RB0RF_1LC0RD_1LA0LD_1LE0RA_0LB---_0LB1RB/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RF_1LC0RD_1LA0LD_1LE0RA_0LB---_0LB1RB/lean/check.sh
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0LE_0RC---_1RD0LA_1RE0RA_1LC0LF_0RC1LC`](../1RB0LE_0RC---_1RD0LA_1RE0RA_1LC0LF_0RC1LC/README.md): rename A→E, B→C, C→D, D→A, E→B, F→F and exchange left and right; it is this table started in state D, in a mirror

<!-- end of related machines -->
