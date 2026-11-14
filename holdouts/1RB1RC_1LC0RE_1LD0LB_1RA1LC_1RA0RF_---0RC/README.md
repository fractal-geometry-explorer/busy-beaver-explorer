# 1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---0RC

bbchallenge id 181043. One of the six-state holdouts whose halting from blank tape is open (group G07).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RC |
| B | 1LC | 0RE |
| C | 1LD | 0LB |
| D | 1RA | 1LC |
| E | 1RA | 0RF |
| F | --- | 0RC |

## What it does

A *visit* is a step at which the head extends the tape to the left in state D. The tape is then

    0^inf  D>0  1^n  R  0^inf

and one sweep later it is the same with `n + 2` and a new region `R`: D0 -> 1RA, the head crosses the block
(`A> 11 -> 01 A>`, 4 steps a pair), works in `R`, and runs home over `1 (01)^(n/2)` in state D, turning it back into
1s. What happens in `R` does not depend on `n` (checked against the direct run, below).

It is easiest to read the tape in pairs aligned to the block: `a` = 01, `b` = 11, `c` = 10, `z` = 00
(`py/pairs.py` prints what each state does to a pair). At a visit `R` is a string of `a` and `b` with a single 1 at
the end. The pairs next to the block change at nearly every visit, deeper ones more and more rarely, like the digits
of a counter; but no independent digits were found: the depth a sweep reaches has a smooth geometric distribution
(each extra 17 cells or so halves the frequency), and the region behaves like a chaotic counter.

Two things can interrupt this, and both need the head at the far end of `R`:

* an **event**: the head comes home in state C instead of D. C turns the block `1 (01)^(n/2)` into `0 (10)^(n/2)`,
  i.e. a fresh reservoir `a^(n/2 + 2)`, the old region becomes a short *tail* behind it, and the block restarts at 2;
* a **halt**: F reads 0. In pairs: `B> b` leaves `z F>`, and `F>` halts on `a` or on a blank pair (it turns `b` into
  `c` and comes back in state C, and `c` into `b`). In every run of the shortened models below, the halt is at
  the blank far end.

Events so far, after visits 5, 9, 29, 137 (`R` = 303 cells) and **167,887**:

| | |
|---|---|
| visit before the event | 167,887, block `1^335,500` |
| head leaves the region in state C | step 84,443,579,279 |
| new region | `a^167,752` + a 305-cell tail = 335,809 cells |

The counter now has to eat 335,504 cells of fresh reservoir at about 17 cells per doubling of the number of visits:
the next event, the next point where a halt is possible, is of the order of **2^19,000 visits** away.

### Why the counter was not decoded

The brief for this pass was to decode the counter (digits, increment, overflow) so that the next event could be
predicted. For the sibling 1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA1RF_---1RD this works: its fresh reservoir is a chain of
independent mod-4 counters, and its run was accelerated exactly through 2.8e36 visits. Here it does not: from a fresh
reservoir (`c/fresh.c`) the search that finds the sibling's counters (a block of cells whose content, at the
sweeps that reach it, is a function of its own previous content) finds nothing here, and the depth statistics are
those of a random walk, not of an odometer.

## Status

Open (cryptid-like: a chaotic counter, and something like a coin toss at each of an unbounded sequence of ever
rarer events).

- **Kernel / native_decide:** `lean/Blank.lean` (halting configurations; 10^4 and 10^7 steps).
- **Computed (trusted):** no halt in 1.1e11 steps (direct C run), which includes the event at visit 167,887.
  `memosim` (in `holdouts/1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---1RE/c/`) reproduces the direct run exactly at the
  level of visits: block, `R` and step count agree at each of 20,000 visits after visit 200, and it finds the event
  at visit 167,887 at the same step with and without its memo table. `c/resetsim.c` (earlier pass) cuts the block to
  40 cells at every visit and agrees with the true `R` at the first 30,000 visits.
- **Heuristic:** the front speed and the 2^19,000 estimate. The small-block model: `c/smallblock.c` runs the real
  machine from a random region with the block cut back to 4 cells at every visit, so that events follow each other
  quickly. All of 2,000 runs (regions of 8 pairs) halt within 8 events, all of 500 (16 pairs) within 13, each time
  with nothing but blank tape right of the head; about a quarter of the far-end contacts halt. If the real events
  behave like these, the machine halts almost surely, after a number of steps far beyond any simulation.
- **Not proved:** that a halt can only happen at the far end. The parity-window closed language that proves this for
  the `..._1RA1RF_---1RD` sibling (`py/fctl.py` there) allows halts in non-blank contexts for this machine with windows
  up to 10 cells. Plain `bbtools.ctl` finds no closed language at all (the pair alignment inside the block is lost).
- **Open:** whether some event halts.

```sh
gcc -O2 -o memosim holdouts/1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---1RE/c/memosim.c
./memosim 1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---0RC 200 20000 check       # against the direct run
./memosim 1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---0RC 200 3000000000 40     # the event at visit 167,887
gcc -O2 -o smallblock holdouts/1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---0RC/c/smallblock.c
./smallblock 1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---0RC 8 2000 1 1 40      # the small-block model
python3 holdouts/1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---0RC/py/pairs.py 1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---0RC
gcc -O2 -o resetsim holdouts/1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---0RC/c/resetsim.c -I tools/c
./resetsim 1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---0RC L D 1 40 2 30000 check
```

## Shared tools (this folder)

| file | what it does |
|---|---|
| `c/resetsim.c` | the run with the block cut to a fixed length at every visit (any machine of the group) |
| `c/rvis.c` | the same with a record per visit: depth reached, length and first cells of `R` |
| `c/fresh.c` | the family from a fresh reservoir: depth and cells per double visit |
| `c/smallblock.c` | the small-block model from random regions: how many events before a halt, and where the halt is |
| `py/pairs.py` | the pair macro table of a machine |
| `../1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---1RE/c/memosim.c` | exact visit-level simulator with step counts |
| `../1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA1RF_---1RD/py/fctl.py` | closed tape languages with a parity feature, and their Lean certificates |

## Next steps

The next event is out of reach of simulation and the counter is not regular. What could still be done: a closed
language richer than parity windows that proves "halts only at the far end" (as for the sibling), and a
description of the tail left by an event precise enough to say which contacts halt.

## Pages

- [`pages/holdouts/1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---0RC/explainer.html`](../../pages/holdouts/1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---0RC/explainer.html)
- [`pages/holdouts/1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---0RC/proof-status.html`](../../pages/holdouts/1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---0RC/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---0RC/lean/check.sh
```
