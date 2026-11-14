# 1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---1RE

bbchallenge id 51709. One of the six-state holdouts whose halting from blank tape is open (group G07).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RC |
| B | 1LC | 0RE |
| C | 1LD | 0LB |
| D | 1RA | 1LC |
| E | 1RA | 0RF |
| F | --- | 1RE |

## What it does

Same first four states as 1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---0RC and the same mechanism (that README has the
shared description and tools). A *visit* is a step at which the head extends the tape to the left in state D; the
tape is then

    0^inf  D>0  1^n  R  0^inf

One sweep later it is the same with `n + 2` and a new region `R` that does not depend on `n`: the head crosses the
block (`A> 11 -> 01 A>`), works in `R`, and comes home. Read in pairs aligned to the block (`a` = 01, `b` = 11), `R` is
a string of `a` and `b` with a single 1 at the end; the cells next to the block change at nearly every visit, deeper
ones more and more rarely (a chaotic counter: no independent digits were found, the depth reached by a sweep has a
smooth geometric distribution).

Two things can end this routine, and both need the head at the far end of `R`:

* an **event**: the head comes home in state C instead of D. Then the whole block becomes a fresh reservoir: the new
  region is `a^(n/2 + 2)` followed by a tail made from the old region (209 cells at the last event), and the block restarts at 2;
* a **halt**: F reads 0. In pairs, `B> b` leaves `F>`, which runs right over `b`s and halts on the first `a` or blank
  pair. Inside the tape this has never been seen; in every model run below the halt is at the blank far end.

Events so far, after visits 3, 5, 7, 15, 91 (`R` = 209 cells) and **1,675,675,235**:

| | |
|---|---|
| visit before the event | 1,675,675,235, block `1^3,351,350,288` |
| head leaves the region in state C | step 8,423,661,719,239,282,477 |
| next visit (block `1^2`) | step 8,423,661,722,590,632,760 |
| new region | `a^1,675,675,146` + a 209-cell tail (ending `...bbbbba 1`) = 3,351,350,501 cells |

So the machine does not halt in its first 8.4e18 steps, and the event that the earlier README called "the first point
where it could halt" passed without a halt. The counter now has a reservoir of 3.35e9 cells to eat; at the measured
rate (the deepest cell reached advances 6.5 to 11 cells each time the number of visits doubles) the next event is
of the order of 2^(3e8) visits away. It cannot be simulated, and the counter is not regular enough to jump.

## Status

Open (cryptid-like: a chaotic counter, and a coin toss at each of an unbounded sequence of ever rarer events).

- **Kernel / native_decide:** `lean/Blank.lean` (halting configurations; no halt in 10^4 / 10^7 steps).
- **Computed (trusted):** `c/memosim.c`, an exact visit-level simulator (a window of 8 block cells and `R`, the rest of
  the block by formula, a memo table on the first P cells of `R`). Validation: `check` mode compares `n`, `R` and the
  step count with the direct run at each of 20,000 visits (0 mismatches); the run is the same for every P (P = 0, 10,
  20, 36, 52 agree at 3e6 visits, step 27,000,426,790,621; P = 30 and P = 52 give the same event visit, window and
  step). An independent earlier program found the same event visit.
- **Heuristic:** with the block kept at 4 cells and a random start (`smallblock`), events follow each other quickly:
  all of 2,000 runs halt within 6 events (region of 8 pairs), all of 500 within 11 (16 pairs), each time with nothing
  but blank tape right of the head. With the last 21 or 41 cells of the true tail (`c/tail_event6.txt`) at the far
  end of a random region of 26 pairs, 123 and 132 of 400 runs halt at the first far-end contact (about a third). If the true events behave like these, the machine halts almost surely, but only
  after a number of steps far beyond any simulation.
- **Not proved:** that a halt can only happen at the far end. The parity-window closed tape language that proves this
  for 1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA1RF_---1RD (`py/fctl.py` there) allows halts in non-blank contexts for this
  machine up to windows of 10 cells.
- **Open:** whether some event halts.

```sh
gcc -O2 -o memosim holdouts/1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---1RE/c/memosim.c
./memosim 1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---1RE 100 20000 check        # against the direct run
./memosim 1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---1RE 100 3000000000 30      # to the event (tens of minutes)
gcc -O2 -o smallblock holdouts/1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---0RC/c/smallblock.c
./smallblock 1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---1RE 8 2000 1 1 40
T=$(cat holdouts/1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---1RE/c/tail_event6.txt)
TAIL=${T: -41} ./smallblock 1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---1RE 26 400 5 1 1 4   # the true far end
```

## Next steps

A decision needs either the counter's law (to say which far-end contacts halt) or luck at an event; the next event
is out of reach. A proof that halts happen only at the far end (a closed language with a richer feature than parity)
would at least make the picture rigorous.

## Pages

- [`pages/holdouts/1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---1RE/explainer.html`](../../pages/holdouts/1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---1RE/explainer.html)
- [`pages/holdouts/1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---1RE/proof-status.html`](../../pages/holdouts/1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---1RE/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---1RE/lean/check.sh
```
