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

Same first four states as 1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---0RC and the same behavior (see that README): at
each visit of the left end in state D the tape is `0^inf D>0 1^n R 0^inf`, the block grows by two per sweep, and the
region `R` (exactly **209 cells** from visit 92) is transformed by a map independent of `n`: a chaotic counter
next to the block that eats into a reservoir, an old region at the far end. Events (the whole block becomes a new
reservoir) so far: visit 91 only.

The counter's front advances about 11 cells per doubling of the number of visits: 211 of the 250 cells of the
shortened configuration (block of 41 included) after 4.2e6 visits, nothing deeper by 3e7. A halt needs `B>1 1 0`,
which only the far end offers.

## Status

Open.

- **Kernel / native_decide:** `lean/Blank.lean`.
- **Computed (trusted):** `resetsim` (in `holdouts/1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---0RC/c/`) with the block
  cut to 40 cells agrees with the true run at all of the first 6,000 visits (one event, at 91); from visit 100 it runs
  3e7 visits (about 2.6e15 steps of the true machine) with no halt and no event.
- **Heuristic:** the front speed; the next event expected after 1e8-1e9 visits.
- **Open:** whether an event ever halts.

```sh
gcc -O2 -o resetsim holdouts/1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---0RC/c/resetsim.c -I tools/c
./resetsim 1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---1RE L D 1 40 2 6000 check
FRONT=1 T0=100 ./resetsim 1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---1RE L D 1 40 2 30000000
```

## Next steps

Run the shortened machine to the next event (1e8-1e9 visits, hours in C) and see what the event does; it is the
first point where a halt is possible.

## Pages

- [`pages/holdouts/1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---1RE/explainer.html`](../../pages/holdouts/1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---1RE/explainer.html)
- [`pages/holdouts/1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---1RE/proof-status.html`](../../pages/holdouts/1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---1RE/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---1RE/lean/check.sh
```
