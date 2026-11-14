# 1RB1RD_1LC1RA_---1LD_1LE0RA_1LF0LE_0RB0LB

bbchallenge id 44742. One of the six-state holdouts whose halting from blank tape is open (group G07).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RD |
| B | 1LC | 1RA |
| C | --- | 1LD |
| D | 1LE | 0RA |
| E | 1LF | 0LE |
| F | 0RB | 0LB |

## What it does

The mirror image of the mechanism of 1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---0RC (that README has the shared
description and tools). A *visit* is a step at which the head extends the tape to the right in state B; the tape,
read leftwards from the head, is then

    B>0  (10111010)^n  R  0^inf

a block of 8-cell words that grows at every sweep, and a region `R` that is transformed by a map independent of `n`
(up to the phase of the block, which has period 4: the depth a sweep reaches into `R` goes 7, 1, 7, x, with x
varying). The cells of `R` next to the block change at nearly every visit, deeper ones more and more rarely: a
chaotic counter that eats into a reservoir of `1010 1110` words. The tracker calls it "a wide shift-overflow bouncer
counter": the head shifts the block by a word each sweep, and what overflows from the busy stretch moves the
front deeper.

When the front reaches the far end there is an **event**: the whole block becomes new reservoir and `n` restarts.
Events so far, after visits 24 (`R` from 31 to 71 cells), 91 (77 to 213 cells) and **9,305** (229 to 18,659 cells,
at about step 2e8). The earlier README left open what the real machine does near visit 9,300, where the shortened
run stops being valid: the true run shows a third event of the same kind, and no halt.

In the new epoch the front advances about 16.6 cells for each doubling of the number of visits, so the 18,400
cells of reservoir last about **2^1100 visits**. The halting transition is C0, reached only as `0 B>0` (B0 -> 1LC
onto a 0): B must arrive on a 0 with a 0 behind it.

## Status

Open (cryptid-like).

- **Kernel / native_decide:** `lean/Blank.lean`.
- **Computed (trusted):** `resetsim` (in `holdouts/1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---0RC/c/`) with the block cut
  to 10 words agrees with the true run at all of the first 8,000 visits. The true run (`rvis`, same folder, with a
  huge block limit) passes the event after visit 9,305 without a halt; from the true configuration at visit 9,320 the
  shortened run makes 4e6 more visits without a halt or an event. No halt in 1e9 steps.
- **Heuristic:** the front speed and the 2^1100 estimate. Runs with the block cut to 2 to 5 words from the start
  (short reservoirs, frequent events) did not halt in 5e6 visits either, so there is no evidence here that events
  halt, unlike for the three `1RB1RC_1LC0RE_1LD0LB_1RA1LC_*` machines.
- **Not proved:** non-halting, or that halts happen only at the far end (no closed language with plain or parity
  windows up to 8 cells).
- **Open:** the counter's law, and whether an event can halt.

```sh
gcc -O2 -o resetsim holdouts/1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---0RC/c/resetsim.c -I tools/c
./resetsim 1RB1RD_1LC1RA_---1LD_1LE0RA_1LF0LE_0RB0LB R B 10111010 10 1 8000 check
gcc -O2 -o rvis holdouts/1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---0RC/c/rvis.c
# the true run: the visits at which the length of R jumps
./rvis 1RB1RD_1LC1RA_---1LD_1LE0RA_1LF0LE_0RB0LB R B - 10111010 100000 1 1 9400 0 | awk '{d=$4-p; if(d>20||d<-20) print; p=$4}'
# the shortened run from the true configuration at visit 9,320
./rvis 1RB1RD_1LC1RA_---1LD_1LE0RA_1LF0LE_0RB0LB R B - 10111010 10 4 9320 4000000 0 | tail -1
```

## Next steps

This machine is the one of the group for which no halting model run was found: look for an invariant of the far
end (what the tail left by an event looks like, and whether `0 B>0` can ever occur there). A closed tape language
with a feature for the phase of the 8-cell words (period 4) would be the natural thing to try.

## Pages

- [`pages/holdouts/1RB1RD_1LC1RA_---1LD_1LE0RA_1LF0LE_0RB0LB/explainer.html`](../../pages/holdouts/1RB1RD_1LC1RA_---1LD_1LE0RA_1LF0LE_0RB0LB/explainer.html)
- [`pages/holdouts/1RB1RD_1LC1RA_---1LD_1LE0RA_1LF0LE_0RB0LB/proof-status.html`](../../pages/holdouts/1RB1RD_1LC1RA_---1LD_1LE0RA_1LF0LE_0RB0LB/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RD_1LC1RA_---1LD_1LE0RA_1LF0LE_0RB0LB/lean/check.sh
```
