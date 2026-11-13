# 1RB0LC_1RC0RC_1LD0RB_1LA0LE_1LD1LF_1LD---

bbchallenge id 83065. One of the six-state holdouts whose halting from blank tape is open (group G10). Family: **binary-counter-like bouncer with sliding digit markers (chaotic)**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LC |
| B | 1RC | 0RC |
| C | 1LD | 0RB |
| D | 1LA | 0LE |
| E | 1LD | 1LF |
| F | 1LD | --- |

## What it does

The tape is a list of segments `(10)^x M (10)^y 1` with a marker `M = 0` or `000`. On each sweep the rightmost segments toggle their markers like the low digits of a binary counter; each toggle moves material by one pair (x+1, y-1, or the marker changes form). The right end grows by 2 pairs per sweep, the left end only 69 cells in 10^9 steps (bursts of 3). Segment sizes cluster near 2^k - 1 (511, 1023, 2047, ...). When a segment's fuel y runs out the segments merge or split, and the run becomes irregular.

```
successive sweeps, right part of the tape (a = 10):
step 600,009,840  ... a^771 0^3 a^502 1 a^1031 0^3 a^2542 1 a^1039 0^3 a^30 1^2
step 600,028,604  ... a^771 0^3 a^502 1 a^1032 0   a^2541 1 a^1040 0^3 a^32 1^2
step 600,057,656  ... a^772 0   a^501 1 a^1032 0^3 a^2540 1 a^1041 0^3 a^34 1^2
step 600,076,460  ... a^772 0   a^501 1 a^1033 0   a^2539 1 a^1042 0^3 a^36 1^2
```

## Halting

The only halting transition is F1. `bbtools.ctl` finds closed tape languages (windows of 2 to 6 cells) that cover the run but still allow halts, with only a local constraint near the head: at K = 6 the head cell and the cells to its right read `110101` or `110110`.

## Status

**Open.** Lean: only the generated `lean/Blank.lean` (halting configurations; no halt in 10^4 steps by the kernel, 10^7 by `native_decide`).
Deciders tried without success: `bbtools.ctl` with windows K = 2..6 (no closed language without halts), `ngramcps`
with widths 2..6, plain and with `-H 2`, `-H 3`, `-U`.

## For later

- Write the per-sweep rule as an operation on the segment list (marker toggles = binary increment, with the
  fuel y of each segment), check it for many sweeps, then find what happens when a fuel runs out.
- Look at which marker configuration would put F on a 1 followed by `10101`/`10110`.

## Pages

- [`pages/holdouts/1RB0LC_1RC0RC_1LD0RB_1LA0LE_1LD1LF_1LD---/explainer.html`](../../pages/holdouts/1RB0LC_1RC0RC_1LD0RB_1LA0LE_1LD1LF_1LD---/explainer.html)
- [`pages/holdouts/1RB0LC_1RC0RC_1LD0RB_1LA0LE_1LD1LF_1LD---/proof-status.html`](../../pages/holdouts/1RB0LC_1RC0RC_1LD0RB_1LA0LE_1LD1LF_1LD---/proof-status.html)

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0RE_1LC0RD_1LD0LD_1RA0LC_1RA1RF_1RA---`](../1RB0RE_1LC0RD_1LD0LD_1RA0LC_1RA1RF_1RA---/README.md): rename A→B, B→C, C→D, D→A, E→E, F→F and exchange left and right; it is this table started in state D, in a mirror

<!-- end of related machines -->
