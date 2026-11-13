# 1RB1RA_1LC0LF_1RA1LD_1LB1LE_1LC0LC_---0RA

bbchallenge id 28031. One of the six-state holdouts whose halting from blank tape is open (group G10). Family: **bouncer over 9-cell blocks with irregular defects (chaotic)**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RA |
| B | 1LC | 0LF |
| C | 1RA | 1LD |
| D | 1LB | 1LE |
| E | 1LC | 0LC |
| F | --- | 0RA |

## What it does

Near the left end the tape is a long stretch of the 9-cell word `e = 011111011`, which grows steadily, followed by a region of short pieces (`1^2 0`, `1^3 d` with `d = 111110110`, ...) that changes irregularly from sample to sample. Near the right end the pattern is `1^7 0^2` repeated. Both ends grow.

```
the tape at the left end (e = 011111011, d = 111110110):
step 100,085,416  C 1 e^735 1^3 0 1^2 0 1^2 0 1^2 0 1^2 0 ... 1^8 e 1^3 0 1^21 d 1^2 0 1^2 0 1^2 e ...
step 150,115,972  C 1 e^1132 0 1^2 0 1^8 0 1^8 e 1^9 e 0 1^2 0 1^2 0 1^2 e 1^6 e 1^9 e ...
step 200,296,075  C 1 e^1334 1^3 0 1^2 0 1^2 0 1^6 d^2 1^6 d 1^3 d 1^2 0 1^2 e 1^6 e ...
```

## Halting

The only halting transition is F0. `bbtools.ctl` finds closed tape languages (windows of 2 to 6 cells) that cover the run but still allow halts, with only a local constraint near the head: at K = 6 the head cell and the cells to its right read `001101` or `001111`.

## Status

**Open.** Lean: only the generated `lean/Blank.lean` (halting configurations; no halt in 10^4 steps by the kernel, 10^7 by `native_decide`).
Deciders tried without success: `bbtools.ctl` with windows K = 2..6 (no closed language without halts), `ngramcps`
with widths 2..6, plain and with `-H 2`, `-H 3`, `-U`.

## For later

- Find a word set that makes the defect region regular (try `bbtools.explore tokens` with the 9-cell words and
  their rotations), then look for a rule at the left-end samples.

## Pages

- [`pages/holdouts/1RB1RA_1LC0LF_1RA1LD_1LB1LE_1LC0LC_---0RA/explainer.html`](../../pages/holdouts/1RB1RA_1LC0LF_1RA1LD_1LB1LE_1LC0LC_---0RA/explainer.html)
- [`pages/holdouts/1RB1RA_1LC0LF_1RA1LD_1LB1LE_1LC0LC_---0RA/proof-status.html`](../../pages/holdouts/1RB1RA_1LC0LF_1RA1LD_1LB1LE_1LC0LC_---0RA/proof-status.html)
