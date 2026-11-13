# 1RB---_0RC1RC_1RD0LE_1RE0RB_1LF0RA_1LC1LF

bbchallenge id 168752. One of the six-state holdouts whose halting from blank tape is open (group G10). Family: **bouncer over 0111 blocks with a slowly consumed left side (chaotic)**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | --- |
| B | 0RC | 1RC |
| C | 1RD | 0LE |
| D | 1RE | 0RB |
| E | 1LF | 0RA |
| F | 1LC | 1LF |

## What it does

At the left end the tape reads as runs of the word `a = 0111`, solid runs of 1s and short junctions. Each visit to the left end takes two a's from the first run (and the last run grows by four), so between rewrites the left part is a counter; when the first run is used up the junctions merge and new runs form, with no visible pattern. The right end grows by exactly 3 cells per sweep (bursts of 3 new cells every ~2·width steps); the left end moves out 248 times in 10^9 steps, by 2 to 6 cells.

```
the tape at successive visits to the left end (a = 0111):
step 195,355,840  F a 1^4 a^66 1^10 a^4 1^1099 a^2 1^4 a^2 1^5 a^1472 1^3 a^2 1^5 a^1540
step 195,568,274  F a 1^4 a^64 1^10 a^4 1^1099 a^2 1^4 a^2 1^5 a^1472 1^3 a^2 1^5 a^1544
step 195,780,828  F a 1^4 a^62 1^10 a^4 1^1099 a^2 1^4 a^2 1^5 a^1472 1^3 a^2 1^5 a^1548
```

## Halting

The machine halts on A reading 1 (A1 undefined). `bbtools.ctl` finds closed tape languages (windows of 2 to 6 cells) that cover the run but still allow halts, with only a local constraint near the head: at K = 6 the cells left of the head read (outward) `011001`, `011010`, `011101` or `011110`. Nothing confines a halt to an edge.

## Status

**Open.** Lean: only the generated `lean/Blank.lean` (halting configurations; no halt in 10^4 steps by the kernel, 10^7 by `native_decide`).
Deciders tried without success: `bbtools.ctl` with windows K = 2..6 (no closed language without halts), `ngramcps`
with widths 2..6, plain and with `-H 2`, `-H 3`, `-U`.

## For later

- Find the rewrite rules at the left end as maps on the block list (run lengths of `a` and of `1`), as was done
  for 1RB1RF_1LC0LB; the per-visit rule (two a's off the first run) is the place to start, with `bbtools.cycles` at
  sample points at the left end.

## Pages

- [`pages/holdouts/1RB---_0RC1RC_1RD0LE_1RE0RB_1LF0RA_1LC1LF/explainer.html`](../../pages/holdouts/1RB---_0RC1RC_1RD0LE_1RE0RB_1LF0RA_1LC1LF/explainer.html)
- [`pages/holdouts/1RB---_0RC1RC_1RD0LE_1RE0RB_1LF0RA_1LC1LF/proof-status.html`](../../pages/holdouts/1RB---_0RC1RC_1RD0LE_1RE0RB_1LF0RA_1LC1LF/proof-status.html)
