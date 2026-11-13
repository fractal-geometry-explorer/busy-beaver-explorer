# 1RB0RA_1LC0RC_1LF0RD_1RA1LE_0LC---_1LD0LA

bbchallenge id 26127. One of the six-state holdouts whose halting from blank tape is open (group G10). Family: **bouncer with a multi-digit counter of 011 blocks (chaotic)**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RA |
| B | 1LC | 0RC |
| C | 1LF | 0RD |
| D | 1RA | 1LE |
| E | 0LC | --- |
| F | 1LD | 0LA |

## What it does

Read from the left end the tape is `1 1` and then blocks of `a = 011` separated by `1`, `0 1` or `1 1 1`. The first separator cycles through four forms, one per sweep; at the end of a cycle it changes the next separator (a carry), and so on: a counter with many digits, each change moving an `a` between neighbouring blocks. The first block grows by about one `a` every two sweeps; block lengths fall off roughly geometrically to the right (12466, 3127, 820, ...).

```
successive sweeps at the left end (a = 011):
step 20,004,745  F 1^2 a^1749 1 a^4 0 1 a^448 1^3 a^4 1 a^21 0 1 a^3 1 a^82 ...
step 20,022,301  F 1^2 a^1750 1 a^5 1^3 a^447 1^3 a^4 1 a^21 0 1 a^3 1 a^82 ...
step 20,039,825  F 1^2 a^1751 0 1 a^5 1^3 a^447 1^3 a^4 1 a^21 0 1 a^3 1 a^82 ...
step 20,057,363  F 1^2 a^1753 1^3 a^4 1^3 a^447 1^3 a^4 1 a^21 0 1 a^3 1 a^82 ...
step 20,098,031  F 1^2 a^1753 1 a^4 1 a^450 1^3 a^3 1 a^21 0 1 a^4 1^3 a^81 ...
```

## Halting

The only halting transition is E1. `bbtools.ctl` finds closed tape languages (windows of 2 to 6 cells) that cover the run but still allow halts, with only a local constraint near the head: at K = 6 the head cell and the cells to its right read `111101`.

## Status

**Open.** Lean: only the generated `lean/Blank.lean` (halting configurations; no halt in 10^4 steps by the kernel, 10^7 by `native_decide`).
Deciders tried without success: `bbtools.ctl` with windows K = 2..6 (no closed language without halts), `ngramcps`
with widths 2..6, plain and with `-H 2`, `-H 3`, `-U`.

## For later

- Write the digit cycle of the separators (four forms, carries) and the transfer of `a`s as an explicit counter,
  check it for many sweeps, then ask whether E can ever meet `111101`.
- Same family as 1RB1LD_1LC---_1RE0LD_1LC1LD_1RF0RE_1RA0RC in this batch.

## Pages

- [`pages/holdouts/1RB0RA_1LC0RC_1LF0RD_1RA1LE_0LC---_1LD0LA/explainer.html`](../../pages/holdouts/1RB0RA_1LC0RC_1LF0RD_1RA1LE_0LC---_1LD0LA/explainer.html)
- [`pages/holdouts/1RB0RA_1LC0RC_1LF0RD_1RA1LE_0LC---_1LD0LA/proof-status.html`](../../pages/holdouts/1RB0RA_1LC0RC_1LF0RD_1RA1LE_0LC---_1LD0LA/proof-status.html)
