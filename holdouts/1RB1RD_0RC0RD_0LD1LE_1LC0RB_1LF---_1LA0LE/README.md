# 1RB1RD_0RC0RD_0LD1LE_1LC0RB_1LF---_1LA0LE

bbchallenge id 161169. One of the six-state holdouts whose halting from blank tape is open (group G10). Family: **two-block bouncer with an irregular exchange (chaotic)**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RD |
| B | 0RC | 0RD |
| C | 0LD | 1LE |
| D | 1LC | 0RB |
| E | 1LF | --- |
| F | 1LA | 0LE |

## What it does

At the moments the head is at the right end in state B the tape is `(10)^x 0^y` (sometimes with a marker `10 000` or a final 1), the width `2x + y` growing by 4 per event. Between events x moves irregularly: up by one when y is close to 2x, otherwise by jumps of either sign; no affine map (x' = ax + bW + c) fits more than a fifth of the events. The visited tape grows very slowly (2,593 cells after 10^9 steps).

```
successive events at the right end (a = 10):
step 3,634,088  B a^97 0^196
step 3,769,137  B a^98 0^198
step 3,883,262  B a^123 0^152
step 4,023,531  B a^100 0^202
step 4,112,854  B a^150 0^106
step 4,252,471  B a^139 0^132
```

## Halting

The only halting transition is E1. `bbtools.ctl` finds closed tape languages (windows of 2 to 6 cells) that cover the run but still allow halts, with only a local constraint near the head: at K = 6 the head cell and the cells to its right read one of `101010`, `101011`, `101110`, `111010`, `111011`.

## Status

**Open.** Lean: only the generated `lean/Blank.lean` (halting configurations; no halt in 10^4 steps by the kernel, 10^7 by `native_decide`).
Deciders tried without success: `bbtools.ctl` with windows K = 2..6 (no closed language without halts), `ngramcps`
with widths 2..6, plain and with `-H 2`, `-H 3`, `-U`.

## For later

- The two-block form suggests a map on (x, W): record (x, W) at every event for a long run and look for a rule mod
  small numbers, or in terms of the head's internal pass (the marker `10 000` travels through the 0 block).

## Pages

- [`pages/holdouts/1RB1RD_0RC0RD_0LD1LE_1LC0RB_1LF---_1LA0LE/explainer.html`](../../pages/holdouts/1RB1RD_0RC0RD_0LD1LE_1LC0RB_1LF---_1LA0LE/explainer.html)
- [`pages/holdouts/1RB1RD_0RC0RD_0LD1LE_1LC0RB_1LF---_1LA0LE/proof-status.html`](../../pages/holdouts/1RB1RD_0RC0RD_0LD1LE_1LC0RB_1LF---_1LA0LE/proof-status.html)
