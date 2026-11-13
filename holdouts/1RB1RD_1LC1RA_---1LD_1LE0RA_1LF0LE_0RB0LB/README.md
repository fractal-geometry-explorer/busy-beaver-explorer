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

The mirror image of the mechanism of 1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---0RC (see that README). At each visit of
the right end in state B the tape, read leftwards from the head, is `B>0 (10111010)^n R`: a block of 8-cell words
that grows each sweep, and a region `R` (213 cells after the event at visit 91) transformed by a map independent of
`n`, with a busy chaotic part next to the block.

The halting transition is C0, reached only as `0 B>0` (B0 -> 1LC onto a 0).

## Status

Open.

- **Kernel / native_decide:** `lean/Blank.lean`.
- **Computed (trusted):** `resetsim` (in `holdouts/1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---0RC/c/`) with the block cut
  to 10 words agrees with the true run at all of the first 8,000 visits (one event, at 91). No halt in 1e9 steps.
- **Open:** in the shortened run, `R` starts absorbing block words near visit 9,300; that event depends on the block
  length, so the shortened run is not valid past it, and what the real machine does there is not yet known.

```sh
gcc -O2 -o resetsim holdouts/1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---0RC/c/resetsim.c -I tools/c
./resetsim 1RB1RD_1LC1RA_---1LD_1LE0RA_1LF0LE_0RB0LB R B 10111010 10 1 8000 check
```

## Next steps

Run the true machine past visit 9,300 (about 2e8 steps) with `check` to see what that event does to the real block,
then continue with the shortened run from the true configuration (`T0`).

## Pages

- [`pages/holdouts/1RB1RD_1LC1RA_---1LD_1LE0RA_1LF0LE_0RB0LB/explainer.html`](../../pages/holdouts/1RB1RD_1LC1RA_---1LD_1LE0RA_1LF0LE_0RB0LB/explainer.html)
- [`pages/holdouts/1RB1RD_1LC1RA_---1LD_1LE0RA_1LF0LE_0RB0LB/proof-status.html`](../../pages/holdouts/1RB1RD_1LC1RA_---1LD_1LE0RA_1LF0LE_0RB0LB/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RD_1LC1RA_---1LD_1LE0RA_1LF0LE_0RB0LB/lean/check.sh
```
