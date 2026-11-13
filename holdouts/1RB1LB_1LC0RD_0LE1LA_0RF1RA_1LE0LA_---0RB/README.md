# 1RB1LB_1LC0RD_0LE1LA_0RF1RA_1LE0LA_---0RB

bbchallenge id 696. One of the six-state holdouts. Analyzed by hand (group G02), partly: shift rules proved, macro rule not found.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LB |
| B | 1LC | 0RD |
| C | 0LE | 1LA |
| D | 0RF | 1RA |
| E | 1LE | 0LA |
| F | --- | 0RB |

## What it does (observed)

The left side (31,721 cells after 10^9 steps) is runs of 1s of lengths 2 mod 3 separated by single 0s, i.e. a
string over the 3-cell words `110` and `111`; right of the start are ~200 cells of `11` and runs of 0s. Every sweep
rewrites the whole string (successive left-end visits show unrelated strings, not shifts) and makes it one or two
cells longer (width 2,366 -> 2,395 over 29 visits near step 3·10^6). This looks like arithmetic on a number written
on the tape, one operation per sweep, with a counter at the right.

## Lean

`lean/Rules.lean` (from `py/rules.py`): ten shift rules over 3-cell words (and runs of 0s), found by a symbolic
search over all words of 1-3 cells, each for every n and every tape around.

## Halting

Only F1 halts. Open; n-gram CPS (widths 3..7) fails; no halt in 10^9 steps (C). `bbtools.cycles` (K = 2) makes
little progress (the string is rewritten, not shifted, so there are no linear regimes).

## Notes for later

* Find the sweep transducer: follow one sweep cell by cell and write it as a finite-state map on the words
  110/111 (with carry states); then identify the number it acts on (a base-2/base-3 reading of the string).
* Then the right-end structure: when the sweep reaches it, and what F1 needs there.

## Where a halt can come from

`lean/Route.lean` (kernel, written by `py/route.py`): `halt_route`, two steps before any halt the machine is in one
of: B with 1 under the head, 0 right, 0 two right.

## Pages

- [`pages/holdouts/1RB1LB_1LC0RD_0LE1LA_0RF1RA_1LE0LA_---0RB/explainer.html`](../../pages/holdouts/1RB1LB_1LC0RD_0LE1LA_0RF1RA_1LE0LA_---0RB/explainer.html)
- [`pages/holdouts/1RB1LB_1LC0RD_0LE1LA_0RF1RA_1LE0LA_---0RB/proof-status.html`](../../pages/holdouts/1RB1LB_1LC0RD_0LE1LA_0RF1RA_1LE0LA_---0RB/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LB_1LC0RD_0LE1LA_0RF1RA_1LE0LA_---0RB/lean/check.sh
```
