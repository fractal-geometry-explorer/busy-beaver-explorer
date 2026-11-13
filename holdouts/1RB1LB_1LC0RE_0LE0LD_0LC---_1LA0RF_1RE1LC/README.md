# 1RB1LB_1LC0RE_0LE0LD_0LC---_1LA0RF_1RE1LC

bbchallenge id 149506. One of the six-state holdouts. Analyzed by hand (group G02), partly: shift rules proved, cascade only observed.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LB |
| B | 1LC | 0RE |
| C | 0LE | 0LD |
| D | 0LC | --- |
| E | 1LA | 0RF |
| F | 1RE | 1LC |

## What it does (observed)

With x = `1110`, at step 2,048,043,645 the tape is

    A>0 1 0 x^5326 1 0 11 0 x^579 00 x^3766 1 0 11 0 x^1939 1 0 11 0 x^78 00 x^5 111   (+ ~60 cells right of start)

At each later visit of the left end the segment before the `00` marker loses ~26 words and the one after gains as
many (579 -> 9 and 3766 -> 4336 by step 2,075,216,540); the first segment gains ~3.5. Then the marker restarts
(`x^5405 00 x^5 1 0 11 0 x^4345 ...`) and the marker of the last segment moves by 8 (`x^78 00 x^5` ->
`x^70 00 x^13`). The right side gains one cell per record, records about 1.5 times apart (3.0e8, 4.9e8, 7.6e8,
1.11e9, 1.61e9, 2.41e9).

## Lean

`lean/Rules.lean` (from `py/rules.py`): twelve shift rules over 2- and 4-cell words, found by a symbolic search,
each for every n and every tape around.

## Halting

Only D1 halts. Open. n-gram CPS (widths 3..7) fails; no halt in 10^9 steps (C).

## Notes for later

* Take the visit of the left end as the sample, prove the per-visit rule (b - 26, c + 26, a + 3.5 on average: the
  exact rule depends on parities) with `bbtools.symtm`, then the rule for the marker's rebirth; this gives a
  multi-digit counter whose overflow should decide D1.

## Pages

- [`pages/holdouts/1RB1LB_1LC0RE_0LE0LD_0LC---_1LA0RF_1RE1LC/explainer.html`](../../pages/holdouts/1RB1LB_1LC0RE_0LE0LD_0LC---_1LA0RF_1RE1LC/explainer.html)
- [`pages/holdouts/1RB1LB_1LC0RE_0LE0LD_0LC---_1LA0RF_1RE1LC/proof-status.html`](../../pages/holdouts/1RB1LB_1LC0RE_0LE0LD_0LC---_1LA0RF_1RE1LC/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LB_1LC0RE_0LE0LD_0LC---_1LA0RF_1RE1LC/lean/check.sh
```
