# 1RB0RC_1RC---_1LD1RE_1LE0LD_1RA0LF_0RC0RB

bbchallenge id 16925. One of the six-state holdouts whose halting from blank tape is open; analyzed by hand (group G02). The pages are built from [`status.json`](status.json).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RC |
| B | 1RC | --- |
| C | 1LD | 1RE |
| D | 1LE | 0LD |
| E | 1RA | 0LF |
| F | 0RC | 0RB |

## What it does

Each time the head is in E on a 0 at the left end, with `a = 10`, `b = 110`, `c = 1110`, the tape is a run of X
ones and a stack `0000 a^s1 b a^s2 b ...` (possibly empty):

    step 17,557,542:  E>0 1^1072 c 0000 a^534 1
                      E>0 1^536 c 0000 a^268 b a^533 1
                      E>0 1^268 c 0000 a^134 b a^267 b a^533 1
                      E>0 1^134 c 0000 a^67 b a^133 b a^267 b a^533 1

The stack map (observed at the 69 samples to 2.9·10^10 steps):

| case | next sample |
|---|---|
| stack non-empty, X ≡ 0 (mod 4) | X' = X/2, push X/4, old top − 1 (every case) |
| empty, X ≡ 0 (mod 4) | X' = 3X/2 + 2, empty (20 of 20 empty cases from X = 18 on, with the next row) |
| empty, X ≡ 2 (mod 4) | X' = X/2 + 3, stack [(X−2)/4] |
| non-empty, X ≡ 2 (mod 4) | fold into a larger X; one entry s: X' = X + 3s + 5 (12118 [6057] → 30294); general rule not decoded |

Sweeps across the whole tape make the square-root side; the samples get rarer as X grows (logarithmic side).

## Status

Open. The only halt is B reading a 1; B follows F reading a 1 (about 1.25·10^8 times in 10^9 steps) or A reading a
0, and has always read a 0.

- Lean, kernel: five shift rules (`lean/Rules.lean`); halting configurations, 10^4 steps (`lean/Blank.lean`).
  `native_decide`: 10^7 steps.
- Computed: no halt in 10^10 steps (`tools/c/tmrun.c`); `bbtools.ctl` K = 2..7 allows a halt; n-gram CPS fails.

## Notes for later

- Decode the fold (non-empty stack, X ≡ 2 mod 4): collect more samples (they get rare; use the cycle accelerator
  or a macro simulator) and fit it. With the whole map, look for the configurations that put F on `11`.

## Pages

- [`pages/holdouts/1RB0RC_1RC---_1LD1RE_1LE0LD_1RA0LF_0RC0RB/explainer.html`](../../pages/holdouts/1RB0RC_1RC---_1LD1RE_1LE0LD_1RA0LF_0RC0RB/explainer.html)
- [`pages/holdouts/1RB0RC_1RC---_1LD1RE_1LE0LD_1RA0LF_0RC0RB/proof-status.html`](../../pages/holdouts/1RB0RC_1RC---_1LD1RE_1LE0LD_1RA0LF_0RC0RB/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RC_1RC---_1LD1RE_1LE0LD_1RA0LF_0RC0RB/lean/check.sh
```
