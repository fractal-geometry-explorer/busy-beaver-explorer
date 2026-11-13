# 1RB---_0RC0LF_1LD0RE_1RC0LB_1RD1RA_1LB0LC

bbchallenge id 29687. A list of counters: the tape is runs of 001 (even lengths) separated by 0001, recoded into 110/1110 and back by every sweep; over a cycle every entry grows by 2 and new small entries are pushed at the left.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | --- |
| B | 0RC | 0LF |
| C | 1LD | 0RE |
| D | 1RC | 0LB |
| E | 1RD | 1RA |
| F | 1LB | 0LC |

## What it does

With `a = 001`, `b = 0001`, the tape at B's visits to the left end is a list of even numbers (runs of `a` between
single `b`s), e.g. step 7,203,647: `a b^2 a^8 b a^4 b a^4 ... b a^8 b a^6 b a^6 b a^6 b a^10 b a^8 ...`.
Sweeps rewrite the words into their complements `110` / `1110` and back, whole runs at a time (`lean/Rules.lean`,
six rules, kernel). Between steps 7,203,647 and 8,576,224 every entry grew by exactly 2 and two new entries came in
at the left:

    7,203,647:        8  4x7  8  6  6  6 10  8x4  6  8 10 10  8 10  8 22 12
    8,576,224:  4  2 10  6x7 10  8  8  8 12 10x4  8 10 12 12 10 12 10 24 14

so the left side is a list of counters that all advance together (heuristic), with reshaping events at the left
end. The right side is the bouncer (sqrt growth).

## Status

Open. Kernel: halting configurations, no halt in 10^4 steps (10^7 native), the six recoding rules. Halting needs A
to read a 1. CTL (K = 2..5) and NGramCPS (widths 2-8, -H, -U) fail.

## For later

1. Prove one full cycle as a rule on a list of runs (needs the turn at each `b`, then induction over the list).
2. Describe the left-end events (the `b^k` front and new entries) as a map, and check it over a long run.
3. With both, look for an invariant (entries even, list shape) that rules out A reading a 1. Looks tractable.

## Reproduce

```sh
./tokrun 1RB---_0RC0LF_1LD0RE_1RC0LB_1RD1RA_1LB0LC 10000000 a=001,b=0001 L 100000 | awk '$4=="B"'
. /etc/profile.d/lean.sh && holdouts/1RB---_0RC0LF_1LD0RE_1RC0LB_1RD1RA_1LB0LC/lean/check.sh
```

## Pages

- [`pages/holdouts/1RB---_0RC0LF_1LD0RE_1RC0LB_1RD1RA_1LB0LC/explainer.html`](../../pages/holdouts/1RB---_0RC0LF_1LD0RE_1RC0LB_1RD1RA_1LB0LC/explainer.html)
- [`pages/holdouts/1RB---_0RC0LF_1LD0RE_1RC0LB_1RD1RA_1LB0LC/proof-status.html`](../../pages/holdouts/1RB---_0RC0LF_1LD0RE_1RC0LB_1RD1RA_1LB0LC/proof-status.html)
