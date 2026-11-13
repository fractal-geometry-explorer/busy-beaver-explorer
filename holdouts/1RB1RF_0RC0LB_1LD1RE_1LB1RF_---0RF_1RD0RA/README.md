# 1RB1RF_0RC0LB_1LD1RE_1LB1RF_---0RF_1RD0RA

bbchallenge id 68358. A marker 0 drifts through a long alternating sea one cell per sweep while a binary counter at the right end counts the sweeps; when the marker reaches the far end a reset sweep starts the next round, one cell wider.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RF |
| B | 0RC | 0LB |
| C | 1LD | 1RE |
| D | 1LB | 1RF |
| E | --- | 0RF |
| F | 1RD | 0RA |

## What it does

Stop the run when the head reaches a new cell on the right. With `a = 10`, `c = 1110`:

    89,473,943  0 a^44 0 a^791 c^2 a^4 c a c 1^2 D>0
    89,549,578  0 a^60 0 a^775 c^2 a^4 c a c 1^3 F>0
    89,696,244  0 a^92 0 a^743 c^2 a^4 c a c 1^5 F>0
    89,971,146  0 a^156 0 a^679 c^2 a^4 c a c 1^7 F>0
    90,447,224  0 a^284 0 a^551 c^2 a^4 c a c 1^9 F>0
    91,104,470  0 a^540 0 a^295 c^2 a^4 c a c 1^11 F>0
    91,377,626  B>0 1^1671 c 1 a 0 1^7 ...                   (reset sweep)
    91,596,210  0 a^45 0 a^791 c a^9 c^2 a c 1^2 D>0

The left part is an alternating sea `0 a^x 0 a^y` (x + y fixed within a round) with one marker 0 after x copies of
`10`. The head shuttles between the marker and the right end, turning the sea into 1s and back; each round trip
moves the marker one cell and adds one to a counter in the right tail; the tape grows on the right only when the counter gains a digit, so between right growths the marker moves by
powers of 2 (64 x107, 32 x105, 16 x90, 128 x86, 8 x63, 256 x42, 4 x31, 2 x14 in the first 10^8
steps; 140 resets). When
the marker reaches the end of the sea a long sweep resets it and the sea grows: width ~ t^(1/3).

The near-duplicate `1RB0RF_1LC1RA_0RD0LC_1LB1RE_---0RA_1RC1RA` behaves the same way.

## Halting

E0 halts; E is entered only from C1 (`1RE`), so a halt needs C on a 1 with a 0 to its right. In the first 10^8 steps E
was entered 58,490 times, always on a 1, 58,053 times at least 7 cells from both ends (`c/sstat.c`). Open.

## Status

Open. Lean (`lean/Blank.lean`): the halting configurations (`step_none_iff`), no halt in 10,000 steps by the kernel, in 10,000,000 by `native_decide`. C: no halt in 10^9 steps (`tools/c/triage.c`) and in 10^12 steps (`c/mrun.c`, exact macro simulation). The structure described here is observed, not proved.

## First look

Growth class **power/power** (left: power, exponent 0.304; right: power,
exponent 0.349). After 1,000,000,000 steps: 3,909 cells visited (246 left of the
start, 2,932 right), 2,340 ones.

- left, step 969,386,424: `B>0 1^3829 0^2 1^10 0^3 1^3 0^2 1^4 0 1 0^5 1 0 1 0 1`
- left, step 991,715,276: `B>0 1^3865 0^2 1^6 0 1^3 0 1^5 0^3 1 0 1 0^3 1 0 1 0 1`
- right, step 973,119,511: `0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 `
- right, step 989,382,624: `0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 `



## Pages

- [`pages/holdouts/1RB1RF_0RC0LB_1LD1RE_1LB1RF_---0RF_1RD0RA/explainer.html`](../../pages/holdouts/1RB1RF_0RC0LB_1LD1RE_1LB1RF_---0RF_1RD0RA/explainer.html)
- [`pages/holdouts/1RB1RF_0RC0LB_1LD1RE_1LB1RF_---0RF_1RD0RA/proof-status.html`](../../pages/holdouts/1RB1RF_0RC0LB_1LD1RE_1LB1RF_---0RF_1RD0RA/proof-status.html)



## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RF_0RC0LB_1LD1RE_1LB1RF_---0RF_1RD0RA/lean/check.sh
gcc -O2 -o mrun holdouts/1RB1RF_0RC0LB_1LD1RE_1LB1RF_---0RF_1RD0RA/c/mrun.c && ./mrun 1RB1RF_0RC0LB_1LD1RE_1LB1RF_---0RF_1RD0RA 16 1000000000000
gcc -O2 -I tools/c -o sstat holdouts/1RB1RF_0RC0LB_1LD1RE_1LB1RF_---0RF_1RD0RA/c/sstat.c && ./sstat 1RB1RF_0RC0LB_1LD1RE_1LB1RF_---0RF_1RD0RA 100000000
```

## Later

- Decode the tail exactly (the binary digits and the carry rule) and the marker's start after each reset.
- Accelerate: the sweeps within a round are a linear regime (marker +1, counter +1); `bbtools.cycles` style jumps
  would reach far beyond 10^12.
- The twin `1RB0RF_1LC1RA_0RD0LC_1LB1RE_---0RA_1RC1RA` probably has the same proof.
