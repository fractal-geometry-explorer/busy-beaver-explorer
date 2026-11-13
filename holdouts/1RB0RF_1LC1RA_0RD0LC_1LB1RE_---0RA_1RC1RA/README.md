# 1RB0RF_1LC1RA_0RD0LC_1LB1RE_---0RA_1RC1RA

bbchallenge id 72270. A marker 0 drifts through a long alternating sea one cell per sweep while a binary counter at the right end counts the sweeps; when the marker reaches the far end a reset sweep starts the next round, one cell wider.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RF |
| B | 1LC | 1RA |
| C | 0RD | 0LC |
| D | 1LB | 1RE |
| E | --- | 0RA |
| F | 1RC | 1RA |

## What it does

Stop the run when the head reaches a new cell on the right. With `a = 10`, `c = 1110`:

    96,383,862  0 a^24 0 a^842 c a c a^6 c 1^2 B>0
    96,424,357  0 a^32 0 a^834 c a c a^6 c 1^3 A>0
    96,504,199  0 a^48 0 a^818 c a c a^6 c 1^5 A>0
    96,659,277  0 a^80 0 a^786 c a c a^6 c 1^7 A>0
    96,951,003  0 a^144 0 a^722 c a c a^6 c 1^9 A>0
    97,460,729  0 a^272 0 a^594 c a c a^6 c 1^11 A>0
    98,185,271  0 a^528 0 a^338 c a c a^6 c 1^13 A>0
    98,543,083  C>0 1^1738 c 1^12 c ...                      (reset sweep)
    98,684,671  0 a^28 0 a^842 c a^9 1^2 c a^2 1^2 B>0

The left part is an alternating sea `0 a^x 0 a^y` (x + y fixed within a round) with one marker 0 after x copies of
`10`. The head shuttles between the marker and the right end, turning the sea into 1s and back; each round trip
moves the marker one cell and adds one to a counter in the right tail; the tape grows on the right only when the counter gains a digit, so between right growths the marker moves by
powers of 2 (64 x104, 32 x99, 128 x85, 16 x79, 8 x43, 256 x43, 4 x23 in the first 10^8 steps; 139 resets). When
the marker reaches the end of the sea a long sweep resets it and the sea grows: width ~ t^(1/3).

The near-duplicate `1RB1RF_0RC0LB_1LD1RE_1LB1RF_---0RF_1RD0RA` behaves the same way.

## Halting

E0 halts; E is entered only from D1 (`1RE`), so a halt needs D on a 1 with a 0 to its right. In the first 10^8 steps E
was entered 58,016 times, always on a 1, 57,572 times at least 7 cells from both ends (`c/sstat.c`). Open.

## Status

Open. Lean (`lean/Blank.lean`): the halting configurations (`step_none_iff`), no halt in 10,000 steps by the kernel, in 10,000,000 by `native_decide`. C: no halt in 10^9 steps (`tools/c/triage.c`) and in 10^12 steps (`c/mrun.c`, exact macro simulation). The structure described here is observed, not proved.

## First look

Growth class **power/power** (left: power, exponent 0.295; right: power,
exponent 0.349). After 1,000,000,000 steps: 3,893 cells visited (246 left of the
start, 2,958 right), 2,178 ones.

- left, step 961,716,673: `C>0 1^3799 0^2 1^6 0^2 1^8 0^7 1 0^3 1 0 1 0 1`
- left, step 983,678,675: `C>0 1^3824 0^3 1^14 0^2 1^6 0^2 1^4 0 1 0^3 1 0^3 1 0 1 0 1`
- right, step 967,076,134: `0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 `
- right, step 984,328,309: `0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0^2 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 `



## Pages

- [`pages/holdouts/1RB0RF_1LC1RA_0RD0LC_1LB1RE_---0RA_1RC1RA/explainer.html`](../../pages/holdouts/1RB0RF_1LC1RA_0RD0LC_1LB1RE_---0RA_1RC1RA/explainer.html)
- [`pages/holdouts/1RB0RF_1LC1RA_0RD0LC_1LB1RE_---0RA_1RC1RA/proof-status.html`](../../pages/holdouts/1RB0RF_1LC1RA_0RD0LC_1LB1RE_---0RA_1RC1RA/proof-status.html)



## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RF_1LC1RA_0RD0LC_1LB1RE_---0RA_1RC1RA/lean/check.sh
gcc -O2 -o mrun holdouts/1RB0RF_1LC1RA_0RD0LC_1LB1RE_---0RA_1RC1RA/c/mrun.c && ./mrun 1RB0RF_1LC1RA_0RD0LC_1LB1RE_---0RA_1RC1RA 12 1000000000000
gcc -O2 -I tools/c -o sstat holdouts/1RB0RF_1LC1RA_0RD0LC_1LB1RE_---0RA_1RC1RA/c/sstat.c && ./sstat 1RB0RF_1LC1RA_0RD0LC_1LB1RE_---0RA_1RC1RA 100000000
```

## Later

- Decode the tail exactly (the binary digits and the carry rule) and the marker's start after each reset.
- Accelerate: the sweeps within a round are a linear regime (marker +1, counter +1); `bbtools.cycles` style jumps
  would reach far beyond 10^12.
- The twin `1RB1RF_0RC0LB_1LD1RE_1LB1RF_---0RF_1RD0RA` probably has the same proof.
