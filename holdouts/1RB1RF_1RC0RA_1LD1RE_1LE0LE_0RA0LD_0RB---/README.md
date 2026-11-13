# 1RB1RF_1RC0RA_1LD1RE_1LE0LE_0RA0LD_0RB---

bbchallenge id 75094. A marker 0 drifts through a long alternating sea one cell per sweep while a base-3 counter at the right end counts the sweeps; when the marker reaches the far end a reset sweep starts the next round, one cell wider.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RF |
| B | 1RC | 0RA |
| C | 1LD | 1RE |
| D | 1LE | 0LE |
| E | 0RA | 0LD |
| F | 0RB | --- |

## What it does

Stop the run when the head reaches a new cell on the right. With `a = 10`, `c = 1110`:

    56,958,976  0 a^18 0 a^810 c a^3 c a^13 c a^5 1 a 1^2 C>0
    57,210,619  0 a^99 0 a^729 c a^3 c a^13 c a^5 c a c 1^2 C>0
    57,808,047  0 a^342 0 a^486 c a^3 c a^13 c a^5 c a c^2 1^2 C>0
    58,297,046  E>0 a^850 0^2 a^9 0^5 ...                         (reset sweep)
    58,315,798  0 a^6 0 a^843 c a^8 c^3 a 1^2 C>0

The left part is an alternating sea `0 a^x 0 a^y` (x + y fixed within a round) with one marker 0 after x copies of
`10`. The head shuttles between the marker and the right end; each round trip moves the marker one cell and
updates a counter in the right tail; the tape grows on the right only
when the counter gains a digit. Between right growths the marker moves by powers of 3 (243 x79, 81 x67, 27 x31, 9, 729
in the first 10^8 steps): the tail counts sweeps in base 3. When the marker reaches the end of the sea a long sweep
resets it and the sea grows by one cell, so the width grows like t^(1/3).

The near-duplicate `1RB0RE_1LC1RD_1LD0LD_0RE0LC_1RA1RF_0RA---` behaves the same way.

## Halting

F1 halts; F is entered only from E1 (`1RF`), so a halt needs E on a 1 with a 1 to its right. In the first 10^8 steps F
was entered 75,302 times, always on a 0, 74,846 times at least 7 cells from both ends (`c/sstat.c`). Open.

## Status

Open. Lean (`lean/Blank.lean`): the halting configurations (`step_none_iff`), no halt in 10,000 steps by the kernel, in 10,000,000 by `native_decide`. C: no halt in 10^9 steps (`tools/c/triage.c`) and in 10^15 steps (`c/mrun.c`, exact macro simulation). The structure described here is observed, not proved.

## First look

Growth class **power/power** (left: power, exponent 0.309; right: power,
exponent 0.349). After 1,000,000,000 steps: 4,585 cells visited (258 left of the
start, 3,474 right), 2,285 ones.

- left, step 971,116,962: `E>0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 `
- left, step 991,609,360: `E>0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 `
- right, step 971,665,400: `0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0^2 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 `
- right, step 988,347,614: `0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 `



## Pages

- [`pages/holdouts/1RB1RF_1RC0RA_1LD1RE_1LE0LE_0RA0LD_0RB---/explainer.html`](../../pages/holdouts/1RB1RF_1RC0RA_1LD1RE_1LE0LE_0RA0LD_0RB---/explainer.html)
- [`pages/holdouts/1RB1RF_1RC0RA_1LD1RE_1LE0LE_0RA0LD_0RB---/proof-status.html`](../../pages/holdouts/1RB1RF_1RC0RA_1LD1RE_1LE0LE_0RA0LD_0RB---/proof-status.html)



## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RF_1RC0RA_1LD1RE_1LE0LE_0RA0LD_0RB---/lean/check.sh
gcc -O2 -o mrun holdouts/1RB1RF_1RC0RA_1LD1RE_1LE0LE_0RA0LD_0RB---/c/mrun.c && ./mrun 1RB1RF_1RC0RA_1LD1RE_1LE0LE_0RA0LD_0RB--- 2 1000000000000000
gcc -O2 -I tools/c -o sstat holdouts/1RB1RF_1RC0RA_1LD1RE_1LE0LE_0RA0LD_0RB---/c/sstat.c && ./sstat 1RB1RF_1RC0RA_1LD1RE_1LE0LE_0RA0LD_0RB--- 100000000
```

## Later

- Decode the tail exactly: which words are the base-3 digits, and the rule for a carry.
- From that, the marker's start position after each reset, and whether E can ever meet `1 1` (the F1 halt).
- The twin `1RB0RE_1LC1RD_1LD0LD_0RE0LC_1RA1RF_0RA---` probably has the same proof.
