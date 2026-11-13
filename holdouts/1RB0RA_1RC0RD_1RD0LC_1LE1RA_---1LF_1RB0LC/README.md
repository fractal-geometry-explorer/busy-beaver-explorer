# 1RB0RA_1RC0RD_1RD0LC_1LE1RA_---1LF_1RB0LC

bbchallenge id 69417. Its tape is a few long runs of <code>110</code> separated by short groups of 0s; a marker cuts the first run at a point that moves from round to round, and a solid tail on the right grows two cells at a time.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RA |
| B | 1RC | 0RD |
| C | 1RD | 0LC |
| D | 1LE | 1RA |
| E | --- | 1LF |
| F | 1RB | 0LC |

## What it does

Stop the run when the head reaches a new cell (`b = 110`):

    98,119,248  1 0 b^214 1 0^2 1 0 b^100 1^4 b^280 1^12 b^2 1^9 A>0              (right end)
    98,238,925  C>0^2 b^317 0^3 b^280 0^6 1 0^5 b^2 0 b 0^5 1^2                   (left end)
    99,006,704  1 0 b^173 1 0^2 1 0 b^142 1^4 b^281 1^8 b^2 1^13 A>0              (right end)
    99,199,973  C>0^2 b^318 0^3 b^281 0^2 1 0^5 b^2 0^2 1 0^2 b 0^5 1^2           (left end)
    99,942,628  1 0 b^158 1 0^2 1 0 b^158 1^4 b^282 1^4 b^2 1^17 A>0              (right end)

Two long runs of `110`; at the right-end moments a marker `1 0^2 1 0` cuts the first one (214 + 100, 173 + 142,
158 + 158) at a point that moves from round to round. Not worked out further.

## Halting

E0 halts; E is entered only from D0 (`1LE`), so a halt needs `0 D>0`. In the first 10^8 steps E was entered
12,465,925 times, always on a 1 (`c/sstat.c`). Open.

## Status

Open. Lean (`lean/Blank.lean`): the halting configurations (`step_none_iff`), no halt in 10,000 steps by the kernel, in 10,000,000 by `native_decide`. C: no halt in 10^9 steps (`tools/c/triage.c`) and in 10^12 steps (`c/mrun.c`, exact macro simulation). The structure described here is observed, not proved.

## First look

Growth class **power/power** (left: power, exponent 0.329; right: power,
exponent 0.331). After 1,000,000,000 steps: 3,953 cells visited (1,088 left of the
start, 2,124 right), 2,625 ones.

- left, step 968,336,707: `C>0 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 `
- left, step 986,309,713: `C>0 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 `
- right, step 973,301,689: `1 0 1^2 0 1^2 0 1 0^2 1 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 `
- right, step 991,251,615: `1 0 1^2 0 1^2 0 1 0^2 1 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 `



## Pages

- [`pages/holdouts/1RB0RA_1RC0RD_1RD0LC_1LE1RA_---1LF_1RB0LC/explainer.html`](../../pages/holdouts/1RB0RA_1RC0RD_1RD0LC_1LE1RA_---1LF_1RB0LC/explainer.html)
- [`pages/holdouts/1RB0RA_1RC0RD_1RD0LC_1LE1RA_---1LF_1RB0LC/proof-status.html`](../../pages/holdouts/1RB0RA_1RC0RD_1RD0LC_1LE1RA_---1LF_1RB0LC/proof-status.html)



## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RA_1RC0RD_1RD0LC_1LE1RA_---1LF_1RB0LC/lean/check.sh
gcc -O2 -o mrun holdouts/1RB0RA_1RC0RD_1RD0LC_1LE1RA_---1LF_1RB0LC/c/mrun.c && ./mrun 1RB0RA_1RC0RD_1RD0LC_1LE1RA_---1LF_1RB0LC 12 1000000000000
gcc -O2 -I tools/c -o sstat holdouts/1RB0RA_1RC0RD_1RD0LC_1LE1RA_---1LF_1RB0LC/c/sstat.c && ./sstat 1RB0RA_1RC0RD_1RD0LC_1LE1RA_---1LF_1RB0LC 100000000
```

## Later

- Work out how the marker's cut point moves from round to round (it is not monotone: 236, 188, 169, 251, 214,
  173, 158 at the right-end moments between steps 9.3*10^7 and 10^8).
- Then whether D can meet `0 D>0`.
