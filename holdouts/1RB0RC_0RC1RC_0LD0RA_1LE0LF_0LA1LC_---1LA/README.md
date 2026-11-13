# 1RB0RC_0RC1RC_0LD0RA_1LE0LF_0LA1LC_---1LA

bbchallenge id 65826. Open. A **collect/expand counter**: a left block of seven-cell words `(1011001)^p` and a right block `(011)^q` trade
places. Collecting moves q into p one word for one; expanding moves p back into q seven words for one, so each round
is about seven times longer (p = 602, q = 4,134, p = 4,374, q = 30,497). A third block `(110)^r` at the far right
grows between rounds (95, 209, 403, 665, 1,111).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RC |
| B | 0RC | 1RC |
| C | 0LD | 0RA |
| D | 1LE | 0LF |
| E | 0LA | 1LC |
| F | --- | 1LA |

## The tape as words

At the left end (state E):

* collect: `0 (1011001)^p (101)^5 1 0 (011)^q 0000 (110)^r`, e.g. step 5,800,574,389: p = 211, q = 30,578, r = 1,111;
  per visit p+1, q-1.
* expand: `0 (1011001)^p 1 0 1 1 0^5 1 1 0 1 1 0 0 1 (10)^3 (110)^q 000 (110)^r`, e.g. step 708,092,141: p = 4,290,
  q = 740; per four visits p-2, q+14.

## Rounds

| step | |
|---|---|
| 13,427,273 | p = 602 collected |
| 112,813,341 | q = 4,134 expanded |
| 617,145,533 | p = 4,374 collected |
| 5,639,901,953 | q = 30,497 expanded |

Between rounds a short pump phase moves part of p into r. At each visit of the right end the head runs an inner
zigzag along the end of the right block (each pass eats a cell and the literal region grows), so `bbtools.symtm`
does not compress the per-visit cycle; the cycle rules need an inner induction first.

## Sweeps (Lean, kernel, `lean/Rules.lean`)

| rule | statement | steps |
|---|---|---|
| `a_right` | `L A>(0011011)^n R` -> `L (1100110)^n A> R` | 13n |
| `d_left` | `L (1011001)^n D>1 R` -> `L D>1 (0110110)^n R` | 23n |
| `a_right3` | `L A>(011)^n R` -> `L (110)^n A> R` | 3n |

## Halting

The only halting transition is F on a 0; F is entered only from D on a 1 (D writes 0, moves left).

## Status

Open. Kernel: halting configurations, 10,000 steps, three shift rules. Native: 10^7 steps. Trusted: no halt in 10^10
steps (`c/ev.c`). The phase rates are measured.

## For later

* State the right-end zigzag as an inner rule (induction on the cells eaten), then prove the collect and expand cycles
  and the round map.

## First look

Growth class **sqrt/sqrt** (left: sqrt, exponent 0.498; right: sqrt,
exponent 0.478). After 1,000,000,000 steps: 43,491 cells visited (12,594 left of the
start, 17,410 right), 26,502 ones.

- left, step 971,976,277: `E>0 1 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 `
- left, step 987,704,249: `E>0 1 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 `
- right, step 972,322,623: `1 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 `
- right, step 988,040,901: `1 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 `

## Pages

- [`pages/holdouts/1RB0RC_0RC1RC_0LD0RA_1LE0LF_0LA1LC_---1LA/explainer.html`](../../pages/holdouts/1RB0RC_0RC1RC_0LD0RA_1LE0LF_0LA1LC_---1LA/explainer.html)
- [`pages/holdouts/1RB0RC_0RC1RC_0LD0RA_1LE0LF_0LA1LC_---1LA/proof-status.html`](../../pages/holdouts/1RB0RC_0RC1RC_0LD0RA_1LE0LF_0LA1LC_---1LA/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RC_0RC1RC_0LD0RA_1LE0LF_0LA1LC_---1LA/lean/check.sh
gcc -O2 -o ev holdouts/1RB0RC_0RC1RC_0LD0RA_1LE0LF_0LA1LC_---1LA/c/ev.c && ./ev 1RB0RC_0RC1RC_0LD0RA_1LE0LF_0LA1LC_---1LA 2000000000 L E 1 100000 12 | awk 'NR%300==0'
```
