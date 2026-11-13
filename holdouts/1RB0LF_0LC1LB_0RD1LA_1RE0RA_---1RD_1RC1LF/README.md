# 1RB0LF_0LC1LB_0RD1LA_1RE0RA_---1RD_1RC1LF

bbchallenge id 147101, group G08 (two-sided sqrt growth). Whether it halts from blank tape is **open**. Pages:
[`explainer.html`](../../pages/holdouts/1RB0LF_0LC1LB_0RD1LA_1RE0RA_---1RD_1RC1LF/explainer.html), [`proof-status.html`](../../pages/holdouts/1RB0LF_0LC1LB_0RD1LA_1RE0RA_---1RD_1RC1LF/proof-status.html), both built from
[`status.json`](status.json).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LF |
| B | 0LC | 1LB |
| C | 0RD | 1LA |
| D | 1RE | 0RA |
| E | --- | 1RD |
| F | 1RC | 1LF |

## What it does

A bouncer: the head sweeps over the whole tape, and both ends grow like the square root of the step count. The left
part is regular, the right end is not.

**Where it can halt.** Only in E reading a 0. E is entered only from `D>0` (write 1, move right), so the machine
halts exactly when `D>0 0` occurs. In the first 10^8 steps E is entered 8,152,495 times, always onto a 1
(`c/haltwatch.c`).

**The left part.** At the left end (`py/snapshots.py 3e6 L 40`) the tape alternates between

    F>0 0 (1011)^77 1 (101110)^n 1010 (111011)^23 ...
    F>0 0 (1011)^77 1010 (111011)^n (1)^5 (011101)^23 ...

(the same tape with the long block shifted by two cells), and n grows by one every two trips: 296 at step 2,896,194,
517 at 7,018,812, 2017 at 81,421,812. `(1011)^77` is built in an earlier phase (steps 75,000 to 150,000) from a first
block of about 48 `101110`s, and is not touched later.

**The right end.** Behind the middle counter (23 blocks at 3·10^6 steps, 17 at 8·10^7, 16 at 10^9, its 6-cell word a rotation of
`111011` or `101110`) the last few dozen cells change irregularly from trip to trip, e.g.

    ... (111011)^23 (1)^7 0 (1)^7 010 (111011)^3 10 (1)^7 (01)^3 10
    ... (011101)^23 (01)^3 1 (10)^3 (1)^5 (011101)^3 010 (1)^3 0 (1)^8 0
    ... (111011)^23 (1)^7 0 (1)^7 010 (111011)^3 (1)^5 (01)^3 110110

## What is proved (Lean)

Only the generated `lean/Blank.lean`: the halting configurations, no halt in 10^4 steps (kernel) and 10^7
(`native_decide`).

## Computed / observed

- No halt in 10^9 steps (`tools/c/triage.c`).
- The halting-condition counts above (`c/haltwatch.c`), the left-part shapes (`py/snapshots.py`).

## Open, and next steps

- The right end has no visible period. A proof of non-halting would need a description of it, for example a finite
  or regular set of words that the head's visits keep it in (a closed-language argument restricted to the right end,
  with the left part as a parameterised block).
- The middle counter shrinks slowly; what happens when it reaches 0 has not been seen (16 blocks from 7·10^8
  to 10^9 steps, n = 7166 at step 952,948,534; the losses get rarer).
- The left-part round trip could be proved by symtm as a rule only once the right end is treated as a context the
  head enters and leaves in a known way, which is exactly what is not known.

## Where a halt can come from

`lean/Route.lean` (kernel, written by `py/route.py`): `halt_route`, two steps before any halt the machine is in one
of: C with 0 under the head, 0 right, 0 two right; E with 1 under the head, 0 right, 0 two right.

