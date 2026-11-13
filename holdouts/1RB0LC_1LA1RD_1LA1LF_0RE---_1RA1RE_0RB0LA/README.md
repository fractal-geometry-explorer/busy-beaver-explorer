# 1RB0LC_1LA1RD_1LA1LF_0RE---_1RA1RE_0RB0LA

bbchallenge id 124153, group G08 (two-sided sqrt growth). Whether it halts from blank tape is **open**. Pages:
[`explainer.html`](../../pages/holdouts/1RB0LC_1LA1RD_1LA1LF_0RE---_1RA1RE_0RB0LA/explainer.html), [`proof-status.html`](../../pages/holdouts/1RB0LC_1LA1RD_1LA1LF_0RE---_1RA1RE_0RB0LA/proof-status.html), both built from
[`status.json`](status.json).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LC |
| B | 1LA | 1RD |
| C | 1LA | 1LF |
| D | 0RE | --- |
| E | 1RA | 1RE |
| F | 0RB | 0LA |

## What it does

A bouncer over runs of `01`. Both ends grow like the square root of the step count.

**Where it can halt.** Only in D reading a 1. D is entered only from `B>1` (1RD), so the machine halts exactly when
`B>1 1` occurs. In the first 10^8 steps D is entered 10,419,815 times, always onto a 0 (`c/haltwatch.c`).

**The tape** (`py/snapshots.py 3e7 L 60`, every 60th left-end record):

    1448288 A>0 10110110 (01010010101)^85 01010010110 (01)^5 0 (01)^8 0 (01)^8 0 (01)^5 0 (01)^8 001010 ...
    1705608 A>0 (10101010100)^78 (10)^11 (01)^5 0 (01)^8 (00101010101)^4 (01)^6 0 (01)^5 ...
    ...                (69, 61, 53, 44, 36, 27, 18, 9 at the next samples)
    4678768 A>0 01011001010 (01)^11 0 (01)^5 0 (01)^8 (00101010101)^4 ...

Runs of `01` separated by single 0s, lengths mostly 2, 3, 5, 8, 11; `01010010101` is a run of 2 then a run of 3. The
block at the left end grows and is eaten back, about nine words per sixty left-end visits, again and again (116 words at
step 26,755,844, 339 at step 38,516,556).

## What is proved (Lean)

Only the generated `lean/Blank.lean`: the halting configurations, no halt in 10^4 steps (kernel) and 10^7
(`native_decide`).

## Computed / observed

- No halt in 10^9 steps (`tools/c/triage.c`).
- The halt-entry counts (`c/haltwatch.c`) and the run picture (`py/snapshots.py`).

## Open, and next steps

- The eating of the end block looks regular: a symtm rule for one left-end visit with the block as
  `(01010010101)^m` should be provable, once the right part of the tape is understood well enough to be a context
  the head crosses and comes back from.
- What the cycle does to the run lengths of the rest of the tape is the real question.
