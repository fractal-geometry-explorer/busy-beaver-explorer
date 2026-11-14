# 1RB0LF_1LC1RF_---1LD_0LE0LB_0RA0LA_0RA1RB

bbchallenge id 140963, a six-state holdout of group G05 (growth class fixed/sqrt). **Open.** Between long
reorganising sweeps the tape is a list of digits that follows a simple exact pattern (seen 282 times without
exception); the reorganising sweeps grow very fast, and the seventh one, from a 278-digit tape at step 9,477,912,
is still running at step 10^10. Nothing beyond the generated bounded runs is proved in Lean yet.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LF |
| B | 1LC | 1RF |
| C | --- | 1LD |
| D | 0LE | 0LB |
| E | 0RA | 0LA |
| F | 0RA | 1RB |


## What it does

**Halting.** C is entered only from B reading 0 (`1LC`), and C halts on a 0. So the machine halts exactly when B
reads a 0 with a 0 on its left (`0 B>0`).

**Digits.** Each time D reaches the left end of the tape, the tape is `D>0 1 1` followed by the words x = `0 1 1` and
y = `0 0 1 1`. Read it as a list of digits: the leading `0 1 1` is the first digit, and every y starts a new digit
whose value is 1 plus the number of x after it (`py/digits.py`). For example, at step 98,599:

    [1, 2^25, 4, 4, 10, 10, 40, 28, 1]

**The simple phase** (seen, not proved). From one left-end visit to the next, a digit 2 is inserted after the first
digit and the last digit loses 1:

    [1, d_2, ..., d_k, n + 1]  ->  [1, 2, d_2, ..., d_k, n]

This holds for 282 of the 289 transitions between consecutive visits in the first 10^10 steps (`py/digits.py check`). Each
visit is one round trip of the head over the tape, so the phase lasts n round trips.

**Resets.** When the last digit is 1, a long sweep rewrites the tape instead: the run of 2s at the front becomes a
run of 4s (one longer, in the last two resets), and the digits behind it change in a way not yet described:

| step | before | after |
|---|---|---|
| 127 -> 329 | [1, 2, 1] | [1, 4, 3] |
| 567 -> 1405 | [1, 2, 2, 4, 1] | [1, 4, 4, 4, 5] |
| 2409 -> 14687 | [1, 2^4, 4^3, 1] | [1, 4, 4, 14, 10, 28, 2] |
| 15460 -> 57674 | [1, 2, 4, 4, 14, 10, 28, 1] | [1, 4, 4, 10, 10, 40, 28, 26] |
| 98599 -> 679125 | [1, 2^25, 4^2, 10^2, 40, 28, 1] | [1, 4^26, 10, 84, 82, 153] |
| 1611037 -> 7691851 | [1, 2^152, 4^26, 10, 84, 82, 1] | [1, 4^153, 10, 38, 28^23, 82, 98] |

The next reset starts from `[1, 2^97, 4^153, 10, 38, 28^23, 82, 1]` (278 digits) at step 9,477,912 and has not ended
by step 10^10: in it the tape turns into other words (`0 1 0 1^4` repeated, at step 2.8·10^9), a counter of its own.
The reset lengths so far are 202, 838, 12,278, 42,214, 580,526, 6,080,814 steps and then more than 10^10.

## Status and evidence

**Lean** (`lean/Blank.lean`, generated): `step_none_iff` (kernel); no halt in 10,000 steps (kernel) and 10^7 steps
(`native_decide`).

**Computed (trusted).** `tmrun` (C): no halt in the first 10^10 steps; 290 left-end visits of D, all digit tapes
(`py/digits.py`); the simple-phase rule on 282 of the 289 transitions, the others being the six resets above and the
first visit.

**Heuristic.** The simple-phase rule for all digit lists.

**Open.** Whether it halts. The resets are where anything new happens, and the seventh one already runs for more than
10^10 steps.

## Reproduce

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LF_1LC1RF_---1LD_0LE0LB_0RA0LA_0RA1RB/lean/check.sh
/home/user/w/tmrun 1RB0LF_1LC1RF_---1LD_0LE0LB_0RA0LA_0RA1RB 10000000000 at D L 1000000 | python3 holdouts/1RB0LF_1LC1RF_---1LD_0LE0LB_0RA0LA_0RA1RB/py/digits.py check   # about 1 minute
```

## Accelerated run (13 November 2026)

Observed, not proved: the accelerated simulator `rsim.py` ran 1.69x10^15 steps from blank tape without reaching a halting transition. Its tape, state and head position were equal to those of a plain C simulator at 6 checkpoints, the last at 1.13x10^10 steps. Of these steps, the part after the last checkpoint rests on the simulator alone, including 2,254 trip-level jumps: a jump applies many identical round trips at once after seeing the same tape shape recur with constant count changes, which is validated against direct simulation but not proved.

```sh
python3 holdouts/1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA1RF_0LC---/py/rsim_screen.py 1RB0LF_1LC1RF_---1LD_0LE0LB_0RA0LA_0RA1RB 400
```

## Pages

- [`pages/holdouts/1RB0LF_1LC1RF_---1LD_0LE0LB_0RA0LA_0RA1RB/explainer.html`](../../pages/holdouts/1RB0LF_1LC1RF_---1LD_0LE0LB_0RA0LA_0RA1RB/explainer.html)
- [`pages/holdouts/1RB0LF_1LC1RF_---1LD_0LE0LB_0RA0LA_0RA1RB/proof-status.html`](../../pages/holdouts/1RB0LF_1LC1RF_---1LD_0LE0LB_0RA0LA_0RA1RB/proof-status.html)

## For later

- Prove the simple phase in Lean for every digit list: the head's sweep over one digit `0 0 1 1 (0 1 1)^d` in each
  direction (with `bbtools.symtm.prove`), composed by induction over the list.
- Work out the reset sweep: it rewrites the tape into the words `0 1 0 1^4` and back; a description of that inner
  counter is needed to say what the digits after a reset are, and to run the machine past the seventh reset (an
  accelerated simulator, since the seventh reset alone is longer than 10^10 steps).
