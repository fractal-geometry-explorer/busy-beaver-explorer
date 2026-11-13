# 1RB1LF_0RC0RB_0LD1RB_1LE0LB_0LA1LC_0LB---

bbchallenge id 57056. One of the six-state holdouts whose halting from blank tape is open. Family: Counter with words 1 0 / 1 1 0 0 / 1 0^3 (exp/exp; structure not yet found).


| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LF |
| B | 0RC | 0RB |
| C | 0LD | 1RB |
| D | 1LE | 0LB |
| E | 0LA | 1LC |
| F | 0LB | --- |

## What it does (first look)

At the left end the tape reads `F>0 1 0 1 0 ... 1 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1 0 1 0 ...`: a stretch `(1 0)^n` followed by the words `1 1 0`, `1 1 0 0` and `1 0`. On the right the tape is single 1s separated by one, two or three 0s.

The head reaches new cells on the left in groups of four (states F, B, E, A). Between 8·10^7 and 1.9·10^8 steps the stretch `(1 0)^n` goes from 34 words to 39 and then falls back to 34: something at its right end consumes it, like a carry.

## What is established

**Proved in Lean, kernel only:** the halting configurations (`step_none_iff`, `lean/Blank.lean`); no halt in 10,000 steps.

**Proved in Lean with `native_decide`:** no halt in 10^7 steps.

**Computed** (trusted):

- No halt in the first 10^10 steps: The C simulator `tools/c/tmrun.c` runs 10^10 steps from blank tape without a halt; at the end the tape holds 255 ones. (`tmrun 1RB1LF_0RC0RB_0LD1RB_1LE0LB_0LA1LC_0LB--- 10000000000`)
- No halt in the first 10^9 steps: The C simulator `tools/c/triage.c` runs 10^9 steps without a halt; at the end 394 cells have been visited and 225 of them hold a 1. (`holdouts/triage.json`)
- Where a halt can be: A closed tape language of windows of 5 cells (`tools/py/bbtools/ctl.py`, closure checked by the script, not by Lean) contains every configuration reachable from blank tape, and its only halting configurations have F reading a 1 with `F>1 1 1 0 1 0`. (`python3 -m bbtools.ctl 1RB1LF_0RC0RB_0LD1RB_1LE0LB_0LA1LC_0LB--- 5`)

- A doubling map at the left end: at the left-end visits in state F the tape right of the head reads, in words
  a = `1100`, b = `110`, c = `10`, `c^s MID b^m c c 0 b^j`. Between consecutive visits with the same MID, s grows
  by 2 and (m, j) → (m - j - k, 2j + k), k constant in the phase (m + j conserved, j doubling), e.g. (33, 1) → (29, 5)
  → (21, 13) → (5, 29) with k = 3. All 39 transitions from step 1,158 to 5·10^9 (24 phases, k from 1 to 23) follow it;
  only the first one (step 636) does not. A phase ends when m is too small, and MID changes like a counter digit.
  (`tmrun 1RB1LF_0RC0RB_0LD1RB_1LE0LB_0LA1LC_0LB--- 5000000000 at F L 5000 | python3 py/phase_check.py`, output `py/phase_check_5e9.txt`)

**Heuristic:**

- Growth shape: exp/exp: Left of the start, the visited part of the tape grows like the logarithm of the step count: each new cell costs a roughly constant factor more time, the signature of a *counter* or of a Collatz-like map whose values are written on the tape (fitted exponent 0.093). Right of the start it grows like the logarithm of the step count: each new cell costs a roughly constant factor more time, the signature of a *counter* or of a Collatz-like map whose values are written on the tape (fitted exponent 0.087).
- The stretch at the left: At the left records between 8·10^7 and 1.9·10^8 steps the left end reads `F>0 (1 0)^n 1^2 0^2 1^2 0 ...` with n going 34, 35, ..., 39, then back to 34 and up again: the stretch grows one word per record and is periodically consumed.

**Open:** whether it halts. The rules for MID and k from phase to phase, and a proof of the phase step, are not known.

## For later

The doubling map at the left end (see above) is the place to start: find how MID and k change from one phase to the
next, prove the phase step with `bbtools.symtm` (with m, j and s as variables), and look for the inner counter that
makes the time between visits double.

Not known: the counter's digits and carry rule, and whether `F>1 1 1 0 1 0` can arise. Tools that should help: `tools/py/bbtools/explore.py` (`events`, `tokens`), `bbtools.macro`, and for proved rules `bbtools.symtm.prove`.

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LF_0RC0RB_0LD1RB_1LE0LB_0LA1LC_0LB---/lean/check.sh
gcc -O2 -o /tmp/tmrun tools/c/tmrun.c && /tmp/tmrun 1RB1LF_0RC0RB_0LD1RB_1LE0LB_0LA1LC_0LB--- 10000000000
cd tools/py && python3 -m bbtools.ctl 1RB1LF_0RC0RB_0LD1RB_1LE0LB_0LA1LC_0LB--- 5
```

## Pages

- [`pages/holdouts/1RB1LF_0RC0RB_0LD1RB_1LE0LB_0LA1LC_0LB---/explainer.html`](../../pages/holdouts/1RB1LF_0RC0RB_0LD1RB_1LE0LB_0LA1LC_0LB---/explainer.html)
- [`pages/holdouts/1RB1LF_0RC0RB_0LD1RB_1LE0LB_0LA1LC_0LB---/proof-status.html`](../../pages/holdouts/1RB1LF_0RC0RB_0LD1RB_1LE0LB_0LA1LC_0LB---/proof-status.html)
