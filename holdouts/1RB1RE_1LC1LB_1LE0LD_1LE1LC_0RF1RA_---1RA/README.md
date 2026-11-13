# 1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_---1RA

bbchallenge id 175628. One of the six-state holdouts whose halting from blank tape is open (group G07).
Family: **3/2 counter feeding a stack of slower counters**. Decision: **open**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RE |
| B | 1LC | 1LB |
| C | 1LE | 0LD |
| D | 1LE | 1LC |
| E | 0RF | 1RA |
| F | --- | 1RA |

## What it does

Read the tape as runs of 1s separated by single 0s, left to right; `u` is a run of length 1 (cells `10`, a *unit*).
The right end of the tape never moves (it has been `... 4 u^3 4 1` since step 1.8·10^5); all the work is done by the
head near the **left** end, which it visits in state B reading the 0 just left of the tape. There the tape is

    [X, 4, u^n, L]        X a long run, then a run of 4, a block of n units, then a list L of short runs.

Two moves are **proved in Lean** (`lean/Rules.lean`, all values of the counts, any tape `R` to the right):

    sweep    [X, 4, u^(n+2), R]  ->  [X+6, 4, u^n, R]               (X = 2x+2, 4x+36 steps)
    convert  [2x+8, u^(k+2), R]  ->  [6, 4, u^x, 4, u^k, R]         (4x+74 steps)

So an **epoch** runs about m/2 sweeps (X grows to about 3m), and then the long run is
converted back into about 3m/2 units. What happens between the last sweep and the conversion depends on the parity
of m and on the first items of L, and changes those items. Measured over 83 epochs (to 7·10^29 steps, `py/epochs.py`):

    m' = 3m/2 + d,    d in {-2, +1, +4} for m even,  d in {-1/2, +5/2} for m odd,

and an epoch takes about 1.5 m^2 steps (the ratio is 1.500 to four digits from m = 10^4 on). The m sequence:
1, 4, 7, 10, 13, 22, 31, 49, 73, 109, 163, 244, 370, 553, 829, 1243, 1864, 2797, 4195, 6292, 9436, ...,
780,830,244,113,908 (epoch 83, step 7.3·10^29).

**The list L is a stack of slower counters.** Its first item behaves like a smaller copy of the top level: a run r
followed by units grows by 6 and loses one unit per epoch of odd m (`18 u^8 -> 24 u^7 -> 30 u^6 -> 36 u^5 -> 42 u^4`),
and when its units run out it is itself converted into about r/2 units (`42 u^4 ... -> 9 u^19 ...`), eating from
the item after it. Deeper items change exponentially more rarely; the bottom of the stack freezes:

    step 1.8e5:   2 4 u^370  4 u^17 4 u^3 4 1
    step 1.1e8:   2 4 u^9436 9 u^25 4 u^4 4 u^3 4 1
    step 8.0e11:  2 4 u^816400 4 u^22 4 u^15 4 u^4 4 u^3 4 1
    step 7.3e29:  2 4 u^780830244113908 9 u^3 12 4 u^14 4 u^2 4 u^2 4 u^3 4^2 u^2 15 u^5 4 u^9 4^2 u^3 4 u^17 4 u^15 4 u^4 4 u^3 4 1

(these are the tapes at the start of an epoch, sampled in state E at the left end while the long run is only 2
long, 30 steps before the visit in state B that reads `[6, 4, u^(m-2), L]`; m above is counted the same way). The list grows by
about one item every three epochs (29 tokens at epoch 83).

## Where it can halt

The halting transition is F0. A closed tape language from windows of 4 cells (`lean/EdgeCert.lean`, checked by
`decide` in `lean/Edge.lean`) shows that **it halts from blank tape exactly when F steps onto the blank region past
the right end of the tape** (`halts_iff_edge`). Since all the work happens at the left end, a halt needs the whole
stack L to be used up, a cascade that would have to reach the frozen bottom items.

## Status

Open.

- **Kernel:** `step_none_iff`, `blank_runs_kernel` (`lean/Blank.lean`); `sweep`, `convert` (`lean/Rules.lean`);
  `halts_iff_edge` (`lean/Edge.lean`). **native_decide:** `blank_runs_native` (10^7 steps).
- **Trusted computation:** the epoch list above, from `py/epochs.py` (the macro simulator with proved cycle jumps of
  `tools/py/bbtools/cycles.py`, exact step counts), to 10^30 steps; no halt. It agrees with a direct C run on the
  epochs below 10^9 steps.
- **Heuristic:** the stack grows and its bottom freezes, so a halt (the stack used up) looks unlikely; the parity
  sequence of m that drives the stack looks random, so this is a probabilistic, Collatz-like question.
- **Open:** the epoch-end rules for every (parity, first items of L) case, which would turn the description into an
  exact map on (m, L).

## Next steps

Enumerate the epoch-end cases with `bbtools.symtm` (a long run `(11)^x`, the parity of the unit block, and the first
two or three items of L as symbolic runs), which would make the map on (m, L) exact; then look for an invariant of
the stack that rules out its being emptied.

## Pages

- [`pages/holdouts/1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_---1RA/explainer.html`](../../pages/holdouts/1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_---1RA/explainer.html)
- [`pages/holdouts/1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_---1RA/proof-status.html`](../../pages/holdouts/1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_---1RA/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_---1RA/lean/check.sh
cd holdouts/1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_---1RA
python3 py/rules.py | diff - lean/Rules.lean
(cd ../../tools/py && python3 -m bbtools.ctl 1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_---1RA 4 lean H175628 Blank) | diff - lean/EdgeCert.lean
python3 py/epochs.py 1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_---1RA 2 1e30 E L "pre:2 4 1^"     # epoch starts, ~1 min
```
