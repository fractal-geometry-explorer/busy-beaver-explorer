# 1RB1LC_1LA1RE_0RD0LA_---1LB_1LD0RF_0RE1RB

bbchallenge id 56057. One of the six-state holdouts whose halting from blank tape is open. Family: **binary counter moving a marker through a word**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LC |
| B | 1LA | 1RE |
| C | 0RD | 0LA |
| D | --- | 1LB |
| E | 1LD | 0RF |
| F | 0RE | 1RB |

## What it does

Each time the head, in state C, is at the left end reading `0 1 0` (an **overflow event**), the tape from the head on
is `C>0 (1 0)^z W` with W a word of odd blocks of 1s separated by single 0s. Read in pairs of cells (`1 0` = digit 0,
`1 1` = digit 1) the tape is a string of binary digits, and `(1 0)^z` is a run of z zero digits.

**Two counters on one clock.** Between two events the head shuttles around a point near the left end of W. Each
shuttle (a *tick*) adds one to a binary counter L on its left (the z digits of the prefix, written in pairs of cells
`0 0` / `1 1`, least significant digit next to W) and one to a binary counter R inside W (its least significant bit
next to the shuttle point): the turning points of the head left of the point follow the ruler sequence of L and those
right of it the ruler sequence of R. An event is an overflow of L: L has counted 2^z ticks, it is reset and gets one
more digit (z -> z + 1).

**The overflow law.** So at each event R has gained exactly 2^z. In W the bits of R sit at fixed digit positions
(slots), mostly 3 digits apart (`11b`, b the bit), with a few separating stretches between them. Running one event
again with every z from 0 to 16 (`py/overflows.py slots`) shows it directly: the next event has W changed by exactly
one binary carry that starts at slot z (digits p1 < ... < pk, 1 -> 0 at all but the last, 0 -> 1 at the last). In the
run, 55 of the 106 pairs of consecutive events up to 2·10^9 steps are such carries (`py/overflows.py check`); the
others are the restructures and the carries through the separating stretches just after them, which also rewrite
some separator digits.

**The marker.** Late in an epoch only the top bits move: W = P `111110` (`110`)^b `111`, where `110` is a 0 bit,
`111110` is the single 1 bit of the high part (the **marker**, cells `1^11 0`) and `111` is the end. Each event moves
the marker one block right (b -> b − 1), and the gap between events obeys **D' = 2D + 2** exactly (all 23 pairs of
consecutive marker moves in the first 5·10^10 steps).

**Restructures.** When R overflows (the marker meets the end) the word is rebuilt and z starts again. Started from one
event with different z, the restructure comes after the same number of steps for every z large enough, so it is
triggered by R, not by L; what it writes depends on z (L's digits are copied into the new word). In the first 10^11
steps the last three restructures came at steps 17,682,600 (102 digits), 5,745,422,543 (131) and 49,800,461,566
(163). At step 96,162,430,390 the run is at z = 30 with 192 digits.

The machine halts only in state D reading a 0. From configurations of the same shape with random short words it often
halts within a hundred steps (`D>0 1` at the right end), so non-halting depends on the words the run writes.

## Status

Open. Proved in Lean (kernel): the halting configurations and no halt in 10,000 steps; with `native_decide`: no halt
in 10^7 steps. Computed (trusted C and Python): no halt in 10^11 steps; the overflow events and their carry law as
above. Not proved: any of the counter laws for all parameters (the tick of L and R is a sweep of several hundred steps
with a dozen intermediate shapes, not decoded into shift rules yet).

## How far it was run

Direct C simulation to 10^11 steps (z = 30, the fourth recorded epoch). With the marker law (`py/overflows.py
predict` on the events of an epoch whose marker is in the periodic tail) the end of an epoch can be placed exactly
from its last two events, since each further event is one doubling (D' = 2D + 2); the restructure itself is not
predicted, so the macro run stops at the end of the current epoch.

## What is established

**Proved in Lean, kernel only** (`lean/Blank.lean`): the halting configurations (`step_none_iff`); no halt in 10,000
steps (`blank_runs_kernel`).

**Proved in Lean with `native_decide`**: no halt in 10^7 steps (`blank_runs_native`).

**Computed** (trusted C): no halt in 10^11 steps (`tools/c/tmrun.c`; 385 cells, 312 ones). All 144 overflow moments
of the run have the shape `(1 0)^z W` with W of odd blocks; z rises by one between them except at 16 restructures.

**Computed** (Python, `py/overflows.py`): the carry law at 55 of the 106 event pairs to 2·10^9 steps; the slot map of
one event for z = 0..16; 96 carries among the 162 event pairs to 5·10^10 steps; the gap law D' = 2D + 2 at all 23 pairs of
consecutive marker moves to 5·10^10 steps.

**Heuristic**: the two counters on one clock (from the ruler sequences of the head's turning points); random words of
the same shape halt quickly.

**Open**: the tick in shift rules, the restructure rule, why the run's words are safe, and the question.

The closed-tape-language search (`bbtools.ctl`, K up to 6) does not confine the halt to an edge: it allows `D>0 1` with
blank beyond, one cell from the right end.

## Open questions

* Decode one tick (a sweep of L's last digit and R's last bit, then the carries) as shift rules and prove them in
  Lean; that would make the overflow law a theorem `(z, R) -> (z + 1, R + 2^z)` for all z.
* The restructure: it is set off by R's overflow at a time fixed by R, and copies L. A rule for it, as a function of
  (z, L, W), would give an epoch-to-epoch map and an accelerated run over many epochs.
* Which words reach the halting configuration `D>0 1` at the right end, and whether a restructure can write one.

## Layout

| path | what it is |
|---|---|
| `lean/Machine.lean`, `lean/Blank.lean` | the machine, the halting configurations and bounded runs (generated) |
| `py/overflows.py` | the overflow events as (z, W), the carry law check, the slot experiment, the end-of-epoch prediction |
| `py/tmsim.py` | a plain simulator started from a given tape, run to the next event |

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LC_1LA1RE_0RD0LA_---1LB_1LD0RF_0RE1RB/lean/check.sh
gcc -O2 -o tmrun tools/c/tmrun.c && ./tmrun 1RB1LC_1LA1RE_0RD0LA_---1LB_1LD0RF_0RE1RB 100000000000 records 100000
./tmrun 1RB1LC_1LA1RE_0RD0LA_---1LB_1LD0RF_0RE1RB 2000000000 at C L 1000 > ev.txt
python3 holdouts/1RB1LC_1LA1RE_0RD0LA_---1LB_1LD0RF_0RE1RB/py/overflows.py check ev.txt
python3 holdouts/1RB1LC_1LA1RE_0RD0LA_---1LB_1LD0RF_0RE1RB/py/overflows.py slots ev.txt 17857444 0 17
```

## Pages

- [`pages/holdouts/1RB1LC_1LA1RE_0RD0LA_---1LB_1LD0RF_0RE1RB/explainer.html`](../../pages/holdouts/1RB1LC_1LA1RE_0RD0LA_---1LB_1LD0RF_0RE1RB/explainer.html)
- [`pages/holdouts/1RB1LC_1LA1RE_0RD0LA_---1LB_1LD0RF_0RE1RB/proof-status.html`](../../pages/holdouts/1RB1LC_1LA1RE_0RD0LA_---1LB_1LD0RF_0RE1RB/proof-status.html)
