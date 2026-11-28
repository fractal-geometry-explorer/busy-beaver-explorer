# 1RB---_0RC0LA_1LD0RB_1LE0LF_1RC1LF_0LC0LB

bbchallenge id 49413. One of the six-state holdouts whose halting from blank tape is open.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | --- |
| B | 0RC | 0LA |
| C | 1LD | 0RB |
| D | 1LE | 0LF |
| E | 1RC | 1LF |
| F | 0LC | 0LB |

**Family:** Nested ternary counter (segments drained at rates 2*3^j, mirrored pair).

A nested ternary counter like a draining odometer: segments of 111-blocks near the growing end lose 2*3^j blocks per cycle while new segments are made at the far end; it survives the collapses seen so far and does not halt in 10^19 steps (accelerated simulation).

## Equivalence

`1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD` (c2, id 5788) and `1RB---_0RC0LA_1LD0RB_1LE0LF_1RC1LF_0LC0LB` (c1, id 49413) are mirror images: swap left and right in c1 and relabel A->E, B->D,
C->A, D->B, E->C, and you get c2's table. So c1 from blank is c2 mirrored and started in state E. They follow the
same law with different numbers; the scripts are in `holdouts/1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD/py/` and `holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/c/`.

## What it does

At each step where the head writes a new cell at the growing end (the right end for c2, the left end for c1), the
tape read from the far end, as lengths of runs of 1s (single 0s left out), is

    6 3^x1 9 3^x2 9 ... 9 3^xm  TAIL

blocks `111` separated by single 0s, cut into segments by markers `1^9`. The head sweeps the whole tape (11 shift
rules in `lean/Rules.lean`). These moments come in cycles of three.

## The map (partial)

Between collapses, per cycle the segment j places from the growing end loses 2*3^j blocks (6, 18, 54, 162, ...),
like an odometer turned backwards, with occasional off-by-one irregularities next to the junk at the ends; new,
large segments of the form a*3^k - 2 are made at the far end. When a segment near the growing end runs out the last
segments merge (a collapse) and the drain starts again with fewer segments. The rule at the far end and at
collapses is not pinned down, so this is not yet a complete map. Segments next to the growing end of c2 in the macro
run (from the growing end):

| step | last four segments |
|---|---|
| 2.30e15 | 47 143 3833 5717 |
| 2.72e16 | 22 65 3599 5015 |
| 2.90e17 | 3 7 3425 4493 |
| 3.00e17 | 3399 4405 23281 180681 (after a collapse) |
| 9.06e18 | 3353 4271 22879 179475 |

c1 had its collapse near 2e12 steps and at 3.6e18 has `371 43406 155472 33394`.

## Halting condition

Not known. Halting needs the head in state B on a 1 with a 1 to its left (B1 -> 0LA, A1 halts); inside the draining regime this does not occur, and what a collapse does in general is not known.

## How far

The macro simulator `holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/c/msim.c` (4-cell blocks, two-block window, whole runs crossed in steady state,
exact 128-bit step counts, checked against `tools/c/tmrun.c` by `py/check_msim.py`) runs both machines to 1e19 steps
without a halt: `data/c2_msim.txt` ends at 10,000,000,000,378,843,465 and `data/c1_msim.txt` at
10,000,000,002,400,213,340.

At the end, c2's next collapse is the 4,261-block segment (18 per cycle), about 240 cycles away; c1's is the
370-block one (6 per cycle), about 62 cycles away. Cycles have been getting longer by a factor of about 2 on
average, so these lie near 1e38 steps (c1) and far beyond (c2): heuristic estimates only.

## Reproduce

```sh
gcc -O2 -o msim holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/c/msim.c
./msim 1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD 4 1e19 - 1          # c2, snapshot at each fresh block on the right
./msim 1RB---_0RC0LA_1LD0RB_1LE0LF_1RC1LF_0LC0LB 4 1e19 - 1 l        # c1, on the left
python3 holdouts/1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD/py/cmap.py c2 4.5e9   # the draining law on the direct run
python3 holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/check_msim.py 2e9
```

## Further work

The far-end generator and the collapse rule, which would make the map complete and let it be iterated past the next
collapses; then a Lean proof of one cycle of the drain from the shift rules.

## Long accelerated run (16 November 2026)

This machine was part of a halt hunt on the nested ternary counters (with 1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---
and 1RB0LC_1LA0RD_1RA0LA_1RE1RD_1RA1RF_1LC---). The time went to those two machines, and this one got no new long
run. The only new check was a list of the right-end D events of 1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD up to
10^13 steps with the record-printing macro simulator
`holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/c/msimev.c`, which showed no halt; no law was derived from it.
The bound stays at 10^19 steps (above), and no halt was found. The general-law method used for the b machines
(event law, collapses run exactly on reduced tapes and spliced back in, in
`holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/track.py`) is the natural next step here too.

## The bouncing end is one ternary counter (24 November 2026)

**Result.** The whole run is one ternary counter that drains, and it now has an exact model. Every bounce of the
head at the bouncing end (the left end of 1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD, the right end of its mirror
image 1RB---_0RC0LA_1LD0RB_1LE0LF_1RC1LF_0LC0LB) adds one to the counter. This gives a closed rule for each bounce.
The rule is proved in Lean for any number of carry digits (`lean/Chain.lean` (this folder)).
An exact accelerator built on it follows both runs through the collapses the older sections forecast:
1RB---_0RC0LA_1LD0RB_1LE0LF_1RC1LF_0LC0LB at 1.1x10^32 steps and 1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD at
6.0x10^65 steps. Neither halts there. Both runs went on to about 10^100 steps with no halt. The best bounds are still
the region-memo runs of 18 November (3.88x10^196 and 4.29x10^179 steps, `holdouts/regaccel.json`). Halting is still
open.

The scripts and data named below are in the folder of 1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD.

**The digit model** (`holdouts/1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD/py/cdigits.py`, in the folder of 1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD). Read
1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD mirrored, so that the counter is on the right as it is in
1RB---_0RC0LA_1LD0RB_1LE0LF_1RC1LF_0LC0LB. A *sample* is the head on a new rightmost cell in state D (state B for
1RB---_0RC0LA_1LD0RB_1LE0LF_1RC1LF_0LC0LB), with `100` just left of it. The tape is then

    0^inf  [r_1]W_1 [r_2]W_2 ... [r_n]W_n  (1000)^L 100  head

A digit `[r]W` is a run of r blocks `1000` followed by a wall: Z = `101010` (digit 0), O = `10` (digit 1),
T = `100000` (digit 2). At the far end there is a small gadget of other walls (`b1_2`, `b1_4`, `b2_1`, `b2_3`).
Each sweep from one sample to the next is a symbolic run of the machine, cached by the window's shape. Check:
`CMACH=c2 python3 py/cdigits.py check 3e7` compares every sample of the direct run with the model: 3,851 sweeps for
1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD and 4,049 for its mirror, with no mismatch.

**The counter rule.** A sweep is one ternary increment, with the head's end least significant. The carry turns the
trailing T digits into Z digits and raises the first Z or O digit (the stop) by one. The runs then change as follows:

* stop on O: the stop digit's run loses 1 block;
* stop on Z: the run of the digit just below the stop gains 1 (the last run L if the stop is the bottom digit);
* the last run L always gains 1;
* steps = 10 x (sum of the runs of the carry digits) + 28 x (number of carry digits) + 10 L + 42.

`sweepZ` and `sweepO` in `lean/Chain.lean` (this folder) prove this on the machine
for every list of carry digits (at least one) and every run length. Each proof is put together from six pieces
proved by `bbtools.symtm` (`py/chain_lean.py`).

**Why the digits drain.** A digit loses one block each time the carry stops on it as an O, which is once every 3 of
its own increments. It gains one block when a carry passes out of it into a Z digit, which is once every 9. So each
digit loses 2 blocks for every 9 increments it receives. In the right-end view of the older sections, the digits are
the segments. The digit j places from the far end counts up 3^j times per far-end cycle, which is the drain of
2*3^j blocks per cycle. The last run L grows by about 4/3 per sweep. When the whole counter overflows into the far
gadget, L becomes a new digit at the bottom. A digit that runs out triggers a collapse. Two kinds were seen:
* At the far end, the empty digit merges into its neighbours: 1,931 + 0 + 10,064 became one digit of 11,995 blocks.
* In the middle, a gadget (`[y]b2_3`, `[y]O [0]b2_1`, `[y]O [0]b1_2`) takes the carries of the digits below it and
  eats y while the digits below go on counting.

**The accelerator** (`py/oacc.py`). It uses two exact ingredients:
* The counter rule in closed form. The increments that take the bottom p places from all Z to all T compose to a
  translation of the runs, with a step count affine in them. So any number of increments short of a carry out of
  the bottom block costs O(digits) work.
* Cycle jumps. When the sequence of shapes of the macro steps repeats twice, each step of the period is the same
  rule. M more periods are then done at once, for the largest M that keeps every big run at least 64 at every phase.

Everything else is a symbolic sweep. Checks:
* `OMAXM=300 python3 py/oacc.py test 1e6 6000000` (and with `c1`) compares every jump and cycle jump with plain
  sweeps, states and step counts: 11,513 and 4,945 of them over 6 million sweeps, all equal.
* `py/directcheck.py` builds the tape of an accelerated state and compares it cell for cell with a direct run of
  `c/at.c` to the same step. It matched at 1.13x10^11 steps (1,228,170 cells) for
  1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD, and at 3.2x10^10 and 9.7x10^9 steps for its mirror.

**The collapses that were forecast.** The older sections forecast the next collapses near 10^38 steps (the
370-block segment of 1RB---_0RC0LA_1LD0RB_1LE0LF_1RC1LF_0LC0LB) and "far beyond" 10^19 (the 4,261-block segment of
1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD). Both are the top digits of the counter.

| machine | event | steps | far end before | far end after |
|---|---|---|---|---|
| 1RB---_0RC0LA_1LD0RB_1LE0LF_1RC1LF_0LC0LB | top digit runs out, absorbed by the gadget | 1.08x10^32 to 1.14x10^32 | `[0]b2_1 [0]Z [1]Z [42297]Z` | `[0]b2_1 [0]O [42291]Z [152123]Z` |
| 1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD | the second digit drains 2 per far-end event from 1.78x10^65, reaches 0, and merges | 5.79x10^65 to 6.03x10^65 | `[0]b2_1 [1931]Z [0]Z [10064]Z` | `[0]b1_2 [11994]Z [141020]Z` |

Both far ends then return to the usual cycle of the gadget (`b1_2`, `b1_4`, `b2_1`, `b2_3`). The digit lists at each
new power of 10 are in `data/c2_oacc_decades.txt` and `data/c1_oacc_decades.txt`. The far end through each collapse
is in `data/c2_collapse_6e65.txt` and `data/c1_collapse_1e32.txt`, written by `py/events.py`. At about 10^100 steps
the counters have 103 to 104 digits. No sweep came near the halting transition. If a symbolic sweep halted, the run
would stop with `rule halt`.

**What comes next (fits, not proofs).** For 1RB---_0RC0LA_1LD0RB_1LE0LF_1RC1LF_0LC0LB the third digit from the far
end has 10,607 blocks at 1.76x10^100 steps and loses 162 per power of 10. It runs out near 10^165, which is below the
region-memo bound of 4.29x10^179, so that run has probably already passed through it. For
1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD the top digit (11,054 blocks at 1.43x10^101, about 24 fewer per power of
10) runs out first, near 10^560.

**What a proof would need.** The rule and the collapses seen so far suggest a self-similar run, but a proof needs a
set of digit lists that is closed under every sweep, the gadget rules and the collapses included. That is the same
open step as for the b machines (1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---, section of 21 November).

Reproduce (in the folder of 1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD):

    CMACH=c2 python3 py/cdigits.py check 3e7; CMACH=c1 python3 py/cdigits.py check 3e7
    OMAXM=300 python3 py/oacc.py test 1e6 6000000 [c1]
    OEVENTS=/tmp/c2ev.txt python3 py/oacc.py run 1e6 3600 /tmp/c2state.txt [c1]     # resumable from the state file
    python3 py/events.py decades /tmp/c2ev.txt
    gcc -O2 -o /tmp/at c/at.c && python3 py/directcheck.py /tmp/at c2 "$(awk '$2>6e10 && $2<1.2e11' /tmp/c2ev.txt | tail -1)"
    python3 py/chain_lean.py --check; . /etc/profile.d/lean.sh && ../1RB---_0RC0LA_1LD0RB_1LE0LF_1RC1LF_0LC0LB/lean/check.sh

`py/tacc.py` and `py/caccel.py` are the b machines' counter-macro accelerator pointed at this digit model. It passes
its test (`python3 py/tacc.py test 1e6 300000`: 24,516 landing points equal) but is slower than `py/oacc.py` here,
because of the gadget in the middle.

## What is proved, and how firmly

| level | claim | where |
|---|---|---|
| kernel | **The halting configurations.** The machine stops exactly when it reads the symbol of a halting transition (A1); the generated statement covers every configuration. | `step_none_iff`, `lean/Blank.lean` |
| kernel | **No halt in the first 10,000 steps.** The list simulator of the shared library, proved to agree with the machine's semantics, runs 10,000 steps from blank tape without a halt, evaluated by Lean's kernel. | `blank_runs_kernel`, `lean/Blank.lean` |
| native | **No halt in the first 10^7 steps.** The same run, evaluated by compiled code. | `blank_runs_native`, `lean/Blank.lean` |
| trusted | **No halt in the first 10^9 steps.** The C simulator `tools/c/triage.c` runs 10^9 steps without a halt; at the end 83,545 cells have been visited and 55,654 of them hold a 1. | `holdouts/triage.json` |
| heuristic | **Growth shape: exp/sqrt.** Left of the start, the visited part of the tape grows like the logarithm of the step count: each new cell costs a roughly constant factor more time, the signature of a counter or of a Collatz-like map whose values are written on the tape (fitted exponent 0.058). Right of the start it grows like the square root of the step count, the signature of a head sweeping back and forth across the whole tape and adding a cell or a few at the end of each sweep (a bouncer-like shape) (fitted exponent 0.466). | `tools/py/bbtools/triage.py` |
| kernel | **11 shift rules.** For every n, the head crosses n copies of a short word in a fixed number of steps per copy and leaves another word behind (for example the head going right over `1011` and leaving `0010`, 18 steps a copy; these cross the 111-blocks of the counter). Generated and proved by `bbtools.symtm`, checked by Lean's kernel. | `lean/Rules.lean`, generated by `holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/rules.py` |
| trusted | **No halt in the first 10^19 steps.** A macro simulator (blocks of 4 cells, crossing long runs of equal blocks in one go; it agrees with the direct simulator at 2x10^9 steps) runs 10,000,000,002,400,213,340 steps without a halt, through the collapses at about 2x10^12. | `holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/c/msim.c`; output in `holdouts/1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD/data/c1_msim.txt` |
| heuristic | **The draining law.** Between collapses, the segment j places from the growing end loses 2*3^j blocks per cycle (6, 18, 54, 162, ... per sampled cycle of the macro run), with occasional off-by-one irregularities at the junk near the ends. It is checked on the cycles of the direct run to 4.5x10^9 steps (failing exactly at the collapses) and on the macro run to 10^19; the far-end rule that makes new segments is not pinned down. | `python3 holdouts/1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD/py/cmap.py c1` |
| heuristic | **The next collapse.** At 10^19 steps the three segments next to the growing end hold 370, 43,402 and 155,460 blocks; the 370 runs out first, after about 62 more cycles; cycles have been getting longer by a factor of about 2 on average, which puts that collapse near 10^38 steps. | `holdouts/1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD/data/c1_msim.txt` |
| trusted | **No new long run (16 November 2026).** The bound stays at 10^19 steps. | |
| kernel | **The counter sweep, for every number of carry digits.** `sweepZ` and `sweepO`: from a sample, any list of T digits and a Z or O stop digit, the machine reaches the next sample with the T digits turned into Z digits (same runs), the stop raised by one, the run changes of the counter rule, in 10 per block of the chain and of the last run, 28 per chain digit, plus 42 steps. Six pieces proved by `bbtools.symtm`, joined by induction over the list (24 November 2026). | `lean/Chain.lean` of 1RB---_0RC0LA_1LD0RB_1LE0LF_1RC1LF_0LC0LB, generated by `holdouts/1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD/py/chain_lean.py` |
| trusted | **The digit model is exact on the direct run.** Every sample (a new cell at the bouncing end in state D, or B in the mirror) of the direct run to 3x10^7 steps equals the model: 3,851 sweeps (1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD) and 4,049 (1RB---_0RC0LA_1LD0RB_1LE0LF_1RC1LF_0LC0LB), no mismatch. | `CMACH=c2 python3 holdouts/1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD/py/cdigits.py check 3e7` |
| trusted | **The accelerator is exact.** Every closed-form counter jump and cycle jump of `py/oacc.py` equals plain sweeps (11,513 and 4,945 over 6x10^6 sweeps); accelerated states equal the direct run cell for cell at 1.13x10^11 steps (1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD) and at 9.7x10^9 and 3.2x10^10 steps (1RB---_0RC0LA_1LD0RB_1LE0LF_1RC1LF_0LC0LB). | `holdouts/1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD/py/oacc.py test`, `holdouts/1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD/py/directcheck.py` |
| trusted | **Through the forecast collapses, to about 10^100 steps.** The run of 1RB---_0RC0LA_1LD0RB_1LE0LF_1RC1LF_0LC0LB passes its top digit running out at 1.1x10^32 steps; the run of 1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD passes the merge of its top digits at 6.0x10^65 steps; both go on to about 10^100 steps (103 to 104 digits) without a halt (24 November 2026). | `holdouts/1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD/data/c?_oacc_decades.txt`, `holdouts/1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD/data/c?_collapse_*.txt` |
| heuristic | **The next collapses.** 1RB---_0RC0LA_1LD0RB_1LE0LF_1RC1LF_0LC0LB: the third digit (10,607 blocks at 1.76x10^100, 162 fewer per power of 10) runs out near 10^165. 1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD: the top digit (11,054 blocks at 1.43x10^101, about 24 fewer per power of 10) near 10^560. Fits of the drain, not proofs. | `holdouts/1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD/data/c?_oacc_decades.txt` |
| open | **Does it halt from blank tape?** Not known. Halting needs the head in state B on a 1 with a 1 to its left (B1 -> 0LA, A1 halts); inside the draining regime this does not occur, and what a collapse does in general is not known. |  |

## Lean

`lean/Rules.lean` is generated by `holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/rules.py` (one script for all eight machines of this worker;
`--check` compares the files instead of writing them) and is listed in `lean/check.sh` after `Blank.lean`, followed by `lean/Chain.lean` (the counter sweep for every number of carry digits, generated by `holdouts/1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD/py/chain_lean.py`):

```sh
. /etc/profile.d/lean.sh && holdouts/1RB---_0RC0LA_1LD0RB_1LE0LF_1RC1LF_0LC0LB/lean/check.sh
python3 holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/rules.py --check
```

## Pages

- [`pages/holdouts/1RB---_0RC0LA_1LD0RB_1LE0LF_1RC1LF_0LC0LB/explainer.html`](../../pages/holdouts/1RB---_0RC0LA_1LD0RB_1LE0LF_1RC1LF_0LC0LB/explainer.html)
- [`pages/holdouts/1RB---_0RC0LA_1LD0RB_1LE0LF_1RC1LF_0LC0LB/proof-status.html`](../../pages/holdouts/1RB---_0RC0LA_1LD0RB_1LE0LF_1RC1LF_0LC0LB/proof-status.html)

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD`](../1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD/README.md): rename A→E, B→D, C→A, D→B, E→C, F→F and exchange left and right; it is this table started in state C, in a mirror
- [`1RB1LD_1LC0RE_1LA0LD_0LB0LE_0RB0LF_1RE---`](../1RB1LD_1LC0RE_1LA0LD_0LB0LE_0RB0LF_1RE---/README.md): rename A→F, B→E, C→B, D→C, E→A, F→D; it is this table started in state E
- [`1RB0RF_1LC1RF_1RA0LD_0LC0RE_1LD---_0RC0RD`](../1RB0RF_1LC1RF_1RA0LD_0LC0RE_1LD---_0RC0RD/README.md): rename A→E, B→D, C→C, D→A, E→B, F→F and exchange left and right; it is this table started in state D, in a mirror

<!-- end of related machines -->
