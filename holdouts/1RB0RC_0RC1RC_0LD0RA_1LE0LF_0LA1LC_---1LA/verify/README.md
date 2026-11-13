# Independent check of `1RB0RC_0RC1RC_0LD0RA_1LE0LF_0LA1LC_---1LA`

Everything in this folder was written from scratch for this check. `py/closure/` and its notes were **not**
read; `tools/py/bbtools` was not used either (the transition table is parsed directly from the bbchallenge
string in each program).

`C(r)` below is the configuration of the claim: state E, head on a blank cell, only blanks to its left, and
to its right `(1011001)^59 1011 00000 1101100110110 (011)^16 001101100110 (011)^r`, then blanks.

## Verdict

| claim | result |
|---|---|
| (b) blank tape reaches `C(16,797,709)` at step 1,818,198,163,340,705 | **confirmed** (exact step, exact tape, head, state) |
| (a) `C(r)` reaches `C(r + 321,042,928)` after `650373336347246654 + 4382930856*(r-65)` steps, no halt | **confirmed numerically** for every r listed below (exact step, exact tape). **Not proven for all odd r** by this tool |
| (c) `C(r)`, r even, halts | **confirmed** for the r listed below. The halting transition is step number `claimed + 1`: the claimed number counts the steps *before* the halting transition (convention offset, not a mismatch in the dynamics) |

No mismatch of any cell, head position, state or step count was found, apart from the +1 convention in (c).

### Numbers

Claim (b): from the blank tape, after exactly 1,818,198,163,340,705 steps the configuration is `C(16797709)`
(non-blank span 50,393,622 cells). Obtained twice: with nested rules, and with nested rules switched off
(`-nonest`, 1,693,791,389 macro steps, about 4.5 minutes).

Claim (a), each line = "started from `C(r)`, ran exactly T steps, result compared cell by cell with `C(r+321042928)`":

| r | T | result |
|---|---|---|
| 65 | 650,373,336,347,246,654 | identical to `C(321,042,993)` |
| 67 | 650,373,345,113,108,366 | identical to `C(321,042,995)` |
| 16,797,709 | 723,996,248,542,949,918 | identical to `C(337,840,637)` |
| further odd r | formula value | see "Extra values" at the end of this file |

Claim (c), run with no step limit until the machine halts (state F reading 0):

| r | claimed | halting transition is step no. |
|---|---|---|
| 64 | 21,481,836,136,725,388 | 21,481,836,136,725,389 |
| 66 | 21,481,837,746,590,860 | 21,481,837,746,590,861 |
| further even r | formula value | see "Extra values" |

The slope 804,932,736 per unit of r is reproduced exactly.

## How to run

    ./run_all.sh                 # compiles, validates against plain simulation, checks (b), (a) r=65,67,16797709, (c) r=64,66
    EXTRA_A="69 71" EXTRA_C="68" ./run_all.sh
    ./check_a.sh 65              # one value of claim (a)
    ./check_c.sh 64              # one value of claim (c)
    ./sim3 -nonest 1818198163340705 > b.txt ; python3 cmp.py sim:b.txt C:16797709    # (b) without nested rules

`run_all.sh` takes about 1.5 minutes on one core (40 s of it is the plain 1e10-step run); the log of the last
run is `run_all.log`. `sim3 T [STATE word^n ...]` runs exactly T steps (from the blank tape, or from the given
tape with the head on its first cell) and prints the tape as run-length words; `cmp.py` compares two tapes
exactly without expanding the runs.

## The tool (`sim3.cpp`)

* **Level 1.** The tape is a run-length list of 21-cell words (21 = lcm of the periods 3 and 7 that occur).
  A word rule (state, direction, word) is computed by plain simulation confined to the word. If the head
  leaves on the far side in the same state, the rule is applied to all n copies at once.
* **Level 2 and nested.** When the tape shape recurs, a rule "this shape with counts y becomes the same shape
  with counts y + d, for all y in a box (lower/upper bounds and congruences)" is proven by re-simulating once
  with symbolic counts (linear forms with exact rational coefficients). An operation is performed in the proof
  only if it is valid for every y in the box; whatever inequality or congruence it needs is added to the box.
  Proven rules may be used inside later proofs. A proven rule is applied k times in one jump, with k the
  largest number of applications that keeps the counts in the box, and the step total is the exact closed sum.
* Hashes are used only to pick candidate rules; a rule is applied only after its full pattern and box are
  checked against the tape.
* **Exact stop.** A run to step T never overshoots: a jump is cut to the largest k that fits, and the last
  steps are done cell by cell. So "configuration at step T" is literal.
* The halting transition is counted as a step (bbchallenge convention).

## What was validated

Identical tape, head position and state versus the plain cell-by-cell simulator `plain.cpp`:

* blank tape at steps 1,000; 123,456,789; 3,000,000,000; 10,000,000,000;
* `C(65)` at steps 777,777 and 2,000,000,000.

Claim (b) was reproduced with the nested rules disabled, so the two acceleration layers agree with each other
over 1.8e15 steps.

## What remains unverified

* **Claim (a) for all odd r >= 65.** I tried a symbolic run with the number of `(011)` blocks left free
  (`sim3 -sym ...`). It does not generalise: the order in which counts run out depends on r, and following the
  actual path pins the free count to its actual value (the admissible box collapses to one point). So this
  tool gives exact numerical confirmation for the listed r only. The claimed formula was correct for every r
  tried, including one seven orders of magnitude away from the others.
* **Claim (c) for all even r >= 64**: same situation, listed values only.
* The accelerated runs beyond 1e10 steps rest on the correctness of `sim3.cpp`. The evidence for it is the
  plain-simulation agreement above, the agreement between nested and non-nested runs on (b), and the fact that
  each run lands exactly on the claimed tape at the claimed step. No formal proof of the tool was made.
* The claims were checked as stated (arrival at the given step). Whether `C(r + 321,042,928)` is the *first*
  configuration of that form after `C(r)` was not examined.

## Extra values

Claim (a), same procedure, all identical to `C(r + 321,042,928)` at the formula step:
r = 69, 71, 73, 75, 77, 79, 81, 83, 85.
For r = 87 ... 105 the run did not finish within the 60 s I allowed per value (the tool falls into a slow
regime where each proven rule applies only once); these are **not checked**, not mismatches.

Claim (c), halting transition at `claimed + 1` in every case:
r = 68, 70, 72, 74, 76, 78, 80, 1000 and 16,797,708 (step 35,002,809,679,999,373).
