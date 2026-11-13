# 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE

bbchallenge id 56722. One of the six-state holdouts whose halting from blank tape is open. Family: Counter on the left feeding a growing region on the right (exp/power; structure not yet found).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RA |
| B | 1LC | 0RD |
| C | 1LD | 1LB |
| D | 1LE | 0LF |
| E | 0RA | --- |
| F | 0LB | 1RE |

**Verdict.** **The question is open.** No halt in the first 10^10 steps (C simulator); the macro configuration and its rules are not yet known, so there is no map to analyse and no heuristic for halting beyond the localisation of the halt below.

## What it does

Left of the start the tape is blocks of an odd number of 1s separated by double 0s; it grows like the logarithm of the
step count. Right of the start the tape is a long stretch of the words `1 0` and `1 1 0`, mostly `(1 0)^n`, growing like a
power of the step count (exponent about 0.68).

New this round: the right end grows by exactly 3 cells at 15,386 of the 15,470 visits in 2·10^9 steps. Between visits
the head turns back at a point that drifts right by about 29 cells per visit, so the swept zone shrinks; 3,478 times
the turning point jumps far left and a new phase starts.

## What is established

**Proved in Lean, kernel only:**

- **The halting configurations.** The machine stops exactly when it reads the symbol of a halting transition (E1); the generated statement covers every configuration. (`step_none_iff`, `lean/Blank.lean`)
- **No halt in the first 10,000 steps.** The list simulator of the shared library, proved to agree with the machine's semantics, runs 10,000 steps from blank tape without a halt, evaluated by Lean's kernel. (`blank_runs_kernel`, `lean/Blank.lean`)

**Proved in Lean with `native_decide`:**

- **No halt in the first 10^7 steps.** The same run, evaluated by compiled code. (`blank_runs_native`, `lean/Blank.lean`)

**Trusted computation (C/Python, not Lean):**

- **No halt in the first 10^10 steps.** The C simulator `tools/c/tmrun.c` runs 10^10 steps from blank tape without a halt; at the end the tape holds 94,290 ones. (`tmrun 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE 10000000000`)
- **No halt in the first 10^9 steps.** The C simulator `tools/c/triage.c` runs 10^9 steps without a halt; at the end 44,635 cells have been visited and 19,460 of them hold a 1. (`holdouts/triage.json`)
- **Where a halt can be.** A closed tape language of windows of 5 cells (`tools/py/bbtools/ctl.py`, closure checked by the script, not by Lean) contains every configuration reachable from blank tape, and its only halting configurations have E reading a 1 with at least four 1s right of the head (`E>1 1 1 1 1`). In the run so far the right region has shown no runs of five 1s, so a halt would have to happen inside a long block of 1s, as in the left region. (`python3 -m bbtools.ctl 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE 5`)
- **Not decided by n-gram CPS up to width 14.** The n-gram Closed Position Set decider (`tools/c/ngramcps.c`) with equal widths 4, 6, 8, 10, 12 and 14, plain and with the fixed-length (1) and LRU history augmentations, either reaches a halting local configuration (UNKNOWN) or stops at 3·10^7 local configurations: it does not prove non-halting at these settings. (`ngramcps MACHINE N [-H 1 | -U] -m 30000000`)
- **The right end grows by three cells per visit.** Counting a visit as the head reaching the right end after having been more than 50 cells to its left, the first 2·10^9 steps have 15,470 visits; at 15,386 of them the right end has grown by exactly 3 cells since the previous visit (57 times by 6, the rest by 0, 1 or 5). The head turns back at a point that drifts to the right by about 29 cells per visit, so the zone it sweeps shrinks, and every so often (3,478 times) the turning point jumps far to the left and a new phase starts. Visits get further apart as the right region grows, which gives the power-law growth. (`c/rvisits.c`: `./rvisits MACHINE 2000000000 50`)

**Heuristic:**

- **Growth shape: exp/power.** Left of the start, the visited part of the tape grows like the logarithm of the step count: each new cell costs a roughly constant factor more time, the signature of a *counter* or of a Collatz-like map whose values are written on the tape (fitted exponent 0.062). Right of the start it grows like a power of the step count other than 1/2 (fitted exponent 0.677). (`tools/py/bbtools/triage.py`)
- **The two regions.** Left: `C>0 1 0^2 1^3 0^2 1^9 0^2 1 0^2 1 0^2 1^357 0^2 ...`, blocks of odd length separated by `0^2`, a few of them long (one of them has 205, 357 and 421 ones at three of the last left records before 10^9). Right: words `1 0` and `1 1 0`, with long stretches `(1 0)^n`. (`tmrun 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE 1000000000 records 100000`)

**Open:**

- **Does it halt from blank tape?.** Not known. The macro configuration family has not been found.

## The proved neighbour (round 6)

The community tracker says: "The same table from another start is proved in busycoq. That proof fails or runs out
of memory from these starts." What we found, and what we tried:

- **Which machine.** `1RB0RF_0LC---_1LD1LC_1RE0LA_1RA1RD_0RD1LB`, proved non-halting in busycoq (`verify/CTLv2.v`,
  lemma `nonhalt17`, by `CPS_LRU 100000001 400000 400000 8 3200 2 6 0 0`). It is this table with left and right
  exchanged, started in this machine's state D (its states A, B, C, D, E, F are D, E, A, B, C, F here).
- **How the start differs** (Lean, kernel: `neighbour_start` in `lean/Neighbour.lean`). From blank tape in state D,
  three steps lead to state A on blank tape with a single 1 on the cell to its left. So the proved machine is this
  machine started on the tape `1 A>0` instead of `A>0`. The table is identical; every entry is used by both.
- **The neighbour's proof, reproduced** (trusted C++, `c/cpslru.cpp`, our own implementation of the search). The
  proof is a closed tape language: blocks of 8 cells; each side of the head summarised by its 2 nearest blocks and
  the list of up to 6 different blocks seen beyond; a set of such abstract configurations that contains the
  neighbour's configuration after some number of steps, is closed under the machine, and has no halt in it. For
  start D our search finds one with 4,091 abstract configurations from the configuration after 10^6+1 steps (about 4,035
  on the mirrored machine as busycoq states it, also from 10^7+1 and 10^8+1). From blank tape, or after 10^5
  steps, it does not close within 300,000 summaries: the neighbour's run has to settle first.
- **The same search from this machine's run** (trusted C++). After 10^8+1 steps with the neighbour's parameters,
  after 10^9+1 and 10^10+1 steps with ten parameter sets (blocks of 1 to 16 cells), and after 10^11+1 steps with
  two: never closed (more than 300,000 summaries or 6,000,000 abstract configurations; with blocks of one cell a
  halting abstract configuration is reached, which decides nothing).
- **What that rules out.** A closed set is the smallest one containing its start. If one of this machine's
  configurations at those four times were inside the neighbour's language, its closure would stay inside the
  neighbour's 4,091 configurations. It does not, so this run has not entered the part of the tape space the
  neighbour's theorem covers, up to 10^11 steps. It does not show that no closed language exists for this machine.
- **Why the runs differ** (observed). After 10^8 steps the neighbour's tape is long regular stretches (`1 0 0`
  repeated, and the 22-cell word `1^5 0 1 0^2 1^5 0^2 1 0^2 1 0^2` repeated); this machine's tape still has
  irregular blocks of 1s (one of 97) next to an irregular region of words `1 0` and `1 1 0`.
- **Other starts.** Two more holdouts are this table from the remaining starts:
  `1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1LD` (state B, mirrored) and `1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE1LC`
  (state C, mirrored). The same search from starts B and C, after 10^8+1 and 10^9+1 steps with parameters 8,2,6
  and 8,1,6, does not close either (`cpslru MACHINE 1000000001 300000 B - 8,2,6,0 8,1,6,0`, and `C`).

No proof was transferred. The decision stays open.

## For later

The phases on the right: record the configuration at the start of each phase (the turning point jump), the
lengths of the `(1 0)^n` stretches, and the rule from one phase to the next; then the odd blocks on the left, which
look like a counter. `c/rvisits.c` gives the visits.

## Reproduce

From the repository root:

```sh
. /etc/profile.d/lean.sh      # after scripts/setup-lean.sh
holdouts/1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE/lean/check.sh
gcc -O2 -o triage tools/c/triage.c && ./triage 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE 1000000000
gcc -O2 -o tmrun tools/c/tmrun.c && ./tmrun 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE 10000000000
cd tools/py && python3 -m bbtools.ctl 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE 5
gcc -O2 -o rvisits holdouts/1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE/c/rvisits.c && ./rvisits 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE 2000000000 50
g++ -O2 -std=c++17 -o cpslru holdouts/1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE/c/cpslru.cpp
./cpslru 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE 1000001 300000 D - 8,2,6,0          # the neighbour's start: CLOSED
./cpslru 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE 1000000001 300000 A - 8,2,6,0 8,1,6,0   # this machine: toobig
```

## Pages

- [`pages/holdouts/1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE/explainer.html`](../../pages/holdouts/1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE/explainer.html)
- [`pages/holdouts/1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE/proof-status.html`](../../pages/holdouts/1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE/proof-status.html)

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1LD`](../1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1LD/README.md): rename A→E, B→A, C→B, D→C, E→D, F→F and exchange left and right; it is this table started in state B, in a mirror
- [`1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE1LC`](../1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE1LC/README.md): rename A→D, B→E, C→A, D→B, E→C, F→F and exchange left and right; it is this table started in state C, in a mirror

<!-- end of related machines -->
