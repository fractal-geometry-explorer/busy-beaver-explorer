# 1RB0RC_1LC0RD_0LD0LC_1RE0LA_0LE1RF_0RA---

bbchallenge id 144992. One of the six-state holdouts. **A base-5 counter of drifting walls**; whether it halts is open.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RC |
| B | 1LC | 0RD |
| C | 0LD | 0LC |
| D | 1RE | 0LA |
| E | 0LE | 1RF |
| F | 0RA | --- |

## What it does

Sample the run each time the head is at the left end in state D reading a 1. The tape is then runs of the block `1000` (written `c`) separated by **walls**, each one of the five words `1001`, `1001100`, `100110`, `10011`, `10010` or a single `0`, and ends with `1001`:

    step 9,999,665,187:  c^7437 10011 c^16515 10011 c^12050 1001100 c^16916 10011 c^8570 10011 c^3595 1001 c^9202 0 c^155 1001

- **A sweep.** The head crosses the first run rightwards (`1000` becomes `0101`, 4 steps a block), changes the first wall, and zigzags back (6 steps a block, `0101` back to `1000`). The first run grows by a block a sweep, so the left side of the tape grows like √t (the *sqrt* side of the triage).
- **Digits.** A wall cycles `1001 → 1001100 → 100110 → 10011 → 10010 → 1001`; the step out of `10011` carries into the next wall. The walls are the base-5 digits of the number of sweeps, lowest first. The right end moves only when every digit is at `10011` (an overflow): every wall becomes a single `0` (a digit that turns into `1001` at the next carry that reaches it) and a new lowest digit is born at the left end, so overflows come about five times further apart each time: logarithmic growth (the *exp* side). 19 overflows in 10,000,000,000 steps.
- **Drift and mergers.** A wall shifts right by two blocks per cycle, so lower digits catch up with higher ones; when the run between two walls is used up they merge into one (13 mergers in 10,000,000,000 steps).
- **Halting.** The only halt is F reading a 1. Here E's 1-transition (1RF) is part of every sweep, and F always reads a 0 there (F0 → 0RA): in 10^10 steps F was entered 833,395,133 times and never read a 1.

The family shares states A–D and differs in E and F (that is, in what a merger does): `1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0LB---`, `1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0RD---`, `1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_1LB---`, `1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA1RF_0RE---`. The lead machine's folder (`1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0RD---`) holds the family's scripts.

## What is proved, computed, conjectured

- **kernel**: The halting configurations. The machine stops exactly when it reads the symbol of a halting transition (F1); the generated statement covers every configuration. (step_none_iff, lean/Blank.lean)
- **kernel**: No halt in the first 10,000 steps. The list simulator of the shared library, proved to agree with the machine's semantics, runs 10,000 steps from blank tape without a halt, evaluated by Lean's kernel. (blank_runs_kernel, lean/Blank.lean)
- **native**: No halt in the first 10^7 steps. The same run, evaluated by compiled code. (blank_runs_native, lean/Blank.lean)
- **trusted**: No halt in the first 10^9 steps. The C simulator tools/c/triage.c runs 10^9 steps without a halt; at the end 72,569 cells have been visited and 19,554 of them hold a 1. (holdouts/triage.json)
- **kernel**: The sweep and carry rules. With the head in state D on the first 1 at the left end, 0^∞ D> (1000)^(x+1) W (1000)^(y+1) R, one sweep moves the first wall W one step along its cycle 1001 → 1001100 → 100110 → 10011 → 10010 → 1001, for every x, y and every tape R (four theorems, one per shape that does not carry). From 10011 the sweep carries: it also moves the second wall one step (four theorems, one per shape of the second wall that does not carry on). The step counts are linear in x. (sweep_w0 … sweep_w4, carry_w0 … carry_w4, lean/Walls.lean)
- **trusted**: No halt in the first 10^10 steps. The C simulator (tools/c/tm.h) runs 10^10 steps without a halt; at the end the tape has 7 walls. Along the way the counter overflowed 19 times (every wall in shape 10011 at once: the carry runs off the right end and the tape grows there) and walls merged 13 times. (py/walls.py in the folder of 1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0RD…)
- **trusted**: Where F comes in. Here E's 1-transition (1RF) is part of every sweep, and F always reads a 0 there (F0 → 0RA): in 10^10 steps F was entered 833,395,133 times and never read a 1. (py/walls.py)
- **trusted**: The mergers tried end without a halt. A symbolic run (head, literal cells and repeated blocks with variable counts, any tape R beyond) from 0^∞ D> (1000)^(x+3) W₁ (1000)^g W₂ (1000)^(y+6) W₃ (1000)^(z+4) R, for each of the 36 pairs of shapes W₁, W₂ and each gap g = 0, 1, 2: 108 of the 108 cases return to the ordinary form without a halt, and none halts. It is evidence, not a proof: mergers deeper in the tape have another wall near on the left, and the edge events (a wall reaching the right end, the overflow) are not covered. (py/collisions.py)
- **trusted**: n-gram CPS fails. The n-gram closed position set decider of the Coq-BB5 paper finds a (spurious) path to the halt for windows of 3 to 7 cells with or without history, and for the lead machine of the family up to 40 cells: windows cannot tell how the walls are spaced. (tools/c/ngramcps.c)
- **open**: Does it halt from blank tape? Not known. It would halt only if some merger of walls (or edge event) put E on a 1 followed by a 1. The mergers tried never do, which suggests it never halts; a proof needs a closed description of every configuration between samples (a regular language over walls and gaps), which is the next thing to try.

## Notes for later

A non-halting proof looks within reach but is more than a day of work: describe the configurations at the sample points as walls and gaps (gaps as exact small values or a symbolic n + k), prove the sweep, carry, merger and edge rules for every combination that can occur (the merger runs of `py/collisions.py` are the start), and show the set is closed. A closed-tape-language search over macro tokens (blocks and walls instead of cells) is the other route; windows of cells (n-gram CPS up to 40) are not enough.

## Pages

- [`pages/holdouts/1RB0RC_1LC0RD_0LD0LC_1RE0LA_0LE1RF_0RA---/explainer.html`](../../pages/holdouts/1RB0RC_1LC0RD_0LD0LC_1RE0LA_0LE1RF_0RA---/explainer.html)
- [`pages/holdouts/1RB0RC_1LC0RD_0LD0LC_1RE0LA_0LE1RF_0RA---/proof-status.html`](../../pages/holdouts/1RB0RC_1LC0RD_0LD0LC_1RE0LA_0LE1RF_0RA---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RC_1LC0RD_0LD0LC_1RE0LA_0LE1RF_0RA---/lean/check.sh
python3 holdouts/1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0RD---/py/walls.py 1RB0RC_1LC0RD_0LD0LC_1RE0LA_0LE1RF_0RA--- 1000000000
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0LD_0LB1RC_0RD---_1RE0RF_1LF0RA_0LA0LF`](../1RB0LD_0LB1RC_0RD---_1RE0RF_1LF0RA_0LA0LF/README.md): rename A→D, B→E, C→F, D→A, E→B, F→C; it is this table started in state D

**Same tapes at another pace (observed, not proved).** Leave the states aside and compare only the tape and the place of the head. Then a large part of the first 10^7 configurations of this machine are configurations of the machines below, in the same order and up to the end of the run. The steps at which they occur differ, the tables are not renamings of each other, and equal tapes with different states may be continued differently, so this does not tie the halting questions together.

- [`1RB---_0LC0LB_1RF0LD_1RE0RB_1LB0RC_0RD1RA`](../1RB---_0LC0LB_1RF0LD_1RE0RB_1LB0RC_0RD1RA/README.md): 8,330,405 configurations, the last at step 10,000,000 here and step 8,330,419 there

<!-- end of related machines -->
