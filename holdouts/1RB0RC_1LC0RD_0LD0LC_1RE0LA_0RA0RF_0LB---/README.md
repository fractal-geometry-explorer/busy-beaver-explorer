# 1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0LB---

bbchallenge id 99697. One of the six-state holdouts. **A base-5 counter of drifting walls**; whether it halts is open.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RC |
| B | 1LC | 0RD |
| C | 0LD | 0LC |
| D | 1RE | 0LA |
| E | 0RA | 0RF |
| F | 0LB | --- |

## What it does

Sample the run each time the head is at the left end in state D reading a 1. The tape is then runs of the block `1000` (written `c`) separated by **walls**, each one of the five words `1001`, `1001100`, `100110`, `10011`, `10010` or a single `0`, and ends with `1001`:

    step 9,999,655,960:  c^7233 10011 c^36376 10010 c^6750 100110 c^3969 10011 c^99 10010 c^947 1001100 c^325 1001100 c^8 1001

- **A sweep.** The head crosses the first run rightwards (`1000` becomes `0101`, 4 steps a block), changes the first wall, and zigzags back (6 steps a block, `0101` back to `1000`). The first run grows by a block a sweep, so the left side of the tape grows like √t (the *sqrt* side of the triage).
- **Digits.** A wall cycles `1001 → 1001100 → 100110 → 10011 → 10010 → 1001`; the step out of `10011` carries into the next wall. The walls are the base-5 digits of the number of sweeps, lowest first. The right end moves only when every digit is at `10011` (an overflow): every wall becomes a single `0` (a digit that turns into `1001` at the next carry that reaches it) and a new lowest digit is born at the left end, so overflows come about five times further apart each time: logarithmic growth (the *exp* side). 13 overflows in 10,000,000,000 steps.
- **Drift and mergers.** A wall shifts right by two blocks per cycle, so lower digits catch up with higher ones; when the run between two walls is used up they merge into one (17 mergers in 10,000,000,000 steps).
- **Halting.** The only halt is F reading a 1. State F is reached only through E reading a 1, which an ordinary sweep never does: in 10^10 steps it happened 4 times, never in an ordinary sweep or carry (their Lean proofs never pass through F) but in the rare events, and each time F read a 0 (F0 → 0LB).

The family shares states A–D and differs in E and F (that is, in what a merger does): `1RB0RC_1LC0RD_0LD0LC_1RE0LA_0LE1RF_0RA---`, `1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0RD---`, `1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_1LB---`, `1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA1RF_0RE---`. The lead machine's folder (`1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0RD---`) holds the family's scripts.

## What is proved, computed, conjectured

- **kernel**: The halting configurations. The machine stops exactly when it reads the symbol of a halting transition (F1); the generated statement covers every configuration. (step_none_iff, lean/Blank.lean)
- **kernel**: No halt in the first 10,000 steps. The list simulator of the shared library, proved to agree with the machine's semantics, runs 10,000 steps from blank tape without a halt, evaluated by Lean's kernel. (blank_runs_kernel, lean/Blank.lean)
- **native**: No halt in the first 10^7 steps. The same run, evaluated by compiled code. (blank_runs_native, lean/Blank.lean)
- **trusted**: No halt in the first 10^9 steps. The C simulator tools/c/triage.c runs 10^9 steps without a halt; at the end 82,384 cells have been visited and 24,033 of them hold a 1. (holdouts/triage.json)
- **kernel**: The sweep and carry rules. With the head in state D on the first 1 at the left end, 0^∞ D> (1000)^(x+1) W (1000)^(y+1) R, one sweep moves the first wall W one step along its cycle 1001 → 1001100 → 100110 → 10011 → 10010 → 1001, for every x, y and every tape R (four theorems, one per shape that does not carry). From 10011 the sweep carries: it also moves the second wall one step (four theorems, one per shape of the second wall that does not carry on). The step counts are linear in x. (sweep_w0 … sweep_w4, carry_w0 … carry_w4, lean/Walls.lean)
- **trusted**: No halt in the first 10^10 steps. The C simulator (tools/c/tm.h) runs 10^10 steps without a halt; at the end the tape has 7 walls. Along the way the counter overflowed 13 times (every wall in shape 10011 at once: the carry runs off the right end and the tape grows there) and walls merged 17 times. (py/walls.py in the folder of 1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0RD…)
- **trusted**: Where F comes in. State F is reached only through E reading a 1, which an ordinary sweep never does: in 10^10 steps it happened 4 times, never in an ordinary sweep or carry (their Lean proofs never pass through F) but in the rare events, and each time F read a 0 (F0 → 0LB). (py/walls.py)
- **trusted**: The mergers tried end without a halt. A symbolic run (head, literal cells and repeated blocks with variable counts, any tape R beyond) from 0^∞ D> (1000)^(x+3) W₁ (1000)^g W₂ (1000)^(y+6) W₃ (1000)^(z+4) R, for each of the 36 pairs of shapes W₁, W₂ and each gap g = 0, 1, 2: 108 of the 108 cases return to the ordinary form without a halt, and none halts. It is evidence, not a proof: mergers deeper in the tape have another wall near on the left, and the edge events (a wall reaching the right end, the overflow) are not covered. (py/collisions.py)
- **trusted**: n-gram CPS fails. The n-gram closed position set decider of the Coq-BB5 paper finds a (spurious) path to the halt for windows of 3 to 7 cells with or without history, and for the lead machine of the family up to 40 cells: windows cannot tell how the walls are spaced. (tools/c/ngramcps.c)
- **open**: Does it halt from blank tape? Not known. It would halt only if some merger of walls (or edge event) put E on a 1 followed by a 1. The mergers tried never do, which suggests it never halts; a proof needs a closed description of every configuration between samples (a regular language over walls and gaps), which is the next thing to try.

## Notes for later

A non-halting proof looks within reach but is more than a day of work: describe the configurations at the sample points as walls and gaps (gaps as exact small values or a symbolic n + k), prove the sweep, carry, merger and edge rules for every combination that can occur (the merger runs of `py/collisions.py` are the start), and show the set is closed. A closed-tape-language search over macro tokens (blocks and walls instead of cells) is the other route; windows of cells (n-gram CPS up to 40) are not enough.

## Pages

- [`pages/holdouts/1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0LB---/explainer.html`](../../pages/holdouts/1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0LB---/explainer.html)
- [`pages/holdouts/1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0LB---/proof-status.html`](../../pages/holdouts/1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0LB---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0LB---/lean/check.sh
python3 holdouts/1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0RD---/py/walls.py 1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0LB--- 1000000000
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---`](../1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---/README.md): rename A→E, B→A, C→B, D→C, E→D, F→F and exchange left and right; it is this table started in state B, in a mirror
- [`1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_0LD---`](../1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_0LD---/README.md): rename A→C, B→D, C→E, D→A, E→B, F→F; it is this table started in state D

<!-- end of related machines -->
