# 1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_1LB---

bbchallenge id 67596. One of the six-state holdouts. **A base-5 counter of drifting walls**; whether it halts is open.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RC |
| B | 1LC | 0RD |
| C | 0LD | 0LC |
| D | 1RE | 0LA |
| E | 0RA | 0RF |
| F | 1LB | --- |

## What it does

Sample the run each time the head is at the left end in state D reading a 1. The tape is then runs of the block `1000` (written `c`) separated by **walls**, each one of the five words `1001`, `1001100`, `100110`, `10011`, `10010` or a single `0`, and ends with `1001`:

    step 9,999,852,852:  c^30987 10011 c^19877 10010 c^1496 10010 c^1342 1001 c^2100 10010 c^2778 1001 c^815 100110 c^521 1001

- **A sweep.** The head crosses the first run rightwards (`1000` becomes `0101`, 4 steps a block), changes the first wall, and zigzags back (6 steps a block, `0101` back to `1000`). The first run grows by a block a sweep, so the left side of the tape grows like √t (the *sqrt* side of the triage).
- **Digits.** A wall cycles `1001 → 1001100 → 100110 → 10011 → 10010 → 1001`; the step out of `10011` carries into the next wall. The walls are the base-5 digits of the number of sweeps, lowest first. The right end moves only when every digit is at `10011` (an overflow): every wall becomes a single `0` (a digit that turns into `1001` at the next carry that reaches it) and a new lowest digit is born at the left end, so overflows come about five times further apart each time: logarithmic growth (the *exp* side). 18 overflows in 10,000,000,000 steps.
- **Drift and mergers.** A wall shifts right by two blocks per cycle, so lower digits catch up with higher ones; when the run between two walls is used up they merge into one (18 mergers in 10,000,000,000 steps).
- **Halting.** The only halt is F reading a 1. State F is reached only through E reading a 1, which an ordinary sweep never does: in 10^10 steps it happened 6 times, never in an ordinary sweep or carry (their Lean proofs never pass through F) but in the rare events, and each time F read a 0 (F0 → 1LB).

The family shares states A–D and differs in E and F (that is, in what a merger does): `1RB0RC_1LC0RD_0LD0LC_1RE0LA_0LE1RF_0RA---`, `1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0LB---`, `1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0RD---`, `1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA1RF_0RE---`. The lead machine's folder (`1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0RD---`) holds the family's scripts.

## What is proved, computed, conjectured

- **kernel**: The halting configurations. The machine stops exactly when it reads the symbol of a halting transition (F1); the generated statement covers every configuration. (step_none_iff, lean/Blank.lean)
- **kernel**: No halt in the first 10,000 steps. The list simulator of the shared library, proved to agree with the machine's semantics, runs 10,000 steps from blank tape without a halt, evaluated by Lean's kernel. (blank_runs_kernel, lean/Blank.lean)
- **native**: No halt in the first 10^7 steps. The same run, evaluated by compiled code. (blank_runs_native, lean/Blank.lean)
- **trusted**: No halt in the first 10^9 steps. The C simulator tools/c/triage.c runs 10^9 steps without a halt; at the end 97,920 cells have been visited and 35,843 of them hold a 1. (holdouts/triage.json)
- **kernel**: The sweep and carry rules. With the head in state D on the first 1 at the left end, 0^∞ D> (1000)^(x+1) W (1000)^(y+1) R, one sweep moves the first wall W one step along its cycle 1001 → 1001100 → 100110 → 10011 → 10010 → 1001, for every x, y and every tape R (four theorems, one per shape that does not carry). From 10011 the sweep carries: it also moves the second wall one step (four theorems, one per shape of the second wall that does not carry on). The step counts are linear in x. (sweep_w0 … sweep_w4, carry_w0 … carry_w4, lean/Walls.lean)
- **trusted**: No halt in the first 10^10 steps. The C simulator (tools/c/tm.h) runs 10^10 steps without a halt; at the end the tape has 7 walls. Along the way the counter overflowed 18 times (every wall in shape 10011 at once: the carry runs off the right end and the tape grows there) and walls merged 18 times. (py/walls.py in the folder of 1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0RD…)
- **trusted**: Where F comes in. State F is reached only through E reading a 1, which an ordinary sweep never does: in 10^10 steps it happened 6 times, never in an ordinary sweep or carry (their Lean proofs never pass through F) but in the rare events, and each time F read a 0 (F0 → 1LB). (py/walls.py)
- **trusted**: The mergers tried end without a halt. A symbolic run (head, literal cells and repeated blocks with variable counts, any tape R beyond) from 0^∞ D> (1000)^(x+3) W₁ (1000)^g W₂ (1000)^(y+6) W₃ (1000)^(z+4) R, for each of the 36 pairs of shapes W₁, W₂ and each gap g = 0, 1, 2: 104 of the 108 cases return to the ordinary form without a halt; 4 stopped unresolved (NeedSplit), and none halts. It is evidence, not a proof: mergers deeper in the tape have another wall near on the left, and the edge events (a wall reaching the right end, the overflow) are not covered. (py/collisions.py)
- **trusted**: n-gram CPS fails. The n-gram closed position set decider of the Coq-BB5 paper finds a (spurious) path to the halt for windows of 3 to 7 cells with or without history, and for the lead machine of the family up to 40 cells: windows cannot tell how the walls are spaced. (tools/c/ngramcps.c)
- **open**: Does it halt from blank tape? Not known. It would halt only if some merger of walls (or edge event) put E on a 1 followed by a 1. The mergers tried never do, which suggests it never halts; a proof needs a closed description of every configuration between samples (a regular language over walls and gaps), which is the next thing to try.

## Notes for later

A non-halting proof looks within reach but is more than a day of work: describe the configurations at the sample points as walls and gaps (gaps as exact small values or a symbolic n + k), prove the sweep, carry, merger and edge rules for every combination that can occur (the merger runs of `py/collisions.py` are the start), and show the set is closed. A closed-tape-language search over macro tokens (blocks and walls instead of cells) is the other route; windows of cells (n-gram CPS up to 40) are not enough.

<!-- F05 -->

## Family F05: one core, forty machines

This machine is one of 40 holdouts with the same five states. In frame A all of them are `1RB0LC_0RC0RB_1LD0RE_0LE?LF_1LA0LB_??---`: they differ in D1 (0LF or 1LF), in F0 and in the start state. This one is the mirror image of `1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1RA---` with the states renamed A->B, B->C, C->D, D->E, E->A, F->F (frame G), started in that table's state E. `lean/Family.lean` proves it (`step_img`, `halts_iff`: the machine halts from blank tape iff `1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1RA---` halts from blank tape in state E).

Shared by all 40 and proved in Lean on each machine's own frame-A table (`lean/Family.lean`, written by `holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---/py/gen_family_lean.py`):

- `go_spec`: the visit rule for every depth (a clean visit to [b1, ..., bk] makes five visits to the list without b1);
- `go_closed`, `visit_closed`: its closed form (b1-5, b2-18, b3-90, ..., bk+12·5^(k-2));
- `visit_conserves` (new): a clean visit conserves, for the blocks after the first and before the last, the residue of block i modulo 18·5^(i-2) and the drift b(i+1) - 5·b(i);
- `birth`, `fevent`, `fevent_reads_zero`: the birth of a block, and the harmless entry into F.

**Run (trusted).** The exact block-list map (`holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---/py/f05_run.py`, `hybrid.py`) reaches step 3.4·10^200 without a halt: 592 returns to the left end, 287 entries into F, all reading 0, tape around the head `010001000100[F]001010101010` (192x); `010001000100[F]001010110101` (95x). Its F-events agree with the plain simulation on the first 3e+09 steps (6 F-events). Summary and the first 80 left-end block lists: `data/f05_run.json`.

**Drifts (observed, at left-end events only).** Smallest |b(i+1) - 5·b(i)| after step 10^20: 2606; after step 10^100: 10405806. Halting would need a drift near 0 at the moment its block runs out (two exceptional events close together); nothing proved excludes that, so the question stays open.

The (D1, F0) variants and their machines (runs marked with the same letter had the same block list at their last left-end event, observed):

| D1 | F0 | machine | frame | frame-A start | same run | exact block-list map |
|---|---|---|---|---|---|---|
| 0LF | 0LC | [`1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_0RA---`](../1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_0RA---/README.md) | B | C |  | no halt in 10^200 steps, 214 F-events, all reading 0 |
| 0LF | 0LC | [`1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0LC---`](../1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0LC---/README.md) | A | A |  | no halt in 10^200 steps, 199 F-events, all reading 0 |
| 0LF | 0LC | [`1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0RD---`](../1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0RD---/README.md) | G | E |  | no halt in 10^200 steps, 223 F-events, all reading 0 |
| 0LF | 0LE | [`1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0LE---`](../1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0LE---/README.md) | A | A |  | no halt in 10^200 steps, 214 F-events, all reading 0 |
| 0LF | 0LE | [`1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_0RC---`](../1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_0RC---/README.md) | B | C |  | no halt in 10^200 steps, 251 F-events, all reading 0 |
| 0LF | 0LE | [`1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0RA---`](../1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0RA---/README.md) | G | E |  | no halt in 10^200 steps, 232 F-events, all reading 0 |
| 0LF | 0RA | [`1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---`](../1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---/README.md) | A | A |  | no halt in 10^200 steps, 278 F-events, all reading 0 |
| 0LF | 0RA | [`1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_0LD---`](../1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_0LD---/README.md) | B | C |  | no halt in 10^200 steps, 278 F-events, all reading 0 |
| 0LF | 0RA | [`1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0LB---`](../1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0LB---/README.md) | G | E |  | no halt in 10^200 steps, 245 F-events, all reading 0 |
| 0LF | 0RB | [`1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RB---`](../1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RB---/README.md) | A | A |  | no halt in 10^200 steps, 200 F-events, all reading 0 |
| 0LF | 0RB | [`1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_0LE---`](../1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_0LE---/README.md) | B | C |  | no halt in 10^200 steps, 200 F-events, all reading 0 |
| 0LF | 0RB | [`1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0LC---`](../1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0LC---/README.md) | G | E |  | no halt in 10^200 steps, 184 F-events, all reading 0 |
| 0LF | 0RE | [`1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RE---`](../1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RE---/README.md) | A | A |  | no halt in 10^200 steps, 292 F-events, all reading 0 |
| 0LF | 0RE | [`1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0LA---`](../1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0LA---/README.md) | G | E |  | no halt in 10^200 steps, 265 F-events, all reading 0 |
| 0LF | 1LA | [`1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LA---`](../1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LA---/README.md) | A | A |  | no halt in 10^200 steps, 214 F-events, all reading 0 |
| 0LF | 1LB | [`1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LB---`](../1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LB---/README.md) | A | A |  | no halt in 10^200 steps, 292 F-events, all reading 0 |
| 0LF | 1LB | [`1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1RE---`](../1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1RE---/README.md) | B | C | a | no halt in 10^200 steps, 292 F-events, all reading 0 |
| 0LF | 1LB | [`1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_1RC---`](../1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_1RC---/README.md) | G | E |  | no halt in 10^200 steps, 265 F-events, all reading 0 |
| 0LF | 1LC | [`1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LC---`](../1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LC---/README.md) | A | A |  | no halt in 10^200 steps, 192 F-events, all reading 0 |
| 0LF | 1LC | [`1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1RA---`](../1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1RA---/README.md) | B | C |  | no halt in 10^200 steps, 192 F-events, all reading 0 |
| 0LF | 1LC | [`1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_1RD---`](../1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_1RD---/README.md) | G | E |  | no halt in 10^200 steps, 197 F-events, all reading 0 |
| 0LF | 1RA | [`1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1RA---`](../1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1RA---/README.md) | A | A |  | no halt in 10^200 steps, 240 F-events, all reading 0 |
| 0LF | 1RA | [`1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1LD---`](../1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1LD---/README.md) | B | C |  | no halt in 10^200 steps, 240 F-events, all reading 0 |
| 0LF | 1RA | **`1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_1LB---`** | G | E |  | no halt in 10^200 steps, 287 F-events, all reading 0 |
| 1LF | 0LB | [`1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_0LB---`](../1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_0LB---/README.md) | A | A |  | no halt in 10^200 steps, 209 F-events, all reading 0 |
| 1LF | 0LB | [`1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_0RE---`](../1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_0RE---/README.md) | B | C |  | no halt in 10^200 steps, 192 F-events, all reading 0 |
| 1LF | 0LB | [`1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA1RF_0RC---`](../1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA1RF_0RC---/README.md) | G | E |  | no halt in 10^200 steps, 211 F-events, all reading 0 |
| 1LF | 0LD | [`1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_0LD---`](../1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_0LD---/README.md) | A | A |  | no halt in 10^22 steps, 21 F-events, all reading 0 |
| 1LF | 0LD | [`1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_0RB---`](../1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_0RB---/README.md) | B | C |  | no halt in 10^22 steps, 21 F-events, all reading 0 |
| 1LF | 0LD | [`1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA1RF_0RE---`](../1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA1RF_0RE---/README.md) | G | E |  | not run |
| 1LF | 0RC | [`1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_0LA---`](../1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_0LA---/README.md) | B | C |  | no halt in 10^200 steps, 251 F-events, all reading 0 |
| 1LF | 0RC | [`1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA1RF_0LD---`](../1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA1RF_0LD---/README.md) | G | E |  | no halt in 10^200 steps, 232 F-events, all reading 0 |
| 1LF | 0RE | [`1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_0RE---`](../1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_0RE---/README.md) | A | A |  | no halt in 10^200 steps, 193 F-events, all reading 0 |
| 1LF | 1LB | [`1RB---_0LC0LB_1RF0LD_1RE0RB_1LB0RC_0RD1RA`](../1RB---_0LC0LB_1RF0LD_1RE0RB_1LB0RC_0RD1RA/README.md) | X | F |  | no halt in 10^200 steps, 206 F-events, all reading 0 |
| 1LF | 1LB | [`1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_1LB---`](../1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_1LB---/README.md) | A | A |  | no halt in 10^200 steps, 193 F-events, all reading 0 |
| 1LF | 1LB | [`1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_1RE---`](../1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_1RE---/README.md) | B | C |  | no halt in 10^200 steps, 193 F-events, all reading 0 |
| 1LF | 1LD | [`1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_1LD---`](../1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_1LD---/README.md) | A | A |  | no halt in 10^200 steps, 209 F-events, all reading 0 |
| 1LF | 1LD | [`1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_1RB---`](../1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_1RB---/README.md) | B | C |  | no halt in 10^200 steps, 192 F-events, all reading 0 |
| 1LF | 1LD | [`1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA1RF_1RE---`](../1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA1RF_1RE---/README.md) | G | E |  | no halt in 10^200 steps, 211 F-events, all reading 0 |
| 1LF | 1RA | [`1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_1LD---`](../1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_1LD---/README.md) | B | C | a | no halt in 10^200 steps, 292 F-events, all reading 0 |

<!-- end F05 -->

## Pages

- [`pages/holdouts/1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_1LB---/explainer.html`](../../pages/holdouts/1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_1LB---/explainer.html)
- [`pages/holdouts/1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_1LB---/proof-status.html`](../../pages/holdouts/1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_1LB---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_1LB---/lean/check.sh
python3 holdouts/1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0RD---/py/walls.py 1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_1LB--- 1000000000
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1RA---`](../1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1RA---/README.md): rename A→E, B→A, C→B, D→C, E→D, F→F and exchange left and right; it is this table started in state B, in a mirror
- [`1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1LD---`](../1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1LD---/README.md): rename A→C, B→D, C→E, D→A, E→B, F→F; it is this table started in state D

<!-- end of related machines -->
