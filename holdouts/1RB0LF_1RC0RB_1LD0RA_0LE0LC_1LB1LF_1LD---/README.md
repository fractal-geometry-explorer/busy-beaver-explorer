# 1RB0LF_1RC0RB_1LD0RA_0LE0LC_1LB1LF_1LD---

bbchallenge id 131976, group G08 (two-sided sqrt growth). Whether it halts from blank tape is **open**. Pages:
[`explainer.html`](../../pages/holdouts/1RB0LF_1RC0RB_1LD0RA_0LE0LC_1LB1LF_1LD---/explainer.html), [`proof-status.html`](../../pages/holdouts/1RB0LF_1RC0RB_1LD0RA_0LE0LC_1LB1LF_1LD---/proof-status.html), both built from
[`status.json`](status.json).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LF |
| B | 1RC | 0RB |
| C | 1LD | 0RA |
| D | 0LE | 0LC |
| E | 1LB | 1LF |
| F | 1LD | --- |

## What it does

A bouncer over a list of counters. Both ends of the tape grow like the square root of the step count.

**Where it can halt.** Only in F reading a 1. F is entered from `A>1` (0LF) and from `E>1` (1LF), so the machine
halts exactly when `1 A>1` or `1 E>1` occurs. In the first 10^8 steps F is entered 27,487 times, always onto a 0,
in 22,690 of them inside `101[0]101` (`c/haltwatch.c`).

**The counters.** At the left end (`py/snapshots.py 3e7 L 50`, every 50th left-end record):

    404490 E>0 (01)^284 (10)^167 (01)^242 (10)^19 (01)^12 0 (01)^3 (10)^3 1
    432128 C>0 (01)^301 0 (01)^174 0 (01)^240 0 (01)^20 0 (01)^11 (10)^5 110101
    459974 E>0 (01)^318 0 (01)^182 0 (01)^237 (10)^23 1 (10)^11 (01)^6 00101

`(01)^a (10)^b` and `(01)^a 0 (01)^b` are the same pair of numbers with a different single-cell boundary, so the tape
is a list a, b, c, d, ... Per 50 left-end visits a grows by 17, b by about 8, c shrinks by about 3, d grows by about 4.
At the right end there are short irregular words. When a counter runs out the list is rebuilt: (185, 127, 110) at
step 136,230, (201, 124, 257) at step 284,618.

## What is proved (Lean)

Only the generated `lean/Blank.lean`: the halting configurations, no halt in 10^4 steps (kernel) and 10^7
(`native_decide`).

## Computed / observed

- No halt in 10^9 steps (`tools/c/triage.c`).
- The halt-entry counts (`c/haltwatch.c`) and the counter list (`py/snapshots.py`).

## Open, and next steps

- Find the exact update of one round trip on the list (which counters change, by how much, and how the boundary
  defects cycle); the rates 1/3, 1/6 per visit suggest the first counters are unary counters passing carries down.
- Describe the rebuild when a counter reaches 0. That is where the irregular right-end words come from and where a
  halt would happen, if it does.

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---`](../1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---/README.md): rename A→E, B→A, C→B, D→C, E→D, F→F; it is this table started in state B
- [`1RB1RF_1LC0LB_1RE0LD_1LB0RF_0RA0RC_1RE---`](../../bb6-1RB1RF_1LC0LB/README.md): rename A→D, B→B, C→C, D→E, E→A, F→F and exchange left and right; it is this table started in state E, in a mirror
- [`1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---`](../1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---/README.md): rename A→E, B→D, C→A, D→B, E→C, F→F and exchange left and right; it is this table started in state C, in a mirror

<!-- end of related machines -->
