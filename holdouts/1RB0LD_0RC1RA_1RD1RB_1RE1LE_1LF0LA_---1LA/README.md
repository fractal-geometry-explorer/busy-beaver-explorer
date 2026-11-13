# 1RB0LD_0RC1RA_1RD1RB_1RE1LE_1LF0LA_---1LA

bbchallenge id 132972, group G08 (two-sided sqrt growth). Whether it halts from blank tape is **open**. Pages:
[`explainer.html`](../../pages/holdouts/1RB0LD_0RC1RA_1RD1RB_1RE1LE_1LF0LA_---1LA/explainer.html), [`proof-status.html`](../../pages/holdouts/1RB0LD_0RC1RA_1RD1RB_1RE1LE_1LF0LA_---1LA/proof-status.html), both built from
[`status.json`](status.json).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LD |
| B | 0RC | 1RA |
| C | 1RD | 1RB |
| D | 1RE | 1LE |
| E | 1LF | 0LA |
| F | --- | 1LA |

## What it does

A bouncer over a tape of words. Both ends grow like the square root of the step count.

**Where it can halt.** Only in F reading a 0. F is entered only from `E>0` (1LF), so the machine halts exactly when
`0 E>0` occurs. In the first 10^8 steps F is entered 6,990,496 times, always onto a 1 (`c/haltwatch.c`).

**The tape** (`py/snapshots.py 1e7 L 100`):

    4319542 A>0 (01)^3 (1)^4 001010 (01)^3 (1)^6 001010 (01)^3 (1)^6 (00101)^3 (1)^4 (00101)^3 0 (1)^7 ...
    9863880 A>0 1 (10)^3 (1)^7 0 (1)^5 0 (01)^3 (1)^6 (00101)^3 (1)^4 001010 (01)^3 (1)^6 (00101)^3 (1)^4 ...

Left words: `001010 (01)^3 1^6`, `(00101)^k 1^4`, `0 1^7`, a few others. Right words: built from `101`, `01101`,
`10110`, e.g. `1010 111 010110 (101)^3 (01101)^3`. Periodic stretches appear and are rewritten.

## What is proved (Lean)

Only the generated `lean/Blank.lean`: the halting configurations, no halt in 10^4 steps (kernel) and 10^7
(`native_decide`).

## Computed / observed

- No halt in 10^9 steps (`tools/c/triage.c`).
- The halt-entry counts (`c/haltwatch.c`) and the word picture (`py/snapshots.py`).

## Open, and next steps

- List the words and how each is changed by a left-moving and a right-moving pass; if the set is finite and closed,
  a closed-language (CTL-style) argument on words rather than single cells might work where window-CTL with K <= 7
  failed.
- Given only a first look.

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB1RF_1RC1LC_1LD0LE_---1LE_1RF0LB_0RA1RE`](../1RB1RF_1RC1LC_1LD0LE_---1LE_1RF0LB_0RA1RE/README.md): rename A→E, B→F, C→A, D→B, E→C, F→D; it is this table started in state C
- [`1RB1LB_1LC0LD_---1LD_1RE0LA_0RF1RD_1RA1RE`](../1RB1LB_1LC0LD_---1LD_1RE0LA_0RF1RD_1RA1RE/README.md): rename A→D, B→E, C→F, D→A, E→B, F→C; it is this table started in state D

<!-- end of related machines -->
