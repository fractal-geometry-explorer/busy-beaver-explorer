# 1RB1LD_1RC0RC_1LD1RB_1LF0LE_0LA1LE_---1LB

bbchallenge id 117020. One of the six-state holdouts whose halting from blank tape is open. A bouncer whose slowly growing zone has not been decoded.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LD |
| B | 1RC | 0RC |
| C | 1LD | 1RB |
| D | 1LF | 0LE |
| E | 0LA | 1LE |
| F | --- | 1LB |

## What it does

A **bouncer with a zone**. Read left to right, the tape is a short zone (fewer than 30 cells for the first 2,500
steps, then between 77 and 102 cells from step 2,667 to at least 3·10^8) followed by the word `111011` repeated:

```
step 29,979,814:  1^9 0 1^3 (01)^3 1^2 010 1^11 010 1^7 0 1^3 (01)^4 1^4 0 1^5 0 (111011)^4 (101111)^1287 10 1^3
```

The head sweeps from the zone to the right end and back; the repeated part is crossed by shift rules (for example
B moving right turns each `111011` into `110101`, C moving right turns it into `101110`), and every sweep adds 6
cells (one more unit) at the right end. So the right side grows like the square root of the step count and the
zone, which is rewritten on every visit, hardly grows at all (the left side is the triage's "exp" side: 24 cells left
of the start after 10^9 steps).

The machine halts only in F reading 0: D reads a 0, writes 1 and moves left onto another 0.

## Does it halt?

Unknown. The zone's successor at each visit should depend only on the zone and on the phase of the right end (the
units are all alike; not checked), so the question is probably whether the orbit of a finite-word map, whose words grow very slowly, reaches a halting word; that map has not been
extracted. Direct simulation: no halt in 10^11 steps. **Open.**

## For later

Stopped at: the shape (above) only. Next steps:

1. Extract the zone map: at each right-end turn, cut the tape at the start of the maximal `(111011)^k 1` suffix
   (allow for the rotated forms) and record the zone; check that the next zone is a function of the zone (and the right end's phase) by
   simulating the zone in front of a long block of units.
2. The zone itself seems to contain a second, slower level (at step 2,667 it holds `(111110)^k`-like runs):
   decode that level, as a counter, before trying to iterate the map far.
3. Prove the bulk sweep with `bbtools.symtm` (contexts for the zone) and the zone transitions as finite runs.

## Status

Open. Lean (`lean/Blank.lean`): the halting configurations (`step_none_iff`), no halt in 10,000 steps by the
kernel, in 10,000,000 by `native_decide`. C (`tools/c/tmrun.c`): no halt in 10^11 steps.

## Pages

- [`pages/holdouts/1RB1LD_1RC0RC_1LD1RB_1LF0LE_0LA1LE_---1LB/explainer.html`](../../pages/holdouts/1RB1LD_1RC0RC_1LD1RB_1LF0LE_0LA1LE_---1LB/explainer.html)
- [`pages/holdouts/1RB1LD_1RC0RC_1LD1RB_1LF0LE_0LA1LE_---1LB/proof-status.html`](../../pages/holdouts/1RB1LD_1RC0RC_1LD1RB_1LF0LE_0LA1LE_---1LB/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LD_1RC0RC_1LD1RB_1LF0LE_0LA1LE_---1LB/lean/check.sh
gcc -O2 -o /tmp/tmrun tools/c/tmrun.c && /tmp/tmrun 1RB1LD_1RC0RC_1LD1RB_1LF0LE_0LA1LE_---1LB 100000000000     # running 100000000000 490714
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0RB_1LC1RA_1LF0LD_0LE1LD_1RA1LC_---1LA`](../1RB0RB_1LC1RA_1LF0LD_0LE1LD_1RA1LC_---1LA/README.md): rename A→E, B→A, C→B, D→C, E→D, F→F; it is this table started in state B

<!-- end of related machines -->
