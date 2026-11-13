# 1RB1RD_1LC0RF_1LD0LB_1RE0RB_---1RA_0LA1RC

bbchallenge id 92170. One of the six-state holdouts whose halting from blank tape is open (group G07).
Family: **nested counters with growth about 15/7, halting only at the right edge (Lean)**. Decision: **open**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RD |
| B | 1LC | 0RF |
| C | 1LD | 0LB |
| D | 1RE | 0RB |
| E | --- | 1RA |
| F | 0LA | 1RC |

## What it does

With `a = 1111110`, the tape is a list of levels `1^X a 00 a^Y` (plus a few short words). On the last level, every 8
visits of the right end (state C):  `1^X a 00 a^Y  ->  1^(X+15) a 00 a^(Y-1)`  (step 1.589e9: X = 30874, 30889, ...,
31009 as Y runs from 9 to 0). When Y = 0 the head rebuilds runs of ones into runs of words (about one word per 7 ones)
and another level becomes active (e.g. `1^54794 a 00 a^10924` at step 9.5e9). Sizes grow by about 15/7 per round,
with remainders mod 7 steering the rebuilds: a multi-counter Collatz-like system.

Sample (step 7,293,164,582, the 50,000th visit of the right end in C, 133,715 cells):

    11111 000 a 1111 a 00 1^39759 a 00 a^7934 1111 a 00 1^34254 a 00 a^584 11111 0 11111 0000 10

The level cycle was checked symbolically with `bbtools.symtm`: the head crosses the block `a^Y` (re-bracketed as
`(0111111)^Y`) and the ones grow by 10 in some visits, but the 8 visits do not form a single shift-rule run (the
word of the block changes as a defect walks through it), so the cycle is not proved yet.

## Where it can halt

The halting transition is E0, reached only as D0 -> 1RE. A closed tape language from windows of 4 cells
(`lean/EdgeCert.lean`, checked by `decide` in `lean/Edge.lean`) proves that **the machine halts from blank tape
exactly when E steps onto the blank region past the right end of the tape** (`halts_iff_edge`), that is, when D
reads the blank cell just right of the tape. The right end is where the active level works (state C visits it
about every 100 steps), so a halt is a question of which state the head is in there, decided by the remainders of
the rebuilds.

## Status

Open.

- **Kernel:** `step_none_iff`, `blank_runs_kernel` (`lean/Blank.lean`); `halts_iff_edge` (`lean/Edge.lean`).
  **native_decide:** `blank_runs_native` (10^7 steps).
- **Trusted:** no halt in 1.2·10^10 steps (`tools/c`, direct run).
- **Heuristic:** the level cycle and the rebuild rule (read off the run).

## Next steps

Find the exact 8-visit cycle (the block's word changes as a defect moves through it: state it with the defect's
position as a second count) and prove it with `bbtools.symtm.prove` and fit the rebuild map by remainder, as for
1RB1RD_1LC0LE_1RA0LB_1RA1RF_0RA0RC_1RE---.

## Pages

- [`pages/holdouts/1RB1RD_1LC0RF_1LD0LB_1RE0RB_---1RA_0LA1RC/explainer.html`](../../pages/holdouts/1RB1RD_1LC0RF_1LD0LB_1RE0RB_---1RA_0LA1RC/explainer.html)
- [`pages/holdouts/1RB1RD_1LC0RF_1LD0LB_1RE0RB_---1RA_0LA1RC/proof-status.html`](../../pages/holdouts/1RB1RD_1LC0RF_1LD0LB_1RE0RB_---1RA_0LA1RC/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RD_1LC0RF_1LD0LB_1RE0RB_---1RA_0LA1RC/lean/check.sh
(cd tools/py && python3 -m bbtools.ctl 1RB1RD_1LC0RF_1LD0LB_1RE0RB_---1RA_0LA1RC 4 lean H92170 Blank) | diff - holdouts/1RB1RD_1LC0RF_1LD0LB_1RE0RB_---1RA_0LA1RC/lean/EdgeCert.lean
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0RE_1LC0LE_---1LD_1LE1LB_1RA0LF_0RD1LA`](../1RB0RE_1LC0LE_---1LD_1LE1LB_1RA0LF_0RD1LA/README.md): rename A→D, B→E, C→A, D→B, E→C, F→F and exchange left and right; it is this table started in state C, in a mirror

<!-- end of related machines -->
