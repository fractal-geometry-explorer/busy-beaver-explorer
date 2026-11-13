# 1RB0RC_0LC0LE_1RA0RD_1LB1RF_1LC1LB_0RA---

bbchallenge id 32304. One of the six-state holdouts whose halting from blank tape is open (group G13). Family: **counters of 1^2 0^2 words and zero gaps**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RC |
| B | 0LC | 0LE |
| C | 1RA | 0RD |
| D | 1LB | 1RF |
| E | 1LC | 1LB |
| F | 0RA | --- |

## What it does

Write b for 1^2 0^2 and a for 1 0. When the head is at the right end in state D the tape ends like 1 0^2 b 1^2 0^22 1^2 0 1 0^2 b^p a 1 0^2 1 0^3 1 0^2 a^2 1^2 0 a^q D>0. Between samples 400 apart, p falls by 450 and q rises by 1,500 (p = 7,597 and q = 3,470 at step 460,944,399; p = 1,747 and q = 22,970 at step 942,980,499).

Further left are gaps of 0s (0^37, 0^22, ...) that shrink over longer times, so they look like higher digits. The tape grows to the right like t0.66.

### Halting

The machine halts when it reads a 1 in state F (F1 is the halting transition). F is entered from D on a 1 (D1 = 1RF).

## Phase 2 results

`lean/Rules.lean` proves four conversion cycles for every length (`cycA`..`cycD`: nine 4-cell words into fifteen
pairs, in four alignments). `py/coverage.py 1000000000`: 0.9717 of the steps lie inside jumps of these shapes. The
phase changes between them are not mapped.

## Status

Open. Lean (`lean/Blank.lean`): the halting configurations, no halt in 10^4 steps (kernel) and 10^7 (`native_decide`). C: no halt in 10^9 steps. Lean (`lean/Rules.lean`, kernel): the four conversion cycles `cycA`..`cycD` (nine 4-cell words into fifteen pairs), for every length and any tape on the left. Trusted: they cover 97.17% of the first 10^9 steps (`py/coverage.py`). The phase changes are observed, not proved.

## Later

1. Prove the conversion of 1^2 0^2 words into 10 pairs with `bbtools.symtm`.
2. Find what happens when p reaches 0 and how the gaps 0^k further left are decremented.
3. Write the run as a counter on (gaps, runs) and look for an invariant.

## Pages

- [`pages/holdouts/1RB0RC_0LC0LE_1RA0RD_1LB1RF_1LC1LB_0RA---/explainer.html`](../../pages/holdouts/1RB0RC_0LC0LE_1RA0RD_1LB1RF_1LC1LB_0RA---/explainer.html)
- [`pages/holdouts/1RB0RC_0LC0LE_1RA0RD_1LB1RF_1LC1LB_0RA---/proof-status.html`](../../pages/holdouts/1RB0RC_0LC0LE_1RA0RD_1LB1RF_1LC1LB_0RA---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RC_0LC0LE_1RA0RD_1LB1RF_1LC1LB_0RA---/lean/check.sh
python3 holdouts/1RB0RC_0LC0LE_1RA0RD_1LB1RF_1LC1LB_0RA---/py/coverage.py 1000000000
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB1RD_1LC0LE_1LD0LB_0RB0RA_1RD1LF_0LC---`](../1RB1RD_1LC0LE_1LD0LB_0RB0RA_1RD1LF_0LC---/README.md): rename A→C, B→D, C→B, D→E, E→A, F→F and exchange left and right; it is this table started in state E, in a mirror
- [`1RB0RD_1RC0RA_0LA0LE_1LC1RF_1LA1LC_0RB---`](../1RB0RD_1RC0RA_0LA0LE_1LC1RF_1LA1LC_0RB---/README.md): rename A→B, B→C, C→A, D→D, E→E, F→F; it is this table started in state C

<!-- end of related machines -->
