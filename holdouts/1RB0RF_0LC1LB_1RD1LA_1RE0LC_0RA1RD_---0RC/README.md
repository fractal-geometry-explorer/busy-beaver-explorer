# 1RB0RF_0LC1LB_1RD1LA_1RE0LC_0RA1RD_---0RC

bbchallenge id 42170. A cousin of 1RB0RF_0LC---_1LD1LC_...: the same multi-level bouncer of (6k+3)-cell words, dense 1^(6k+1) 00 on one side of the head and sparse 011 (01)^(3k) on the other, ending in a staircase of 1^(3m) 011011(01)^j blocks on the right.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RF |
| B | 0LC | 1LB |
| C | 1RD | 1LA |
| D | 1RE | 0LC |
| E | 0RA | 1RD |
| F | --- | 0RC |

## What it does

Same emergent structure as `1RB0RF_0LC---_1LD1LC_1RE0LA_1RA1RD_0RD0RF` (different table). Step 4·10^9:

    (100)^2498 (9-cell)^662 (100)^3 (15-cell)^32 10 A>0 (15-cell)^1592 ... (21-cell)^95 ...
    ((111)^3 011011(01)^7)^39 ... (111)^m 011011(01)^j ... (m up to 22)

Level-k words (length 6k+3): dense `1^(6k+1) 00`, sparse `011 (01)^(3k)`; the head flips them as it passes.

**Proved** (`lean/Rules.lean`): `D> (011(01)^3k)^n -> (001 1^6k)^n D>` (k = 1, 2, 3), `E> (101(10)^3k)^n ->
(100 1^6k)^n E>` (k = 1, 2), `(1^7 00)^n C> 1 -> C> 1 (011010101)^n`, `D> (011)^n -> (001)^n D>`. The level-2 C
rule (65n steps) was checked by `symtm` only (Lean recursion limit).

## Halting

Only F0 halts; F is entered only from A1 (0RF): halts iff `A> 1 0`. CTL K = 3..6: halts remain; n-gram CPS fails;
no invariant mod 2..12; no halt in 10^9 steps (C).

## Notes for later

- Analyze together with the cousin `1RB0RF_0LC---_1LD1LC_1RE0LA_1RA1RD_0RD0RF`: a level-boundary rule for one
  likely transfers.
- The staircase `(111)^m 011011(01)^j` on the right: find how a sweep that reaches it changes m and j.

## Accelerated run (13 November 2026)

Observed, not proved: the accelerated simulator `rsim.py` ran 5.27x10^14 steps from blank tape without reaching a halting transition. Its tape, state and head position were equal to those of a plain C simulator at 6 checkpoints, the last at 1.08x10^10 steps. Of these steps, the part after the last checkpoint rests on the simulator alone, including 1,946 trip-level jumps: a jump applies many identical round trips at once after seeing the same tape shape recur with constant count changes, which is validated against direct simulation but not proved.

```sh
python3 holdouts/1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA1RF_0LC---/py/rsim_screen.py 1RB0RF_0LC1LB_1RD1LA_1RE0LC_0RA1RD_---0RC 400
```

## Pages

- [`pages/holdouts/1RB0RF_0LC1LB_1RD1LA_1RE0LC_0RA1RD_---0RC/explainer.html`](../../pages/holdouts/1RB0RF_0LC1LB_1RD1LA_1RE0LC_0RA1RD_---0RC/explainer.html)
- [`pages/holdouts/1RB0RF_0LC1LB_1RD1LA_1RE0LC_0RA1RD_---0RC/proof-status.html`](../../pages/holdouts/1RB0RF_0LC1LB_1RD1LA_1RE0LC_0RA1RD_---0RC/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RF_0LC1LB_1RD1LA_1RE0LC_0RA1RD_---0RC/lean/check.sh
```

## Write-only test at the left end (27 November 2026)

The end-signature screen of 27 November listed this machine's left end as a candidate for a finite end controller
beside a write-only bulk, the structure of DeepMind's proof of 1RB0LD_1LC0RE_---1LD_1LE1LA_1RA0LF_1LC1RE. The direct
test (10^9 steps; a trip leaves a 24-cell window at the end and goes more than 1,000 cells further): **fails**.
Computed, not proved: 9,006 deep trips from the left end fall on 16 end words, and 8,854 of them have an end word with more than one return state (A, B, C); 64 more cells of context still leave 8,653. The head brings back a bit that is the content of the bulk. Trips take 8.4 steps per cell of depth: these are sweeps. Details and the other 11 candidates: [`recent-proofs/followup/write-only-test.md`](../recent-proofs/followup/write-only-test.md).

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0LE_0RC1RA_1RD0RF_0LE1LD_1RA1LC_---0RE`](../1RB0LE_0RC1RA_1RD0RF_0LE1LD_1RA1LC_---0RE/README.md): rename A→C, B→D, C→E, D→A, E→B, F→F; it is this table started in state D
- [`1RB1LD_1RC0LA_0RD1RB_1RE0RF_0LA1LE_---0RA`](../1RB1LD_1RC0LA_0RD1RB_1RE0RF_0LA1LE_---0RA/README.md): rename A→D, B→E, C→A, D→B, E→C, F→F; it is this table started in state C

<!-- end of related machines -->
