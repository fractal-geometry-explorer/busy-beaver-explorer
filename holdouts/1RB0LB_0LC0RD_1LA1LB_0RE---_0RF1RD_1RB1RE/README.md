# 1RB0LB_0LC0RD_1LA1LB_0RE---_0RF1RD_1RB1RE

bbchallenge id 37222.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LB |
| B | 0LC | 0RD |
| C | 1LA | 1LB |
| D | 0RE | --- |
| E | 0RF | 1RD |
| F | 1RB | 1RE |

## Status

**Open.** The macro structure below is read off long runs (heuristic: not yet stated as rules or proved); no
decision. Lean (`lean/Blank.lean`): no halt in 10^7 steps; C (`tools/c/triage.c`): none in 10^9.

## What it does

The tape is a list of numbers written as `(01)^n`, separated by single 0s (with a few markers such as `10` and
`0^3 (10)^k`): late in the run, `0 (01)^7 0 (01)^25 0 (01)^12 0 (01)^187 0 (01)^88 0 (01)^592 ...`. The head sweeps
the whole list. Only a zone near the right end changes: there, every sweep moves a fixed amount between neighbours,
alternately up and down (`541 108 368 210 264` becomes `537 112 364 214 260`), and a marker travels through the zone
taking 10 from one counter and giving 10 to another per sweep. When a counter is used up the zone moves on and the
counters behind it freeze; most of the list (the left part) has not changed for millions of steps. The right end grows
by one new cell per sweep, so the width grows like the square root of the step count. The halt is D1.

## For later

Pin down the zone's rules (which counters trade, by how much, and what happens when one reaches 0) as a map on
the list; the halting configuration is probably a counter reaching 0 at the wrong moment.

## First look

Growth class **fixed/sqrt** (left: fixed, exponent 0.0; right: sqrt,
exponent 0.44). After 1,000,000,000 steps: 83,001 cells visited (101 left of the
start, 62,179 right), 41,479 ones.

- right, step 969,730,190: `0^2 1 0^2 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0^3 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 `
- right, step 985,363,399: `0^2 1 0^2 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0^3 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 `

## Accelerated run (13 November 2026)

Observed, not proved: the accelerated simulator `rsim.py` ran 2.66x10^23 steps from blank tape without reaching a halting transition. Its tape, state and head position were equal to those of a plain C simulator at 6 checkpoints, the last at 1.31x10^10 steps. Of these steps, the part after the last checkpoint rests on the simulator alone, including 7,201 trip-level jumps: a jump applies many identical round trips at once after seeing the same tape shape recur with constant count changes, which is validated against direct simulation but not proved.

```sh
python3 holdouts/1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA1RF_0LC---/py/rsim_screen.py 1RB0LB_0LC0RD_1LA1LB_0RE---_0RF1RD_1RB1RE 400
```

## Pages

- [`pages/holdouts/1RB0LB_0LC0RD_1LA1LB_0RE---_0RF1RD_1RB1RE/explainer.html`](../../pages/holdouts/1RB0LB_0LC0RD_1LA1LB_0RE---_0RF1RD_1RB1RE/explainer.html)
- [`pages/holdouts/1RB0LB_0LC0RD_1LA1LB_0RE---_0RF1RD_1RB1RE/proof-status.html`](../../pages/holdouts/1RB0LB_0LC0RD_1LA1LB_0RE---_0RF1RD_1RB1RE/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LB_0LC0RD_1LA1LB_0RE---_0RF1RD_1RB1RE/lean/check.sh
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB1RC_1LC0RC_0RA0LD_0LE---_0LF1LD_1LC1LE`](../1RB1RC_1LC0RC_0RA0LD_0LE---_0LF1LD_1LC1LE/README.md): rename A→B, B→C, C→A, D→D, E→E, F→F and exchange left and right; it is this table started in state C, in a mirror

<!-- end of related machines -->
