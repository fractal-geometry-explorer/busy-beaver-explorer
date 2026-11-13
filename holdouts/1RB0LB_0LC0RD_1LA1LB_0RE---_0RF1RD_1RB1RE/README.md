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

## Pages

- [`pages/holdouts/1RB0LB_0LC0RD_1LA1LB_0RE---_0RF1RD_1RB1RE/explainer.html`](../../pages/holdouts/1RB0LB_0LC0RD_1LA1LB_0RE---_0RF1RD_1RB1RE/explainer.html)
- [`pages/holdouts/1RB0LB_0LC0RD_1LA1LB_0RE---_0RF1RD_1RB1RE/proof-status.html`](../../pages/holdouts/1RB0LB_0LC0RD_1LA1LB_0RE---_0RF1RD_1RB1RE/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LB_0LC0RD_1LA1LB_0RE---_0RF1RD_1RB1RE/lean/check.sh
```
