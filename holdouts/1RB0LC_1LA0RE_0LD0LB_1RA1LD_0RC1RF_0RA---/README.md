# 1RB0LC_1LA0RE_0LD0LB_1RA1LD_0RC1RF_0RA---

bbchallenge id 67956.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LC |
| B | 1LA | 0RE |
| C | 0LD | 0LB |
| D | 1RA | 1LD |
| E | 0RC | 1RF |
| F | 0RA | --- |

## Status

**Open.** The macro structure below is read off long runs (heuristic: not yet stated as rules or proved); no
decision. Lean (`lean/Blank.lean`): no halt in 10^7 steps; C (`tools/c/triage.c`): none in 10^9.

## What it does

The tape is a sequence of units. At level 1 the unit is `U = (010)^17 (100)^16 1` (100 cells); at level 2
`V = (010)^55 (100)^54 1` (328 cells); a level-3 block `(010)^1016 (100)^1015 1` also appears. In one phase the head
consumes a reservoir `(010)^n` at the right end, about 6.5 copies per left-end visit, and emits one U at the left every
few visits (`U^2 ... (010)^113`, `U^6 ... (100)^78`, `U^11 ... (100)^11`); when the reservoir is gone the next level is
rearranged (`V^12` blocks, a new reservoir) and the emission starts over. Unit sizes grow by about ×3 per level
(17 → 55), so this is a hierarchy of counters. The halt is F1.

## For later

Prove the one-level rule (a reservoir of n gives about n/6.5 units U), then the level-to-level step; whether the
hierarchy is regular decides it.

## First look

Growth class **fixed/sqrt** (left: fixed, exponent 0.438; right: sqrt,
exponent 0.603). After 1,000,000,000 steps: 84,949 cells visited (2,283 left of the
start, 62,592 right), 45,874 ones.

- right, step 969,924,486: `0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0^2 1^2 0 1^2 0 1 0 1 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0^2 1^2 0 1^2 0 1 0 1 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0^2 1^2 0 1^2 0 1 0 1 0 1^2 0 1^2 0 1^2 `
- right, step 985,637,609: `0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0^2 1^2 0 1^2 0 1 0 1 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0^2 1^2 0 1^2 0 1 0 1 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0^2 1^2 0 1^2 0 1 0 1 0 1^2 0 1^2 0 1^2 `

## Pages

- [`pages/holdouts/1RB0LC_1LA0RE_0LD0LB_1RA1LD_0RC1RF_0RA---/explainer.html`](../../pages/holdouts/1RB0LC_1LA0RE_0LD0LB_1RA1LD_0RC1RF_0RA---/explainer.html)
- [`pages/holdouts/1RB0LC_1LA0RE_0LD0LB_1RA1LD_0RC1RF_0RA---/proof-status.html`](../../pages/holdouts/1RB0LC_1LA0RE_0LD0LB_1RA1LD_0RC1RF_0RA---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LC_1LA0RE_0LD0LB_1RA1LD_0RC1RF_0RA---/lean/check.sh
```
