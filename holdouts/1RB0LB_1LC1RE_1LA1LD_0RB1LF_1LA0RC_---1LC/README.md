# 1RB0LB_1LC1RE_1LA1LD_0RB1LF_1LA0RC_---1LC

bbchallenge id 24566.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LB |
| B | 1LC | 1RE |
| C | 1LA | 1LD |
| D | 0RB | 1LF |
| E | 1LA | 0RC |
| F | --- | 1LC |

## Status

**Open.** The macro structure below is read off long runs (heuristic: not yet stated as rules or proved); no
decision. Lean (`lean/Blank.lean`): no halt in 10^7 steps; C (`tools/c/triage.c`): none in 10^9.

## What it does

The tape is made almost entirely of one periodic pattern, the word `110101` read in different phases
(`011101`, `101110`, `111010`, `010111`, `101011`), cut into segments by short defects such as `1^3 (01)^3`,
`(1101)^3`, `1 (10)^3`. Late in the run: `1^4 (01)^3 (110101)^23 (1101)^3 (011101)^57 (110101)^9 (011101)^100 1
(101110)^149 1^3 (01)^3 (110101)^420 ...`. Each sweep moves the defects, so one segment loses a copy while its
neighbour gains one (`(011101)^101 ... (101110)^151` becomes `(011101)^100 ... (101110)^149`), and the last segment
grows by about 7 copies per sweep. The halt is F0, reached only if a defect
meets a pattern not yet seen.

## For later

Classify the defects (there seem to be about six kinds) and write how each moves per sweep; this is a
cellular-automaton-like bouncer and may admit a closed tape language once the defect grammar is known.

## First look

Growth class **fixed/sqrt** (left: fixed, exponent 0.071; right: sqrt,
exponent 0.502). After 1,000,000,000 steps: 49,167 cells visited (45 left of the
start, 38,381 right), 35,800 ones.

- right, step 970,110,412: `1^4 0 1 0 1 0 1^3 0 1 0 1^3 0 1 0 1^3 0 1 0 1^3 0 1 0 1^3 0 1 0 1^3 0 1 0 1^3 0 1 0 1^3 0 1 0 1^3 0 1 0 1^3 0 1 0 1^3 0 1 0 1^3 0 1 0 1^3 0 1 0 1^3 0 1 0 1^3 0 1 0 1^3 0 1 0 1^3 0 1 0 1^3 0 1 0 1^3 0 1 0 1^3 0 1^3 0 1^3 0 1 0 1^3 0 1 0 1^3 0 1 0 1^3 0 1 0 1^3 0 1 0 1^3 0 1 0 1^3 0 1 0 1^3 0 1 0 1^3 `
- right, step 985,778,694: `1^4 0 1 0 1 0 1^3 0 1 0 1^3 0 1 0 1^3 0 1 0 1^3 0 1 0 1^3 0 1 0 1^3 0 1 0 1^3 0 1 0 1^3 0 1 0 1^3 0 1 0 1^3 0 1 0 1^3 0 1 0 1^3 0 1 0 1^3 0 1 0 1^3 0 1 0 1^3 0 1 0 1^3 0 1 0 1^3 0 1 0 1^3 0 1 0 1^3 0 1 0 1^3 0 1^3 0 1^3 0 1 0 1^3 0 1 0 1^3 0 1 0 1^3 0 1 0 1^3 0 1 0 1^3 0 1 0 1^3 0 1 0 1^3 0 1 0 1^3 `

## Pages

- [`pages/holdouts/1RB0LB_1LC1RE_1LA1LD_0RB1LF_1LA0RC_---1LC/explainer.html`](../../pages/holdouts/1RB0LB_1LC1RE_1LA1LD_0RB1LF_1LA0RC_---1LC/explainer.html)
- [`pages/holdouts/1RB0LB_1LC1RE_1LA1LD_0RB1LF_1LA0RC_---1LC/proof-status.html`](../../pages/holdouts/1RB0LB_1LC1RE_1LA1LD_0RB1LF_1LA0RC_---1LC/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LB_1LC1RE_1LA1LD_0RB1LF_1LA0RC_---1LC/lean/check.sh
```
