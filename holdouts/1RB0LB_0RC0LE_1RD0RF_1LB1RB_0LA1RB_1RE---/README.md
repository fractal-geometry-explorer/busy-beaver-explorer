# 1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA1RB_1RE---

bbchallenge id 60498. One of the six-state holdouts whose halting from blank tape is open (group G11).

Family **G11-Y** (two counters ticking together, `1RB0LB_0RC0LD` and relatives): this machine is a relative in different clothes, the twin of 1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA0RE_1RE--- (E1 = 1RB against 0RE): the same clockwork left side (3·2^k turns, each count twice, the second time 3 less) and the same tapes (at its left-end visit at step 12,788,128 its tape is exactly the twin's at step 14,008,454).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LB |
| B | 0RC | 0LE |
| C | 1RD | 0RF |
| D | 1LB | 1RB |
| E | 0LA | 1RB |
| F | 1RE | --- |

## What it does

The tape is, most of the time, `L · engine · R`. Every visit of the head to the engine (an *event*) adds 1 to two binary
counters, one on each side. In the reference machine `1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RC---`, `L` is in 4-cell blocks (`0101` = 1,
`0001` = 0, lowest digit next to the engine) and `R` has one cell per digit, three cells apart (cells 9, 12, 15, … right
of the head), lowest digit nearest the engine. Between some digits of `R` there are fixed stretches (junk) that the carries cross.

- **Left side: clockwork.** When `L` overflows the carry reaches the left end, the tape grows by two cells and `L`
  restarts. The busiest cell (the lowest digit of `L`) turns 3·2^k times between consecutive left-end extensions, each count twice: 48, 96, 96, 192, 192, …, 3·2^22
  (first 1.5·10^9 steps, `ymax.c`).
- **The junk.** The change counts per cell (`chg.c`: how often each cell changes between consecutive events over a
  whole period) halve from one digit to the next, with junk stretches between some digits. The junk is written when a
  carry reaches the end of the tape (at irregular event counts); how is not decoded.
- **Where it can halt.** Only in F reading 1; F is entered from C1 (0RF) only. After C1, used about 3.1·10^7 times in 10^9 steps, the head has read a 0 every time (F0 is used exactly as often); no transition is rare. Halting would need that ordinary step to find a 1.

The family: `1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RC---` (reference), `1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RB_0RC---` (the same run, checked cell for cell for
10^10 steps), `1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD0LC_0RC---`, `1RB0LB_0RC0LD_1LD1RE_0LA0RF_1RB0RD_0RB---`,
`1RB0LB_0RC0LF_1LD1RE_0LA0RB_0RD0RF_0LA---` (left-end extensions after 2^k events, each twice, within a few hundred
steps of each other), `1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA0RE_1RE---` and `1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA1RB_1RE---` (same
right part at the left-end visits, 3·2^k), and the mirror case `1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD1RF_1LA---`.

## Events, third round

The twin of `1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA0RE_1RE---` (E1 = 1RB instead of 0RE), with the same words. As in
`1RB0LB_0RC0LD_1LD1RE_0LA0RF_1RB0RD_0RB---`, A is on cell 3 only in phase 1: one event is a left increment followed
by a right increment in one pass. `lean/Events.lean` (5 theorems, every size). Coverage: 90.5% of the 513,702 events
of the first 10^8 steps.

## Status

Open. Lean, kernel only: the halting configurations and 10^4 steps (`lean/Blank.lean`), the sweeps of the run (`lean/Rules.lean`), the left-and-right increments in one pass, 5 theorems (`lean/Events.lean`). `native_decide`: 10^7 steps. C: no halt in
10^11 steps.

## Next steps

Decode what a carry writes when it reaches the end of the tape, so that the junk after each visit is a formula in the
counters; then decide whether a carry can ever find a 1 where it has always found a 0.

## Scripts

- `py/events.py` writes `lean/Events.lean` (`--coverage STEPS [SHOW]`: match every event of the run against the rules).
`py/rules.py` writes `lean/Rules.lean` (with `../1RB---_0LC0RB_1RA1LD_0RD1LE_1LF0LA_1LB0LE/py/g11rules.py`). The C
tools of the batch are in `../1RB---_0LC0RB_1RA1LD_0RD1LE_1LF0LA_1LB0LE/c/` (`gcc -O2 -o X X.c`): `ymax.c` (turns of
the busiest cell between end extensions), `chg.c` (change counts per cell between events), `usage.c` (transition
counts), `lockstep.c` (two machines side by side), `trlog.c` (every use of one transition), `longrun.c` (a long run).


## First look

Growth class **exp/exp** (left: exp, exponent 0.08; right: exp,
exponent 0.071). After 1,000,000,000 steps: 248 cells visited (88 left of the
start, 152 right), 100 ones.

- left, step 529,197,137: `B>0 0^3 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0^4 1 0^26 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0^2 1 0 1 0^4 1 0^2 1 0^2 1 0 1 0 1 0^2 1 0 1 0^4 1 0^2 1 0 1 0^4 1 0^5 1`
- left, step 732,376,883: `B>0 0^3 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0^2 1 0 1 0^4 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0^4 1 0^2 1 0 1 0^4 1 `
- right, step 678,853,833: `1 0 1^3 0 1^2 0^2 1^3 0 1^3 0 1^3 0 1^3 0 1^2 0^2 1^2 0^2 1^3 0 1^2 0^2 1^2 0^2 1^3 0 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0 1^3 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^3 0 1^2 0^2 1^2 0^2 1^3 0 1^2 0 1^2 0 1^3 0 1^2 0 1^2 0 1^3 0 1^2 `
- right, step 729,649,043: `1 0 1^3 0 1^3 0 1^3 0 1^3 0 1^3 0 1^3 0 1^2 0^2 1^2 0^2 1^3 0 1^2 0^2 1^2 0^2 1^3 0 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0 1^3 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^3 0 1^2 0^2 1^2 0^2 1^3 0 1^2 0 1^2 0 1^3 0 1^2 0 1^2 0 1^3 0 1^2 0 `

## Pages

- [`pages/holdouts/1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA1RB_1RE---/explainer.html`](../../pages/holdouts/1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA1RB_1RE---/explainer.html)
- [`pages/holdouts/1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA1RB_1RE---/proof-status.html`](../../pages/holdouts/1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA1RB_1RE---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA1RB_1RE---/lean/check.sh
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same tapes at another pace (observed, not proved).** Leave the states aside and compare only the tape and the place of the head. Then a large part of the first 10^7 configurations of this machine are configurations of the machines below, in the same order and up to the end of the run. The steps at which they occur differ, the tables are not renamings of each other, and equal tapes with different states may be continued differently, so this does not tie the halting questions together.

- [`1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA0RE_1RE---`](../1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA0RE_1RE---/README.md): 9,132,095 configurations, the last at step 9,132,094 here and step 10,000,000 there

<!-- end of related machines -->
