# 1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RC---

bbchallenge id 85227. One of the six-state holdouts whose halting from blank tape is open (group G11).

Family **G11-Y** (two counters ticking together, `1RB0LB_0RC0LD` and relatives): this machine is the reference machine of the family.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LB |
| B | 0RC | 0LD |
| C | 1LD | 1RE |
| D | 0LA | 0RF |
| E | 0RD | 1RF |
| F | 0RC | --- |

## What it does

The tape is, most of the time, `L · engine · R`. Every visit of the head to the engine (an *event*) adds 1 to two binary
counters, one on each side. In the reference machine `1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RC---`, `L` is in 4-cell blocks (`0101` = 1,
`0001` = 0, lowest digit next to the engine) and `R` has one cell per digit, three cells apart (cells 9, 12, 15, … right
of the head), lowest digit nearest the engine. Between some digits of `R` there are fixed stretches (junk) that the carries cross.

- **Left side: clockwork.** When `L` overflows the carry reaches the left end, the tape grows by two cells and `L`
  restarts. The busiest cell (the lowest digit of `L`) turns exactly 2^k times between consecutive left-end extensions, each power twice: 64, 64, 128, 128, …, 2^24
  (first 1.5·10^9 steps, `ymax.c`).
- **The junk.** The change counts per cell (`chg.c`: how often each cell changes between consecutive events over a
  whole period) halve from one digit to the next, with junk stretches between some digits. The junk is written when a
  carry reaches the end of the tape (at irregular event counts); how is not decoded.
- **Where it can halt.** Only in F reading 1; F is entered from D1 (0RF) and E1 (1RF). After D1, used about 4·10^7 times in 10^9 steps, the head has read a 0 every time: part of the counters' ordinary carry. E1 is the rare one: 306 uses in the first 10^9 steps; in the reference machine E1 fires when a carry of the right counter reaches a digit for the first time since the last left-end visit: right after the visit at step 2,188,604 it fires at steps 2,188,675, 2,188,767, 2,188,882, 2,189,117, 2,189,592, 2,190,547, 2,192,462, three cells further right each time and after twice the wait each time, as a binary counter reaching new digits. So one way to halt is a carry meeting a fresh digit followed by a 1, the other an ordinary carry finding a 1 after D1.

The family: `1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RC---` (reference), `1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RB_0RC---` (the same run, checked cell for cell for
10^10 steps), `1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD0LC_0RC---`, `1RB0LB_0RC0LD_1LD1RE_0LA0RF_1RB0RD_0RB---`,
`1RB0LB_0RC0LF_1LD1RE_0LA0RB_0RD0RF_0LA---` (left-end extensions after 2^k events, each twice, within a few hundred
steps of each other), `1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA0RE_1RE---` and `1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA1RB_1RE---` (same
right part at the left-end visits, 3·2^k), and the mirror case `1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD1RF_1LA---`.

## Events, third round

The reference's event theorems (`../1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RB_0RC---/py/events.py`) prove here unchanged (`lean/Events.lean`,
10 theorems): they never use E1, the one transition where the two machines differ. E1 = 1RF here; F then reads a 0
(every time so far) and F0 = 0RC = B0, so `L E> 1 0 R` → `L 1 0 C> R` in 2 steps exactly as in the reference
(`y_e1_same`). The event tapes are the reference's (2,000,000 events compared) and so is the coverage: 95.2% of the
1,048,574 events of the first 10^8 steps are instances of the theorems. This machine halts if an E1 or a D1 is ever
followed by a 1; the reference only after D1.

## Status

Open. Lean, kernel only: the halting configurations and 10^4 steps (`lean/Blank.lean`), the sweeps of the run and the right counter's carry for every number of ones (`r_up`, `r_down`, `event0`) (`lean/Rules.lean`), the increments of both counters and the junk crossings, the reference's 9 theorems plus `y_e1_same` (`lean/Events.lean`). `native_decide`: 10^7 steps. C: no halt in
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

Growth class **exp/exp** (left: exp, exponent 0.073; right: exp,
exponent 0.067). After 1,000,000,000 steps: 252 cells visited (88 left of the
start, 153 right), 78 ones.

- left, step 553,687,211: `B>0 0^2 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0^2 1 0 1 0^4 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0^4 1 0^2 1 0 1 0^4 1 `
- left, step 810,905,241: `B>0 0^2 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0^4 1 0^2 1 0 1 0^4 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0 1 0 1 0 1 0 1 0 1 0 1 0^2 1 0 1 0^7 1 0 1 0^`
- right, step 551,600,578: `1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0^3 1 0^3 1 0 1 0 1 0^3 1 0^3 1 0 1 0 1 0^3 1 0^3 1 0^3 1 0^3 1 0^3 1 0^3 1 0^3 1 0^3 1 0^3 1 0^3 1^2 0 1 0 1 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1 0 1 0 1 0^3 1 0^3 1 0 1 0 1^2 0 1^2 0 1 0 1 0 1^2 0 1^2 0 1 0 1 0 1^2 0 1^2 0 `
- right, step 946,792,441: `1 0 1 0^3 1 0 1 0 1 0 1 0 1 0^3 1 0^3 1 0^3 1 0^3 1 0^3 1 0 1 0 1 0 1 0 1 0^3 1 0^3 1 0^3 1 0^3 1 0 1 0 1 0^3 1 0^3 1 0^3 1 0^3 1 0^3 1 0^3 1 0 1 0 1 0^3 1^2 0 1 0 1 0 1^2 0 1^2 0 1 0 1 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1 0 1 0 1 0^3 1 0 1 0 1^2 0 1^2 0 1^2 0 1 0^3 1^2 0 1^2 0 1 0 1 0 1^2 `

## Pages

- [`pages/holdouts/1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RC---/explainer.html`](../../pages/holdouts/1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RC---/explainer.html)
- [`pages/holdouts/1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RC---/proof-status.html`](../../pages/holdouts/1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RC---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RC---/lean/check.sh
```
