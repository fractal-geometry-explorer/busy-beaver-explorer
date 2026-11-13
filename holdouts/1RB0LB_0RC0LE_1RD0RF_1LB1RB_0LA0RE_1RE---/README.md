# 1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA0RE_1RE---

bbchallenge id 32161. One of the six-state holdouts whose halting from blank tape is open (group G11).

Family **G11-Y** (two counters ticking together, `1RB0LB_0RC0LD` and relatives): this machine is a relative in different clothes: its left counter has 4-cell digits `x011`, its left-end extensions come after exactly 3·2^k turns of the busiest cell, each count twice, and at its left-end visits the tape is that of the reference family: at step 14,008,454 its 183-cell tape agrees with that of 1RB0LB_0RC0LF_1LD1RE_0LA0RB_0RD0RF_0LA--- at step 9,617,068 in all cells but the first two.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LB |
| B | 0RC | 0LE |
| C | 1RD | 0RF |
| D | 1LB | 1RB |
| E | 0LA | 0RE |
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
- **Where it can halt.** Only in F reading 1; F is entered from C1 (0RF) only. After C1, used about 2.9·10^7 times in 10^9 steps, the head has read a 0 every time (F0 is used exactly as often). Unlike the other members this machine has no rare transition: every transition is used more than 10^7 times in 10^9 steps. Halting would need that ordinary step to find a 1.

The family: `1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RC---` (reference), `1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RB_0RC---` (the same run, checked cell for cell for
10^10 steps), `1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD0LC_0RC---`, `1RB0LB_0RC0LD_1LD1RE_0LA0RF_1RB0RD_0RB---`,
`1RB0LB_0RC0LF_1LD1RE_0LA0RB_0RD0RF_0LA---` (left-end extensions after 2^k events, each twice, within a few hundred
steps of each other), `1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA0RE_1RE---` and `1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA1RB_1RE---` (same
right part at the left-end visits, 3·2^k), and the mirror case `1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD1RF_1LA---`.

## Events, third round

The same two counters as the reference `1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RB_0RC---`, in other words: left digits `0110` = 0, `0111` = 1
next to the block `011001`; on the right the phase cell, the block `001010000` and the right counter one cell per digit,
three cells apart, with junk units `1010000` between digits, exactly the reference's right side. `lean/Events.lean`
(6 theorems, every size): the left increment (22n+34 steps), the right increments (42; 6k+48), and carries across
junk units. Coverage: 95.5% of the 879,588 events of the first 10^8 steps (right1 92,325 and junk_jk 1,733 times, the
same counts as in the reference).

## Status

Open. Lean, kernel only: the halting configurations and 10^4 steps (`lean/Blank.lean`), the sweeps of the run (`lean/Rules.lean`), the increments of both counters and the junk crossings, 6 theorems (`lean/Events.lean`). `native_decide`: 10^7 steps. C: no halt in
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

Growth class **exp/exp** (left: exp, exponent 0.075; right: exp,
exponent 0.067). After 1,000,000,000 steps: 248 cells visited (86 left of the
start, 149 right), 98 ones.

- left, step 579,891,093: `B>0 0^3 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0^4 1 0^26 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0^2 1 0 1 0^4 1 0^2 1 0^2 1 0 1 0 1 0^2 1 0 1 0^4 1 0^2 1 0 1 0^4 1 0^5 1`
- left, step 804,526,293: `B>0 0^3 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0^2 1 0 1 0^4 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0^4 1 0^2 1 0 1 0^4 1 `
- right, step 745,351,313: `1 0 1^3 0 1^2 0^2 1^3 0 1^3 0 1^3 0 1^3 0 1^2 0^2 1^2 0^2 1^3 0 1^2 0^2 1^2 0^2 1^3 0 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0 1^3 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^3 0 1^2 0^2 1^2 0^2 1^3 0 1^2 0 1^2 0 1^3 0 1^2 0 1^2 0 1^3 0 1^2 `
- right, step 801,510,397: `1 0 1^3 0 1^3 0 1^3 0 1^3 0 1^3 0 1^3 0 1^2 0^2 1^2 0^2 1^3 0 1^2 0^2 1^2 0^2 1^3 0 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0 1^3 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^3 0 1^2 0^2 1^2 0^2 1^3 0 1^2 0 1^2 0 1^3 0 1^2 0 1^2 0 1^3 0 1^2 0 `

## Pages

- [`pages/holdouts/1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA0RE_1RE---/explainer.html`](../../pages/holdouts/1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA0RE_1RE---/explainer.html)
- [`pages/holdouts/1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA0RE_1RE---/proof-status.html`](../../pages/holdouts/1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA0RE_1RE---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA0RE_1RE---/lean/check.sh
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same tapes at another pace (observed, not proved).** Leave the states aside and compare only the tape and the place of the head. Then a large part of the first 10^7 configurations of this machine are configurations of the machines below, in the same order and up to the end of the run. The steps at which they occur differ, the tables are not renamings of each other, and equal tapes with different states may be continued differently, so this does not tie the halting questions together.

- [`1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA1RB_1RE---`](../1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA1RB_1RE---/README.md): 9,132,095 configurations, the last at step 10,000,000 here and step 9,132,094 there

<!-- end of related machines -->
