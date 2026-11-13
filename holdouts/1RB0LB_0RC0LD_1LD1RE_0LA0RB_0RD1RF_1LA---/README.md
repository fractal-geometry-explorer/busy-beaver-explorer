# 1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD1RF_1LA---

bbchallenge id 133258. One of the six-state holdouts whose halting from blank tape is open (group G11).

Family **G11-Y** (two counters ticking together, `1RB0LB_0RC0LD` and relatives): this machine is the mirror case of the family: the same engine, but the junk sits between the digits of the left counter and the right counter is clean, and neither side is clockwork.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LB |
| B | 0RC | 0LD |
| C | 1LD | 1RE |
| D | 0LA | 0RB |
| E | 0RD | 1RF |
| F | 1LA | --- |

## What it does

The tape is, most of the time, `L · engine · R`. Every visit of the head to the engine (an *event*) adds 1 to two binary
counters, one on each side. In the reference machine `1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RC---`, `L` is in 4-cell blocks (`0101` = 1,
`0001` = 0, lowest digit next to the engine) and `R` has one cell per digit, three cells apart (cells 9, 12, 15, … right
of the head), lowest digit nearest the engine. Between some digits of `L` there are fixed stretches (junk) that the carries cross.

- **No clockwork side.** The junk is in the left counter; the right counter is clean, and neither side's period is regular.
- **The junk.** The change counts per cell (`chg.c`: how often each cell changes between consecutive events over a
  whole period) halve from one digit to the next, with junk stretches between some digits. The junk is written when a
  carry reaches the end of the tape (at irregular event counts); how is not decoded.
- **Where it can halt.** Only in F reading 1; F is entered from E1 (1RF) only. E1 is the rare transition here: 62 uses in the first 10^9 steps, each followed by F reading a 0 (F0 = 1LA, also 62 uses). So it halts only if one of these rare moments finds a 1.

The family: `1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RC---` (reference), `1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RB_0RC---` (the same run, checked cell for cell for
10^10 steps), `1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD0LC_0RC---`, `1RB0LB_0RC0LD_1LD1RE_0LA0RF_1RB0RD_0RB---`,
`1RB0LB_0RC0LF_1LD1RE_0LA0RB_0RD0RF_0LA---` (left-end extensions after 2^k events, each twice, within a few hundred
steps of each other), `1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA0RE_1RE---` and `1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA1RB_1RE---` (same
right part at the left-end visits, 3·2^k), and the mirror case `1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD1RF_1LA---`.

## Events, third round

This machine is the reference `1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RB_0RC---` except at E1: D1 = 0RB (the reference's D1 = 0RF followed
by F0 = 0RC = B0 when a 0 follows, which it always does) and E1 = 1RF with F0 = 1LA. At the first use of E1, at step
87, it writes a 1 the reference never writes (`m_e1_split`), and from then on the run is a different one. From step
216,421 the engine is at cell 117 and from step 40,881,629 the tape at each event (A on cell 117) reads
`… junk … d2 d1 d0 01011010001 A> p 0 e0 0 0 e1 0 0 e2 …`: the left counter in digits `0001` = 0 / `0101` = 1
(three digits before the junk in 3·10^8 steps), an 11-cell block, the phase cell and a clean right counter, one cell
per digit three cells apart. The junk on the left is itself a nest of counters: a left carry over d0 d1 d2 enters it
(every 8th left event), and in 3·10^8 steps about 60 different crossings occur, each about half as often as the one
before (65,109; 32,555; 16,277; 8,139; …). `lean/Events.lean` (6 theorems): the left increment (12n+48 steps), the
right increments (4; 8k+12), the two most frequent junk crossings (concrete), and the split. Coverage: 95.4% of the
2,221,740 events of the first 3·10^8 steps. Halting needs E1 followed by a 1.

## Status

Open. Lean, kernel only: the halting configurations and 10^4 steps (`lean/Blank.lean`), the sweeps of the run (`lean/Rules.lean`), the increments of both counters, two junk crossings and the split from the reference, 6 theorems (`lean/Events.lean`). `native_decide`: 10^7 steps. C: no halt in
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

Growth class **exp/exp** (left: exp, exponent 0.044; right: exp,
exponent 0.067). After 1,000,000,000 steps: 256 cells visited (44 left of the
start, 200 right), 101 ones.

- left, step 816,433,929: `B>0 0^2 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0^2 1 0 1 0 1 0 1 0 1 0 1 0^7 1 0 1 0 1 0^5 1 0 1 0 1 0 1 0 1 0 1 0 1 0^2 1 0 1 0 1 0 1 0 1 0 1 0 1 0^2 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0^4 1 0 1 0 1 0 1 0 1 0^2 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0^4 1 0 1 0 `
- right, step 867,540,452: `1 0 1 0^3 1 0^3 1 0^3 1 0^3 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0^3 1 0 1 0 1 0 1 0 1^2 0 1 0 1 0 1 0^3 1^2 0 1^2 0 1 0 1 0 1 0 1 0 1^2 0 1^2 0 1 0 1 0 1 0^3 1 0 1 0 1^2 0 1 0^3 1 0 1 0 1 0 1 0 1^2 0 1 0^3 1 0 1 0 1 0^3 1^2 0 1 0^3 1 0 1 0 1 0 1 0 1^2 0 1 0^3 1 0^3 1 0^3 1^2 0 1 0 1 0 1 0 1 0 `
- right, step 976,627,157: `1 0 1 0^3 1 0^3 1 0 1 0 1 0^3 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0^3 1 0 1 0 1 0 1 0 1^2 0 1 0 1 0 1 0^3 1^2 0 1^2 0 1 0 1 0 1 0 1 0 1^2 0 1^2 0 1 0 1 0 1 0^3 1 0 1 0 1^2 0 1 0^3 1 0 1 0 1 0 1 0 1^2 0 1 0^3 1 0 1 0 1 0^3 1^2 0 1 0^3 1 0 1 0 1 0 1 0 1^2 0 1 0^3 1 0^3 1 0^3 1^2 0 1 0 1 0 1 0 1 `

## Pages

- [`pages/holdouts/1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD1RF_1LA---/explainer.html`](../../pages/holdouts/1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD1RF_1LA---/explainer.html)
- [`pages/holdouts/1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD1RF_1LA---/proof-status.html`](../../pages/holdouts/1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD1RF_1LA---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD1RF_1LA---/lean/check.sh
```
