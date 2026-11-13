# 1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RB_0RC---

bbchallenge id 23933. One of the six-state holdouts whose halting from blank tape is open (group G11).

Family **G11-Y** (two counters ticking together, `1RB0LB_0RC0LD` and relatives): this machine is the reference machine with E1 = 1RB instead of 1RF: after E1 the head reads a 0 every time, and F0 = B0 = 0RC, so the run is the reference machine's run cell for cell (same head and tape at every step for 10^10 steps).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LB |
| B | 0RC | 0LD |
| C | 1LD | 1RE |
| D | 0LA | 0RF |
| E | 0RD | 1RB |
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
- **Where it can halt.** Only in F reading 1; F is entered from D1 (0RF) only. After D1, used about 4·10^7 times in 10^9 steps, the head has read a 0 every time. The rare transition E1 (306 uses) leads to B here, not F; in the reference machine E1 fires when a carry of the right counter reaches a digit for the first time since the last left-end visit: right after the visit at step 2,188,604 it fires at steps 2,188,675, 2,188,767, 2,188,882, 2,189,117, 2,189,592, 2,190,547, 2,192,462, three cells further right each time and after twice the wait each time, as a binary counter reaching new digits. So this machine halts only if an ordinary carry finds a 1 after D1, while the reference machine would also halt at a fresh digit followed by a 1, where this one goes on.

The family: `1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RC---` (reference), `1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RB_0RC---` (the same run, checked cell for cell for
10^10 steps), `1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD0LC_0RC---`, `1RB0LB_0RC0LD_1LD1RE_0LA0RF_1RB0RD_0RB---`,
`1RB0LB_0RC0LF_1LD1RE_0LA0RB_0RD0RF_0LA---` (left-end extensions after 2^k events, each twice, within a few hundred
steps of each other), `1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA0RE_1RE---` and `1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA1RB_1RE---` (same
right part at the left-end visits, 3·2^k), and the mirror case `1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD1RF_1LA---`.

**Decoded in the second round (this machine; event = A on cell 3).** At an event the tape is
`... L 0001 | p 0 1010000 R ...`: the left counter `L` (4-cell digits `0001` = 0, `0101` = 1, lowest next to the
fixed block `0001`), the phase cell `p` (1: this event adds 1 to `L`; 0: it adds 1 to `R`), and the right counter `R`,
one cell per digit, lowest first. Consecutive digits of `R` are separated by `00`, or by `00` followed by one or more
**junk units** `1010000` (7 cells; the engine block `0 1010000` is one too).

- The increments are theorems for every size (`lean/Events.lean`, 9 theorems, kernel, `py/events.py`): the left
  increment with a carry over n ones (12n+24 steps), the right increment on a lowest 0 (28 steps) and with a carry
  over k+1 ones (8k+36 steps), and carries crossing junk units, which they leave unchanged (one unit; j units in a
  row, 24j+36 steps; j units then k+1 more ones, 24j+8k+44 steps). The same file proves for all the siblings (below).
- **Coverage** (`python3 py/events.py --coverage 100000000`): of the 1,048,574 events of the first 10^8 steps, 95.2% are
  instances of these theorems. The other 50,167 come at fixed offsets inside each period (in the period from event
  131,070: offsets 0, 1, 2 and then every 32nd event; from 262,142: every 32nd; from 524,286: every 128th): carries
  that reach one particular digit whose neighbourhood is not of the form `00 (1010000)^j` (for instance a block
  `1010101` in the period from event 131,070). So the regrouping at a left-end visit can leave junk words other than
  `1010000`, which then stay for the whole period. Decoding them is the next step.
- **Left side: clockwork.** The left end is visited right after events 2^k - 2 (2, 6, 14, ..., 16,777,214), and `L`
  restarts.
- **The junk stays put inside a period and moves only at left-end visits.** Within each period between left-end
  visits the cells that change between events are exactly the digit cells of `R`; their gaps (3 = adjacent, 10 = one
  junk unit, 17 = two, ...) give the junk layout of the period (`c/yper.c`). Junk units between the digits
  d0 d1 d2 ... in successive periods (`.` none, `J` one, a number = gap in cells):

| events | junk layout after d0, d1, ... |
|---|---|
| 1,022-2,046 | `. . . JJJ . .` |
| 2,046-4,094 | `J . J J . . JJ .` |
| 4,094-8,190 | `J . . . JJ J . . .` |
| 8,190-16,382 | `. . . . . 31 . J . .` |
| 16,382-32,766 | `. . . . . 38 . . . J .` |
| 32,766-65,534 | `J . . . JJJ J . J . . J .` |
| 65,534-131,070 | `J . J J J J . . . JJ . J .` |
| 131,070-262,142 | `. . . JJJ J J . . . JJ . J J .` |
| 262,142-524,286 | `. . . JJ JJ . J J . . . J . JJ` |
| 524,286-1,048,574 | `J . J . . JJ JJ . . . . J JJ . . .` |
| 1,048,574-2,097,150 | `J . . . . . 38 . J . . J J . J . .` |
| 2,097,150-4,194,302 | `. . . . . . . 52 . . . . J . . JJ J .` |
| 4,194,302-8,388,606 | `. . . . . . . 52 J . . . J . J . . .` |
| 8,388,606-16,777,214 | `J . . . . . 31 JJ . J . J . J . . . . JJ .` |
| 16,777,214-33,554,430 | `J . J . . JJJ . . JJ . JJ . . J . J . . . . .` |

  (31, 38, 52: 4, 5, 7 junk units in one stretch.) The total grows by about one unit per period, and the units near
  the engine are regrouped at each visit; the rule of the regrouping is not decoded. The halting transition is
  reached only through D1 (0RF) followed by a 1; the proved increments, including the junk crossings, end with the
  head back at the engine and never take D1 into a 1, so a halt needs a moment these rules do not cover: a left-end visit (the regrouping), a right-end extension, or a carry
  meeting a junk stretch in a way not listed.

## Siblings, third round

The reference's event theorems were ported to every member of the family (`py/events.py` in each folder imports
`RULES` and the coverage tool from here); what differs:

| machine | differs from this one | events |
|---|---|---|
| `..._0RD1RF_0RC---` | E1 = 1RF; then F reads 0 and F0 = 0RC = B0 | the same 9 theorems; the same run cell for cell |
| `..._0RD0LC_0RC---` | E1 = 0LC: `L 1 E> 1 0 R` → `L 1 1 B> 0 R` in 5 steps instead of 1 | the same 9 theorems; the same tape at every event, 4 steps later per E1 use (996 = 4·249 at 2.95·10^8 steps) |
| `1RB0LB_0RC0LF_..._0RD0RF_0LA---` | B1 = 0LF with F0 = 0LA = D0; D1 = 0RB; E1 = 0RF: 3 steps instead of 1 | the same 9 theorems; the same tape at every event, 2 steps later per E1 use (498 = 2·249) |
| `..._0LA0RF_1RB0RD_0RB---` | E0 = 1RB, E1 = 0RD, F0 = 0RB | A on cell 3 only in phase 1, at this machine's events 2, 4, 6, … (2,097,151 events checked): a left and a right increment in one pass, 8 theorems (14n steps for the left carry) |
| `..._0LA0RB_0RD1RF_1LA---` | D1 = 0RB, E1 = 1RF, F0 = 1LA | splits off at the first use of E1 (step 87); a different run: clean right counter, junk on the left, engine at cell 117 |
| `1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA0RE_1RE---` | other words: left digits `0110`/`0111`, block `011001`, right block `001010000` | 6 theorems of the same shapes (left 22n+34 steps) |
| `1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA1RB_1RE---` | its twin with E1 = 1RB | A on cell 3 only in phase 1: left and right increment in one pass, 5 theorems |

In the first three rows the tape at every event is this machine's, checked for the first 2,000,000 events
(`c/evdump.c`); they differ only in how the halting transition is reached (this machine: D1 followed by a 1; `0RD1RF`: also E1 followed
by a 1; `0RD0LC`: D1 followed by a 1; the `0LF` sibling: B1 or E1 followed by a 1).

## Status

Open. Lean, kernel only: the halting configurations and 10^4 steps (`lean/Blank.lean`), the sweeps of the run and the right counter's carry for every number of ones (`r_up`, `r_down`, `event0`) (`lean/Rules.lean`), the increments of both counters at the engine and the junk crossings, 9 theorems (`lean/Events.lean`). `native_decide`: 10^7 steps. C: no halt in
10^11 steps.

## Next steps

Decode the regrouping of junk units at a left-end visit (table above): then the junk layout is a function of the period number. 
Decode what a carry writes when it reaches the end of the tape, so that the junk after each visit is a formula in the
counters; then decide whether a carry can ever find a 1 where it has always found a 0.

## Scripts

- `py/events.py` writes `lean/Events.lean` (`--coverage STEPS [SHOW]`: match every event against the rules, with `c/evdump.c`); `c/yper.c M STEPS 3`: the digit cells of `R` in each period (the table).

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

- [`pages/holdouts/1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RB_0RC---/explainer.html`](../../pages/holdouts/1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RB_0RC---/explainer.html)
- [`pages/holdouts/1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RB_0RC---/proof-status.html`](../../pages/holdouts/1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RB_0RC---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RB_0RC---/lean/check.sh
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same run as [`1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RC---`](../1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RC---/README.md) (observed, not proved).** At every one of the first 10^7 steps from blank tape the two machines have the same tape and the head on the same cell. Their tables differ, and no renaming of the states turns one into the other. While they run, the states pair up as A–A, B–B, B–F, C–C, D–D, E–E, F–F (this machine first), which is not one to one. Transitions not used in these steps: this machine never uses F1 and the other never uses F1. Lean proves (`lean/Twin.lean` here, `lock_or_break`, `not_halts_of_noBreak`) that the two runs have the same tape, the same head position and paired states up to the first break, a configuration where the paired states act differently, and that neither machine halts if no break ever comes. A halt of either machine is itself a break, and the halting transitions of the two do not correspond, so the two are not known to halt together.

**Same tapes at another pace (observed, not proved).** Leave the states aside and compare only the tape and the place of the head. Then a large part of the first 10^7 configurations of this machine are configurations of the machines below, in the same order and up to the end of the run. The steps at which they occur differ, the tables are not renamings of each other, and equal tapes with different states may be continued differently, so this does not tie the halting questions together.

- [`1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD0LC_0RC---`](../1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD0LC_0RC---/README.md): 9,999,409 configurations, the last at step 9,999,408 here and step 10,000,000 there
- [`1RB0LB_0RC0LD_1LD1RE_0LA0RF_1RB0RD_0RB---`](../1RB0LB_0RC0LD_1LD1RE_0LA0RF_1RB0RD_0RB---/README.md): 8,749,634 configurations, the last at step 9,999,093 here and step 9,999,999 there
- [`1RB0LB_0RC0LF_1LD1RE_0LA0RB_0RD0RF_0LA---`](../1RB0LB_0RC0LF_1LD1RE_0LA0RB_0RD0RF_0LA---/README.md): 9,999,705 configurations, the last at step 9,999,704 here and step 10,000,000 there
- [`1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD---`](../1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD---/README.md): 7,916,520 configurations, the last at step 10,000,000 here and step 9,166,232 there

<!-- end of related machines -->
