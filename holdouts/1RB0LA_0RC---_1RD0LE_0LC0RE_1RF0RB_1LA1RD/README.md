# 1RB0LA_0RC---_1RD0LE_0LC0RE_1RF0RB_1LA1RD

bbchallenge id 3919. One of the six-state holdouts whose halting from blank tape is open (group G11).

Family **G11-H** (base 3/2, `1RB0LA_0RC---`), a single machine in this batch.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LA |
| B | 0RC | --- |
| C | 1RD | 0LE |
| D | 0LC | 0RE |
| E | 1RF | 0RB |
| F | 1LA | 1RD |

## What it does

- **Right side: a counter in base 3/2.** At right-end visits the right part is a word in `10`, `110`, `1110` with a
  fixed tail. Between consecutive right-end extensions the busiest cell turns about 1.5 times as often as the time
  before: 285,018, 427,933, 641,487, 962,206, 1,443,670 from step 139,644,038, then again 641,553, 962,401, 1,443,533,
  2,165,391, … after a restart (`ymax.c`). Factor 3/2 per new cell: the numeration of Collatz-like machines.
- **Left side: slow and irregular.** 202,215, 1,789,546, 4,800,410, 8,534,372 turns between left-end extensions at
  steps 21,310,616, 126,868,352, 364,736,478, 899,271,976.
- **Where it can halt.** Only B reading 1; B is entered from A0 (1RB) and E1 (0RB), 9·10^7 and 2·10^7 uses in 10^9
  steps, always followed by a 0. No rare transition.

**Second round: the factor is exactly 3/2 per 3 cells.** Turns of the head per cell between steps 3·10^8 and
3.1·10^8 (`../1RB0LD_0LC0RE_1LA0RD_0RB0LD_1RC1RF_1RA---/c/ahist.c M 300000000 310000000`): the busiest cell is cell 108 (counted from
the start cell; 201,806 turns), and from it rightwards every third cell has 201,806, 134,539, 89,692, 59,794, 39,862,
26,574, 17,718, 11,813, 7,876, 5,248, 3,498, ... turns, ratios 1.4999-1.5000: each 3 cells further right are visited
exactly 2/3 as often, as in a counter in base 3/2 (each digit passes on 2 carries for every 3 it receives). Far to
the left the turns halve every 4 cells (5, 10, 20, 40, 81, 164, 324 at cells -3, 1, 5, ..., 21): a binary counter.
Read as words `1^d 0` the right part right of the engine has digits d = 0, 1, 2 (e.g. at step 300,000,102:
`0 0 0 | 0 1 2 0 1 1 0 1 0 2 2 2 0 1 1 0 1 1 0 1 2 0 1 0 1 1 0 2 1 ...`), and an event at the engine rewrites a
variable-length prefix of it (`012` -> `22`, `2201` -> `10102`, ...), so the digits are not at fixed cells: the
increment rule of this base-3/2 numeration is not decoded yet.

## Status

Open. Lean, kernel only: the halting configurations and 10^4 steps (`lean/Blank.lean`), the sweeps of the run
(`lean/Rules.lean`). `native_decide`: 10^7 steps. C: no halt in 10^11 steps.

## Next steps

Read consecutive events at cell 108 (state E) as words `1^d 0` and find the rewriting of the prefix (it should be
the carry of a base-3/2 counter: three units in, two out). 
Find the digit values of `10`/`110`/`1110` and the carry rule of the right counter, and what a left-end visit does to
it; then state the Collatz-like map, if that is what it is.

## Scripts

`py/rules.py` writes `lean/Rules.lean`. C tools of the batch: `../1RB---_0LC0RB_1RA1LD_0RD1LE_1LF0LA_1LB0LE/c/`.


## First look

Growth class **exp/exp** (left: exp, exponent 0.051; right: exp,
exponent 0.062). After 1,000,000,000 steps: 271 cells visited (33 left of the
start, 223 right), 118 ones.

- left, step 899,271,976: `A>0 0^3 1 0 1 0 1 0 1 0 1 0^2 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0^2 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0^2 1 0 1 0 1 0 1 0 1 0 1 0 1 0^2 1 0 1 0 1 0 1 0^2 1 0 1 0 1 0^2 1 0 1 0 1^2 0 1^2 0 1 0 1 0 1^2 0 1 0 1 0 1 0 1 0^2 1 0 1 0^2 1 0 1 0 1^2 0 `
- right, step 901,878,298: `1 0 1 0^3 1 0^3 1^2 0 1 0^3 1 0^3 1 0^3 1 0^3 1 0^3 1 0^3 1 0^3 1 0 1 0 1 0^3 1 0 1 0 1 0 1 0 1 0 1^2 0 1 0 1 0^3 1 0 1 0 1 0^3 1 0 1^2 0 1 0 1 0^3 1 0 1 0 1 0 1^2 0^3 1 0 1 0 1 0 1^2 0 1 0 1^2 0 1 0 1 0 1 0 1^2 0 1^2 0 1 0 1^2 0 1 0^3 1 0 1^2 0 1 0 1 0 1^2 0 1 0 1 0 1^2 0 1 0 1 0 1^2 0^3 1^2 0 1 0 `
- right, step 990,380,713: `1 0 1 0^3 1 0^3 1^2 0 1 0^3 1 0^3 1 0 1 0 1 0 1 0 1 0^3 1 0^3 1 0 1 0 1 0^3 1 0^3 1 0^3 1 0 1 0 1 0 1^2 0^3 1 0 1 0 1 0 1 0 1 0^3 1^2 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1^2 0 1 0 1 0 1 0 1^2 0 1 0 1 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1 0 1^2 0^3 1^2 0 1 0^3 1^2 0 1 0^3 1 0 1^2 0^3 1 0 1^2 0 1 0 1 0 1^2 `

## Pages

- [`pages/holdouts/1RB0LA_0RC---_1RD0LE_0LC0RE_1RF0RB_1LA1RD/explainer.html`](../../pages/holdouts/1RB0LA_0RC---_1RD0LE_0LC0RE_1RF0RB_1LA1RD/explainer.html)
- [`pages/holdouts/1RB0LA_0RC---_1RD0LE_0LC0RE_1RF0RB_1LA1RD/proof-status.html`](../../pages/holdouts/1RB0LA_0RC---_1RD0LE_0LC0RE_1RF0RB_1LA1RD/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LA_0RC---_1RD0LE_0LC0RE_1RF0RB_1LA1RD/lean/check.sh
```
