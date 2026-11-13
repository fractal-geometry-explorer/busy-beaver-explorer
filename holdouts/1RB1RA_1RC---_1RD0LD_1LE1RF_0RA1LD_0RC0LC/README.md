# 1RB1RA_1RC---_1RD0LD_1LE1RF_0RA1LD_0RC0LC

bbchallenge id 41852. Open. A **queue of growing blocks**, tag-system-like: the tape is a row of blocks `1^n` separated by `0 0 1 0 0`; at
each visit of the left end the first block is taken apart, the second becomes the first with 8 more ones, every
other block gains 6 ones, and new small blocks are made at the right end. Checked 69,068 times in 3e9 steps.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RA |
| B | 1RC | --- |
| C | 1RD | 0LD |
| D | 1LE | 1RF |
| E | 0RA | 1LD |
| F | 0RC | 0LC |

## The tape as words

At each visit of the left end: `1^n1 00100 1^n2 00100 ... 1^nk` + a tail where new blocks are built, e.g. step
2,999,129,327 (51 blocks): `297 303 287 275 281 259 261 247 255 245 ... 49 49 49 33 31 15 13 13 3`, tail
`1^3 (001)^4 1^8 (001)^4 1^5 (00111)^4`.

## The queue law

| block | at the next visit |
|---|---|
| n1 | removed |
| n2 | first, n2 + 8 |
| ni, i >= 3 | ni + 6, one place forward |
| tail | 0-2 new small blocks |

Checked at every visit of the first 3e9 steps (`py/queue.py`: 69,068 checks, no exception). A block made with a few
ones leaves the queue with about 6 x (queue length) ones: queue length 16 (8e6 steps), 25 (1.4e8), 38 (8e8),
51 (2.9e9), first block 103, 169, 227, 289. Runs like `43 43 43` travel through unchanged: the queue remembers what was
appended, as a tag system does. The tape grows by about one cell per visit.

## Sweeps (Lean, kernel, `lean/Rules.lean`)

* `a_right`: `L A>1^n R` -> `L 1^n A> R` (n steps).
* `d_zig`: `L 1 D>(11)^n R` -> `L (10)^n 1 D> R` (6n steps): the zigzag that takes a block apart.

## Halting

The only halting transition is B on a 1; B is entered only from A on a 0 (A writes 1, moves right).

## Status

Open. Kernel: halting configurations, 10,000 steps, the two sweep rules. Native: 10^7 steps. Trusted: no halt in
10^10 steps; the queue law at every visit of the first 3e9 steps.

## For later

* Work out the production rule: which new blocks a removed front block of size n produces (its parity or residue mod
  6 is the natural candidate); with it the machine becomes an explicit tag-like system on block sizes that can be run
  far beyond 10^10 steps, and its halting condition can be stated.

## First look

Growth class **sqrt/sqrt** (left: sqrt, exponent 0.394; right: sqrt,
exponent 0.377). After 1,000,000,000 steps: 4,947 cells visited (1,276 left of the
start, 2,602 right), 4,149 ones.

- left, step 969,066,653: `E>0 1^225 0^2 1 0^2 1^219 0^2 1 0^2 1^217 0^2 1 0^2 1^231 0^2 1 0^2 1^209 0^2 1 0^2 1^199 0^2 1 0^2 1^195 0^2 1 0^2 1^185 0^2 1 0^2 1^191 0^2 1 0^2 1^169 0^2 1 0^2 1^171 0^2 1 0^2 1^167 0^2 1 0^2 1^157 0^2 1 0^2 1^153 0^2 1 0^2 1^145 0^2 1 0^2 1^147 0^2 1 0^2 1^127 0^2 1 0^2 1^135 0^2 1 0^2 1^127 0^`
- left, step 985,472,974: `E>0 1^235 0^2 1 0^2 1^223 0^2 1 0^2 1^219 0^2 1 0^2 1^211 0^2 1 0^2 1^213 0^2 1 0^2 1^193 0^2 1 0^2 1^201 0^2 1 0^2 1^193 0^2 1 0^2 1^201 0^2 1 0^2 1^185 0^2 1 0^2 1^169 0^2 1 0^2 1^159 0^2 1 0^2 1^161 0^2 1 0^2 1^145 0^2 1 0^2 1^151 0^2 1 0^2 1^133 0^2 1 0^2 1^127 0^2 1 0^2 1^135 0^2 1 0^2 1^121 0^`
- right, step 974,913,172: `0 1^15 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0`
- right, step 991,445,563: `0 1^3 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 `

## Pages

- [`pages/holdouts/1RB1RA_1RC---_1RD0LD_1LE1RF_0RA1LD_0RC0LC/explainer.html`](../../pages/holdouts/1RB1RA_1RC---_1RD0LD_1LE1RF_0RA1LD_0RC0LC/explainer.html)
- [`pages/holdouts/1RB1RA_1RC---_1RD0LD_1LE1RF_0RA1LD_0RC0LC/proof-status.html`](../../pages/holdouts/1RB1RA_1RC---_1RD0LD_1LE1RF_0RA1LD_0RC0LC/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RA_1RC---_1RD0LD_1LE1RF_0RA1LD_0RC0LC/lean/check.sh
python3 holdouts/1RB1RA_1RC---_1RD0LD_1LE1RF_0RA1LD_0RC0LC/py/queue.py 1e9
```

## Accelerated run

Trusted computation: `python3 tools/py/bbtools/rleaccel.py 1RB1RA_1RC---_1RD0LD_1LE1RF_0RA1LD_0RC0LC 2 109200000` runs 109,200,000 macro steps from blank tape without a halt, more than 5.64·10^9
machine steps (tape: 9,928 cells). The simulator codes the tape in runs, crosses a run in one step and jumps cycles whose
one-cycle rule it has first proved symbolically; it is tested cell for cell against direct runs
(`tools/tests/test_rleaccel.py`).
