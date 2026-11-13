# 1RB0RD_1LC0LE_0RA0LB_1RC1RF_1LB1RD_0RC---

bbchallenge id 21160. A row of frozen blocks of 001 on the left and one live block on the right that a sub-bouncer keeps refilling: at each full return the live block (001)^a (011)^b becomes (001)^(a+b+7) (011)^b', and now and then it splits off a new frozen block.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RD |
| B | 1LC | 0LE |
| C | 0RA | 0LB |
| D | 1RC | 1RF |
| E | 1LB | 1RD |
| F | 0RC | --- |

## What it does

The tape is a row of blocks of `001` separated by short walls, with a bouncer in the last block. Sampled each
time the head comes back to the left end (state C, 135 times in 10⁹ steps), the tape reads

    step 856,843,289:  C>0 1 0 1 (100)^59 0^3 1 (100)^107 0 1^3 (001)^1452 0 (1001)^2 (001)^392 0^3 101 (100)^165
                       10 (1001)^2 (001)^337 0 (1001)^2 (001)^837 0 (1001)^2 (001)^3680 0^3 1^3 (001)^3 (011)^1055 01

Every block except the last is **frozen**: 59, 107, 1452, 392, 165, 337, 837 never change once a newer block
exists. The last block is **live**. Between two left returns the head works only inside it, with a second,
smaller bouncer:

- **P1** (proved, `bounce_tail`): seen at the right end in A, the live block is `(100)^a (010)^b (110)^c`; each
  bounce moves three copies from the middle part to the left part and adds one `110`: (a, b, c) → (a+3, b−3, c+1).
  For example (step 4,422,876 → 4,479,114, six bounces apart): `(001)^61 0^3 (100)^263 (101)^5` →
  `(001)^79 0^3 (100)^245 (101)^11`. The whole phase is proved too: with `Live(x, y, z)` =
  `L 1 1 (001)^x 0 (001)^y (011)^z 0 A> 0^∞`, (x, y+1+3n, z+2) → (x+3n, y+1, z+2+n) (`p1`) and
  (x, y+6+3n, 0) → (x+4+3n, y+2, n+2) (`p1_from0`), so P1 always ends with y = 2, 3 or 4.
- **P2** (measured): when the middle part is used up, a slower phase turns (a, 0, c) into (a', b', 0) with
  a' + b' = a + c + 1 and a' = c − d, d a constant set by the block to the left (d = 39 for four phases in a
  row: (326,93) → (54,366), (543,154) → (115,583), (698,195) → (156,738), (1141,312) → (273,1181)).
  In `Live` coordinates, from (x, 2, z) the next empty-right configuration (x', y', 0) has x' + y' = x + z + 3
  (all 9 cases in 10⁹ steps); x' = z + 1 while no frozen block is to the left, then z + 1 − 41 (3 cases) and
  z + 1 − 333 (2 cases). P2 reaches the left end of the tape, which is why the frozen blocks matter.

At the left returns the live block reads `(001)^a (011)^b 01`, and the measured rule is **a' = a + b + 7**:
(229,6) → (242,82) → (331,87) → (425,116) → (548,148) → (703,189) → (899,240) → (1146,306), with b'/a' near 0.27.
So the live block grows geometrically (about ×1.27 per return); from time to time it **splits**: a wall appears
inside it, the left part freezes and a new live block starts small. The slow left side is the row of frozen blocks
(64 cells left of the start after 10⁹ steps); the right side grows with the live block.

In plain words: a bouncer inside a bouncer. The outer one sweeps the whole row rarely, the inner one refills the
last block, and each refill is a bit bigger than the one before.

## What is proved

- Lean, kernel only (`lean/Blank.lean`, generated): the halting configurations (`step_none_iff`) and no halt in the first 10,000 steps; with `native_decide`, none in the first 10<sup>7</sup>.
- Lean, kernel only (`lean/Rules.lean`, written by `py/rules.py`): the leftward crossing of a block of `001` by C (`shift_l_C_001`), and one bounce of the inner bouncer of the live block: `L 1 1 (001)^m 0 (001)^(j+4) 0 (110)^(k+1) 1 1 0 A> 0^∞` reaches the same shape with m+3, j−3, k+1 (`bounce_tail`) (`shift_l_C_001`, `bounce_tail`), and the first two bounces from an empty right part (`bounce_z0`, `bounce_z1`).
- Lean, kernel only (`lean/P1.lean`): the whole phase P1 by induction, `p1` and `p1_from0` (see above).
- C (`tools/c/triage.c`, trusted): no halt in the first 10<sup>9</sup> steps.

Everything else above is measured on runs (heuristic), not proved.

## Open

Whether it halts. The measured rules (the live block's growth `a' = a + b + 7`, the P2 phase change, the
splitting) are not proved; the splitting depends on the sizes modulo 3 in a way not yet written down, so the
question may well be Collatz-like. Halting needs D reading 1 with a 1 to its right.

## For later

This machine needs more than a day. Next steps: (1) write the macro configuration at A-at-right events as
the list of frozen blocks plus (a, b, c) of the live block; (2) find P2 and the split as explicit maps (collect
every phase start and end with `tools/c/tmrun.c MACHINE N at A R`; the shapes listed in the README of the run);
(3) prove each phase with `symtm.prove` (P1 is done: `p1`, `p1_from0`; P2 has to be stated with the frozen block to
its left, since it runs to the left end) and chain them into a macro step;
(4) look for an invariant of the block sizes (modulo 3) that excludes the halting shape.

## Reproduce

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RD_1LC0LE_0RA0LB_1RC1RF_1LB1RD_0RC---/lean/check.sh
python3 holdouts/1RB0RD_1LC0LE_0RA0LB_1RC1RF_1LB1RD_0RC---/py/rules.py          # rewrites lean/Rules.lean
python3 holdouts/1RB0RD_1LC0LE_0RA0LB_1RC1RF_1LB1RD_0RC---/py/observe.py 1e7 B 6  # the tape at the last moments each end grew
```

## Family screen (F09, 13 November 2026)

The 22 machines of family F09 were screened in one way, to decide which family each belongs to. `holdouts/1RB0LC_0RC0RF_1RD0LE_1LA1RA_1LC1RB_0RB---/screen/screen.py`
runs the machine from blank tape for 2·10^10 steps and, at the first new leftmost and rightmost cell after each
threshold 10^6·4^k, compresses the tape twice: repeats of a word of at most 40 cells (level 1), then repeats of
groups of such tokens (level 2). A bounded description keeps the number of level-2 tokens bounded while the tape
grows. The long runs use the macro simulator `holdouts/1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA/c/msim.c`, sampled at one record per leading digit of the step count.
Everything in this section is observed in one run; none of it is proved.

| record | step | visited cells | cells in no repeat | repeats | level-2 tokens | largest repeat / tape |
|---|---|---|---|---|---|---|
| left | 267,471,845 | 9,496 | 31 | 11 | 30 | 0.46 |
| right | 272,180,549 | 9,497 | 17 | 12 | 29 | 0.45 |
| right | 1,079,042,429 | 25,667 | 20 | 13 | 33 | 0.44 |
| left | 1,188,757,164 | 27,361 | 31 | 11 | 30 | 0.57 |
| right | 4,637,250,694 | 56,873 | 20 | 13 | 33 | 0.51 |
| left | 4,819,237,177 | 61,075 | 34 | 13 | 35 | 0.60 |
| right | 19,255,482,922 | 111,671 | 23 | 14 | 37 | 0.33 |
| left | 19,693,788,191 | 118,465 | 34 | 13 | 35 | 0.55 |

**Proposed family: F01, periodic blocks driven by a bounded engine** (frozen blocks of 001 and one live block rebuilt by an inner bouncer).

The description grows slowly if at all: 29 to 37 level-2 tokens at every record from 2.7·10^8 to 2·10^10 steps, and 10 to 32 runs in the macro simulator (blocks of 3 cells) at the sampled records from 10^6 to 9·10^12 steps. At step 19,693,788,191 the tape has frozen blocks of 60, 107, 1,452, 394, 165, 338, 838 and 12,270 copies of `100` or `001` and a live part `(001)^21588 (011)^2262`.

Within a level this is the F01 shape (a live block with a short engine, phase P1 already proved in Lean), and a level ends with the block frozen, as in 1RB0LC_0RC0RF_1RD0LE_1LA1RA_1LC1RB_0RB---. The list of frozen blocks is not bounded: 5 blocks at 7.6·10^7 steps, 8 at 2·10^10.

Next step: Prove the whole return `a' = a + b + 7` (measured), then the F01 closure on (a, b) with the frozen list treated as arbitrary.

## Pages

- [`pages/holdouts/1RB0RD_1LC0LE_0RA0LB_1RC1RF_1LB1RD_0RC---/explainer.html`](../../pages/holdouts/1RB0RD_1LC0LE_0RA0LB_1RC1RF_1LB1RD_0RC---/explainer.html)
- [`pages/holdouts/1RB0RD_1LC0LE_0RA0LB_1RC1RF_1LB1RD_0RC---/proof-status.html`](../../pages/holdouts/1RB0RD_1LC0LE_0RA0LB_1RC1RF_1LB1RD_0RC---/proof-status.html)
