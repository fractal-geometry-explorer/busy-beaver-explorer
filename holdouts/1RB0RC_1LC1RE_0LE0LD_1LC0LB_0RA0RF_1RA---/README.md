# 1RB0RC_1LC1RE_0LE0LD_1LC0LB_0RA0RF_1RA---

bbchallenge id 4176. One of the six-state holdouts whose halting from blank tape is open. Family: **word counter on 1100 / 10 (right end)**, with the sibling [`1RB0RD_1LC1RE_1LD0LC_0LE0LC_0RA0RF_1RA---`](../1RB0RD_1LC1RE_1LD0LC_0LE0LC_0RA0RF_1RA---/README.md) (C and D swapped, two transitions differ).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RC |
| B | 1LC | 1RE |
| C | 0LE | 0LD |
| D | 1LC | 0LB |
| E | 0RA | 0RF |
| F | 1RA | --- |

## What it does

The tape grows mostly to the right, logarithmically: each new cell costs a roughly constant factor more time.

| rightmost cell | first reached at step |
|---|---|
| 50 | 1,089 |
| 100 | 15,405 |
| 150 | 131,443 |
| 200 | 2,803,197 |
| 300 | 1,182,697,357 |
| 350 | 16,667,114,039 |

359 cells after 18,417,187,404 steps (`tools/c/tmrun.c records`). Read in the words `a = 1100`, `b = 10` (`tools/c/tokrun.c`), the
tape is a word over a, b and single 1s (e.g. `a^6 b^14 a 1 b^2 a^3 1 b^4 a^5 b^2 ...`) followed by a regular tail
`(1 b^2)^n`; the front changes at every pass, the tail grows by a unit now and then.

**Halting.** F on 1 is the only halt and F is entered only from E on 1: the machine halts exactly at `E>1 1`. Not seen.

**Open:** the overflow rule (how the counters are laid out again when the left one runs out), and whether `E>1 1` can occur at an overflow.

## The two counters

At every visit of the hub turn, E reading 0 at cell 143 at step 1.3·10^9 (the hub moves right by about ten cells per overflow), the tape reads as two binary counters back to back:

- **left counter**, lowest digit next to the hub: 4-cell digits `1001` (1) and `0101` (0), the lowest digit `10` (1) / `01` (0), in stretches separated by the 9-cell word `100110101` that borrows cross unchanged;
- **right counter**, lowest digit next to the hub: 5-cell digits `10101` (1) and `10100` (0), the lowest digit one cell (`1` is 1), with separator words such as `10010100`.

Each hub event takes 1 from the left counter and adds 1 to the right counter. Its cost is linear in what changes:
10 steps per left digit changed, 12 per right digit changed, 32 per left separator crossed, plus a constant. `tools/py/bbtools/cjump.py` learns these words and costs from the run (exact
rational fit, accepted only if it predicts every observed event, whole tape and step count) and then jumps whole
stretches of counting at once; it matched direct runs exactly at every check.

**Proved in Lean** (`lean/Counter.lean`, kernel, for every `k`, `j` and every tape beyond the cells shown, written by
`py/rules.py` from 4,000 sampled events):

- `borrow` (10k + 20 steps): `L 1001 (0101)^k 01 E> 0 0 0 R` -> `L 0101 (1001)^k 10 E> 0 0 1 R`, the left counter borrowing through `k` digits;
- `carry0` (12j + 22 steps): `L 1 0 E> 0 0 (11010)^j 1 1 0 1 0 0 R` -> `L 0 1 E> 0 (00101)^j 0 0 1 0 1 0 1 R`, the right counter carrying through `j` digits;
- `carry1` (12j + 106 steps): the same beyond a 30-cell stretch that holds a separator, the right counter carrying through `j` digits;
- `plain` (22 steps): `L 1 0 E> 0 0 1 1 0 1 0 0 R` -> `L 0 1 E> 0 0 0 1 0 1 0 1 R`, the most frequent short event.

**Overflows.** When the left counter runs out the hub moves and the counters are laid out again; the accelerator
then simulates directly until it can learn the new layout. The hub turn moves to a new cell at each overflow (table below).

At each overflow the left counter has just counted down to 0 and the right counter holds one more digit than the left counter had (`cjump.py`, the counters as read at the last hub event before the head leaves on the overflow excursion, which lasts up to 10^8 steps; afterwards the left counter has n digits and a value close to 2^n):

| overflow at step | left counter (digits) | right counter (digits) | right counter (value) |
|---|---|---|---|
| 2.1011·10^8 | 18 | 19 | 228,440 |
| 1.2920·10^9 | 23 | 24 | 8,316,170 |
| 4.5633·10^9 | 26 | 27 | 64,999,639 |
| 1.6005·10^10 | 25 | 26 | 29,229,807 |
| 1.2801·10^11 | 31 | 32 | 2,128,592,315 |
| 6.0541·10^11 | 31 | 32 | 1,876,710,861 |
| 9.9268·10^12 | 38 | 39 | 272,461,191,975 |
| 3.9152·10^13 | 37 | 38 | 120,108,424,947 |
| 1.5808·10^14 | 39 | 40 | 530,410,399,330 |
| 1.4603·10^15 | 41 | 42 | 2,181,240,383,542 |
| 4.9618·10^15 | 46 | 47 | 68,151,962,712,175 |

**Accelerated halt hunt.** A 30-minute run of `cjump.py` reached step 4,961,958,653,181,237 (4.96·10^15) with 549 cells visited and no halt, through 11 overflows. After the overflow at step 4.96·10^15 it found no model in the remaining time.

## Status

Open.

- Lean (`lean/Blank.lean`): `step_none_iff`, no halt in 10,000 steps by the kernel, in 10,000,000 by `native_decide`.
- Lean, kernel (`lean/Counter.lean`): the borrow and carry rules of the two counters.
- C: no halt in 2·10^10 steps.
- Accelerated (`tools/py/bbtools/cjump.py`, trusted computation): no halt in 4.96·10^15 steps.

## Next steps

Decode the overflow from the layouts before and after each hub move (the times and cells are in the section above), write it as a rule on the two counter values, and prove it with `symtm` as for the counting rules; then the run becomes a map on (left, right) values that can be iterated far beyond 10^13.

## Pages

- [`pages/holdouts/1RB0RC_1LC1RE_0LE0LD_1LC0LB_0RA0RF_1RA---/explainer.html`](../../pages/holdouts/1RB0RC_1LC1RE_0LE0LD_1LC0LB_0RA0RF_1RA---/explainer.html)
- [`pages/holdouts/1RB0RC_1LC1RE_0LE0LD_1LC0LB_0RA0RF_1RA---/proof-status.html`](../../pages/holdouts/1RB0RC_1LC1RE_0LE0LD_1LC0LB_0RA0RF_1RA---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RC_1LC1RE_0LE0LD_1LC0LB_0RA0RF_1RA---/lean/check.sh
./tmrun 1RB0RC_1LC1RE_0LE0LD_1LC0LB_0RA0RF_1RA--- 20000000000 records 1500
python3 tools/py/bbtools/cjump.py 1RB0RC_1LC1RE_0LE0LD_1LC0LB_0RA0RF_1RA--- 1e3000 1800      # accelerated, 30 minutes
python3 holdouts/1RB0RC_1LC1RE_0LE0LD_1LC0LB_0RA0RF_1RA---/py/rules.py                        # writes lean/Counter.lean
```
