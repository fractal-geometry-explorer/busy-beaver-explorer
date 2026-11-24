# 1RB0RD_1LC1RE_1LD0LC_0LE0LC_0RA0RF_1RA---

bbchallenge id 124880. One of the six-state holdouts whose halting from blank tape is open. Family: **word counter on 1100 / 10 (right end)**, with the sibling [`1RB0RC_1LC1RE_0LE0LD_1LC0LB_0RA0RF_1RA---`](../1RB0RC_1LC1RE_0LE0LD_1LC0LB_0RA0RF_1RA---/README.md) (C and D swapped, two transitions differ).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RD |
| B | 1LC | 1RE |
| C | 1LD | 0LC |
| D | 0LE | 0LC |
| E | 0RA | 0RF |
| F | 1RA | --- |

## What it does

The tape grows mostly to the right, logarithmically: each new cell costs a roughly constant factor more time.

| rightmost cell | first reached at step |
|---|---|
| 50 | 1,791 |
| 100 | 37,189 |
| 150 | 436,687 |
| 200 | 24,850,931 |
| 250 | 1,127,467,227 |
| 300 | 15,161,635,357 |

304 cells after 18,989,462,033 steps (`tools/c/tmrun.c records`). Read in the words `a = 1100`, `b = 10` (`tools/c/tokrun.c`), the
tape is a word over a, b and single 1s (e.g. `a^6 b^14 a 1 b^2 a^3 1 b^4 a^5 b^2 ...`) followed by a regular tail
`(1 b^2)^n`; the front changes at every pass, the tail grows by a unit now and then.

**Halting.** F on 1 is the only halt and F is entered only from E on 1: the machine halts exactly at `E>1 1`. Not seen.

**Open:** the overflow rule (how the counters are laid out again when the left one runs out), and whether `E>1 1` can occur at an overflow.

## The two counters

At every visit of the hub turn, E reading 0 at cell 87 at step 1.2·10^8 (the hub moves right at each overflow), the tape reads as two binary counters back to back:

- **left counter**, lowest digit next to the hub: the same words as the sibling: 4-cell digits `1001` (1) and `0101` (0), the lowest digit `10` / `01`, separators `100110101` and `10011011`;
- **right counter**, lowest digit next to the hub: 5-cell digits `10101` (1) and `10100` (0), the lowest digit one cell, separators `10010101` and `101010101`.

Each hub event takes 1 from the left counter and adds 1 to the right counter. Its cost is linear in what changes:
10 steps per left digit changed, 12 per right digit changed, 28 or 32 per separator crossed, plus a constant. `tools/py/bbtools/cjump.py` learns these words and costs from the run (exact
rational fit, accepted only if it predicts every observed event, whole tape and step count) and then jumps whole
stretches of counting at once; it matched direct runs exactly at every check.

**Proved in Lean** (`lean/Counter.lean`, kernel, for every `k`, `j` and every tape beyond the cells shown, written by
`py/rules.py` from 4,000 sampled events):

- `borrow` (10k + 20 steps): `L 1001 (0101)^k 01 E> 0 0 0 R` -> `L 0101 (1001)^k 10 E> 0 0 1 R`, the left counter borrowing through `k` digits;
- `carry0` (12j + 54 steps): `L 1 0 E> 0 0 1 1 0 1 0 1 0 (10110)^j 1 0 1 1 0 1 0 0 R` -> `L 0 1 E> 0 0 0 1 0 1 0 1 0 1 0 1 (10100)^j 1 0 1 0 1 R`, the right counter carrying through `j` digits;
- `carry1` (12j + 66 steps): the same with one more digit beyond the carry, the right counter carrying through `j` digits;
- `plain` (54 steps): `L 1 0 E> 0 0 1 1 0 1 0 1 0 1 0 1 1 0 1 0 0 R` -> `L 0 1 E> 0 0 0 1 0 1 0 1 0 1 0 1 1 0 1 0 1 R`, the most frequent short event.

**Overflows.** When the left counter runs out the hub moves and the counters are laid out again; the accelerator
then simulates directly until it can learn the new layout. Seen so far: the hub turn moved to cells 87, 111, 113, 132, 146, 156, 158, 176 and 186 at steps 1.1·10^8, 2.5·10^9, 2.7·10^10, 2.2·10^11, 2.0·10^12, 9.5·10^12, 1.7·10^14, 7.0·10^14 and 3.4·10^15.

**Accelerated halt hunt.** A 30-minute run of `cjump.py` reached step 3,446,148,086,008,046 (3.45·10^15) with 455 cells visited and no halt. 

## Status

Open.

- Lean (`lean/Blank.lean`): `step_none_iff`, no halt in 10,000 steps by the kernel, in 10,000,000 by `native_decide`.
- Lean, kernel (`lean/Sweeps.lean`): the sweep rules of the self-loops.
- Lean, kernel (`lean/Counter.lean`): the borrow and carry rules of the two counters.
- C: no halt in 2·10^10 steps.
- Accelerated (`tools/py/bbtools/cjump.py`, trusted computation): no halt in 3.45·10^15 steps.

## Next steps

Decode the overflow from the layouts before and after each hub move, as for the sibling 1RB0RC_1LC1RE_0LE0LD_1LC0LB_0RA0RF_1RA---, which has the same counter words; one overflow rule may serve both.

## Pages

- [`pages/holdouts/1RB0RD_1LC1RE_1LD0LC_0LE0LC_0RA0RF_1RA---/explainer.html`](../../pages/holdouts/1RB0RD_1LC1RE_1LD0LC_0LE0LC_0RA0RF_1RA---/explainer.html)
- [`pages/holdouts/1RB0RD_1LC1RE_1LD0LC_0LE0LC_0RA0RF_1RA---/proof-status.html`](../../pages/holdouts/1RB0RD_1LC1RE_1LD0LC_0LE0LC_0RA0RF_1RA---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RD_1LC1RE_1LD0LC_0LE0LC_0RA0RF_1RA---/lean/check.sh
./tmrun 1RB0RD_1LC1RE_1LD0LC_0LE0LC_0RA0RF_1RA--- 20000000000 records 1500
python3 tools/py/bbtools/cjump.py 1RB0RD_1LC1RE_1LD0LC_0LE0LC_0RA0RF_1RA--- 1e3000 1800      # accelerated, 30 minutes
python3 holdouts/1RB0RD_1LC1RE_1LD0LC_0LE0LC_0RA0RF_1RA---/py/rules.py                        # writes lean/Counter.lean
```
