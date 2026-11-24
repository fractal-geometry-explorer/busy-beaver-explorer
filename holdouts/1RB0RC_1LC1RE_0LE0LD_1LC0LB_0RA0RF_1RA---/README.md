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
then simulates directly until it can learn the new layout. Seen so far: the hub turn moved to cells 122, 128, 143, 153, 168, 182, 192 and 202 at steps 3.5·10^7, 2.1·10^8, 1.3·10^9, 4.6·10^9, 1.6·10^10, 1.3·10^11, 6.1·10^11 and 9.9·10^12, each layout lasting 3 to 16 times longer than the one before.

**Accelerated halt hunt.** A 25-minute run of `cjump.py` reached step 39,282,271,415,780 (3.93·10^13) with 458 cells visited and no halt. From step 3.9·10^13 on the learner finds only short jumps (a layout with a 45-cell hub region), so the run slows to direct speed there.

## Status

Open.

- Lean (`lean/Blank.lean`): `step_none_iff`, no halt in 10,000 steps by the kernel, in 10,000,000 by `native_decide`.
- Lean, kernel (`lean/Counter.lean`): the borrow and carry rules of the two counters.
- C: no halt in 2·10^10 steps.
- Accelerated (`tools/py/bbtools/cjump.py`, trusted computation): no halt in 3.93·10^13 steps.

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
