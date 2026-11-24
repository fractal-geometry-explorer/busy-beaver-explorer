# 1RB0RD_1LC1RE_0LD1LC_1RA0LA_1RF0RC_---1RA

bbchallenge id 25604. One of the six-state holdouts whose halting from blank tape is open. Family: **counter of 1^4 blocks (left end)**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RD |
| B | 1LC | 1RE |
| C | 0LD | 1LC |
| D | 1RA | 0LA |
| E | 1RF | 0RC |
| F | --- | 1RA |

## What it does

At every visit of the left end in state C (on a 0, then `1^4`) the tape starts with a row of n blocks `1^4 0`. Along a
stretch n grows by 1 per visit and the gap between visits tends to double (ratios 1.08, 1.15, 1.26, 1.42, ..., 1.96);
now and then n drops by 2–4 while the word of longer blocks behind the row (1^3, 1^7, 1^11, 1^23, ...) is rebuilt.
n = 27 at step 15,886,922,696 (`tools/c/tmrun.c`, `at C L`, 2·10^10 steps).

**Halting.** F on 0 is the only halt; F is entered only from E on 0, E only from B on 1: the machine halts exactly at
`B>1 0 0`. Not seen.

**Open:** the overflow rule (the left counter is short and overflows often), and whether `B>1 0 0` can occur.

## The two counters

At every visit of the hub turn, A reading 1 at cell -125 at step 5.9·10^9, the tape reads as two binary counters back to back:

- **left counter**, lowest digit next to the hub: 5-cell digits `11011` (1) and `01011` (0), the lowest digit one cell (`1` is 1); these are the blocks `1^4 0` of the row the first look saw at the left end;
- **right counter**, lowest digit next to the hub: 4-cell digits `1111` (1) and `1110` (0), the lowest digit one cell.

Each hub event takes 1 from the left counter and adds 1 to the right counter. Its cost is linear in what changes:
20 steps per left digit changed, 22 per right digit changed, plus a constant. `tools/py/bbtools/cjump.py` learns these words and costs from the run (exact
rational fit, accepted only if it predicts every observed event, whole tape and step count) and then jumps whole
stretches of counting at once; it matched direct runs exactly at every check.

**Proved in Lean** (`lean/Counter.lean`, kernel, for every `k`, `j` and every tape beyond the cells shown, written by
`py/rules.py` from 4,000 sampled events):

- `borrow` (20k + 46 steps): `L 11011 (01011)^k 0 1 A> 1 0 0 1 0 1 1 1 R` -> `L 01011 (11011)^k 1 1 A> 1 0 0 1 1 1 1 1 R`, the left counter borrowing through `k` digits;
- `carry0` (22j + 48 steps): `L 1 1 A> 1 0 0 1 (1111)^j 1 1 1 1 0 1 1 1 R` -> `L 0 1 A> 1 0 0 (1011)^j 1 0 1 1 1 1 1 1 1 R`, the right counter carrying through `j` digits;
- `carry1` (22j + 680 steps): the same beyond a 60-cell stretch of the right counter, the right counter carrying through `j` digits;
- `plain` (48 steps): `L 1 1 A> 1 0 0 1 1 1 1 1 0 1 1 1 R` -> `L 0 1 A> 1 0 0 1 0 1 1 1 1 1 1 1 R`, the most frequent short event.

**Overflows.** When the left counter runs out the hub moves and the counters are laid out again; the accelerator
then simulates directly until it can learn the new layout. Seen so far: the hub turn moved to cells -73, -100 and -125 at steps 4.8·10^6, 2.8·10^8 and 5.0·10^9. The left counter is short, so its overflows are frequent: they are the drops of n that the first look saw.

**Accelerated halt hunt.** A 30-minute run of `cjump.py` reached step 11,563,284,563 (1.16·10^10) with 282 cells visited and no halt. The left counter stays short (a few digits), so jumps are short and most events are simulated directly.

## Status

Open.

- Lean, kernel (`lean/Sweeps.lean`, written by `holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/py/sweeps.py`): the sweep rules of the self-loops.
- Lean (`lean/Blank.lean`): `step_none_iff`, no halt in 10,000 steps by the kernel, in 10,000,000 by `native_decide`.
- Lean, kernel (`lean/Counter.lean`): the borrow and carry rules of the two counters.
- C: no halt in 2·10^10 steps.
- Accelerated (`tools/py/bbtools/cjump.py`, trusted computation): no halt in 1.16·10^10 steps.

## Next steps

Decode the overflow first: here it happens every few dozen events, so it decides the long-run behaviour more than the counting does.

## Pages

- [`pages/holdouts/1RB0RD_1LC1RE_0LD1LC_1RA0LA_1RF0RC_---1RA/explainer.html`](../../pages/holdouts/1RB0RD_1LC1RE_0LD1LC_1RA0LA_1RF0RC_---1RA/explainer.html)
- [`pages/holdouts/1RB0RD_1LC1RE_0LD1LC_1RA0LA_1RF0RC_---1RA/proof-status.html`](../../pages/holdouts/1RB0RD_1LC1RE_0LD1LC_1RA0LA_1RF0RC_---1RA/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RD_1LC1RE_0LD1LC_1RA0LA_1RF0RC_---1RA/lean/check.sh
./tmrun 1RB0RD_1LC1RE_0LD1LC_1RA0LA_1RF0RC_---1RA 20000000000 at C L 1500
python3 tools/py/bbtools/cjump.py 1RB0RD_1LC1RE_0LD1LC_1RA0LA_1RF0RC_---1RA 1e3000 1800      # accelerated, 30 minutes
python3 holdouts/1RB0RD_1LC1RE_0LD1LC_1RA0LA_1RF0RC_---1RA/py/rules.py                        # writes lean/Counter.lean
```
