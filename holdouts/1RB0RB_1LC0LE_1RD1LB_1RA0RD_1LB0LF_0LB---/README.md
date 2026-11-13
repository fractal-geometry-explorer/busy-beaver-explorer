# 1RB0RB_1LC0LE_1RD1LB_1RA0RD_1LB0LF_0LB---

bbchallenge id 155590. One of the six-state holdouts whose halting from blank tape is open. Family: **clock and word map (block grows by 2, the word is rewritten by 2^k excursions)** (with the four other clock machines of this batch).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RB |
| B | 1LC | 0LE |
| C | 1RD | 1LB |
| D | 1RA | 0RD |
| E | 1LB | 0LF |
| F | 0LB | --- |

## What it does

At every visit of the left end in state B the tape is `B>0 1^L 0 W`: a block of L ones and a word W of short
blocks. One step earlier the head was in state C on the first 1, one cell to the right: write `J(k, W)` for
`C>1 1^(3+2k-1) 0 W`.

**The clock.** `0 0 J(k, W)` reaches `J(k+1, W')` two cells to the left, where `W' = P^(2^k)(W)` for one fixed map
`P` on words. One application of P (a *P-step*) is one trip of the head into the word and back:
`L 0^3 1 A> W` → `L C> 1^3 0 W'`. The tick `k` is: the sweep (`0 0 C> 1^(3+2k) 0` → `1 0^(4+2k) 1 A>`),
one P-step, the ticks `0, ..., k-1` (each eats two of the zeros the sweep left), and the merge (`1 0 C>1` → `C>1 1 1`).
Its step count is `E + 12·2^k − 2`, E the total cost of the 2^k P-steps. Proved in Lean for every k and every word, whenever the 2^k P-steps all come back.

**The word.** Blocks 1, 1^3, 1^5, … with double 0s; P is irregular (some trips rewrite a long stretch). Not
identified.

**Phases.** A phase ends when a P-step does not come back (the front of the word has run out): the head goes left
over the unfinished recursion, the block is dissolved into the word, and a new phase starts from a short block.
Phases of the exact accelerated run with blocks of 9 or more:

| starts at step | block | last tick at step | block | ticks |
|---|---|---|---|---|
| 530 | 1^1 | 2,124 | 1^13 | 7 |
| 3,647 | 1^1 | 31,393 | 1^21 | 11 |
| 33,588 | 1^1 | 87,128 | 1^17 | 9 |
| 140,843 | 1^1 | 1,867,573 | 1^33 | 17 |
| 2,158,610 | 1^1 | 3,741,882 | 1^11 | 6 |
| 5,307,819 | 1^1 | 195,932,189 | 1^45 | 23 |
| 199,035,980 | 1^1 | 4,858,359,866 | 1^43 | 22 |
| 4,863,510,345 | 1^1 | 1.266·10^12 | 1^55 | 28 |
| 1.276·10^12 | 1^1 | 4.069·10^12 | 1^37 | 19 |
| 4.071·10^12 | 1^1 | 4.352·10^13 | 1^61 | 31 |
| 4.368·10^13 | 1^1 | 3.633·10^18 | 1^91 | 46 |

The run was followed to 3.634·10^18 steps (14 phases; block 1^5 at the last visit followed): no halt.

**Halting.** The only halting transition is F on 1. F is entered only from E on 1 (0LF), and E only from B on 1 (0LE): the machine halts exactly when B reads a 1 with two 1s to its left, `1 1 B>1`. A normal tick cannot halt (it is proved to reach its end), so a halt can only come
at a phase end. Open: a closed form for P^(2^k) on the words that occur, what a phase end builds, and whether one
ever halts.

## Status

Open.

- Lean, kernel (`lean/Clock.lean`): `tick` (the clock for every k and every word, for each tick whose 2^k P-steps all come back, with the exact step count),
  `tick_left_end`; from `lean/Rules.lean` (`rule_sweep`, `rule_merge`, written by
  `holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/py/gen_clock.py` with `bbtools.symtm.prove`).
- Lean, kernel (`lean/Sweeps.lean`): the sweep rules of the self-loops.
- Lean, kernel (`lean/HaltPred.lean`, written by `python3 ../1RB0LD_0RC---_1LD0RF_0LE0RA_0RA1LF_0LA1LB/py/halt_pred.py 1RB0RB_1LC0LE_1RD1LB_1RA0RD_1LB0LF_0LB--- 1 2 3`):
  every configuration that halts after exactly 1, 2 or 3 more steps; `halt_iff_2`: the machine halts two steps later exactly from `1 1 B>1`.
- Lean (`lean/Blank.lean`): the halting configurations (`step_none_iff`), no halt in 10,000 steps by the kernel, in
  10,000,000 by `native_decide`.
- Trusted computation: `holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/py/clock.py` (the tick done at once, P computed by running the machine
  and memoized) gives the same time, block and word as `tools/c/tmrun.c` at every visit of the left end in the
  first 2·10^10 steps (`tmcheck`), and follows the run through 14 phases to 3.634·10^18 steps without a halt.
- ngramcps (widths 2–6), `bbtools.ctl` and `bbtools.invariants` (earlier batch runs): nothing.

## Scripts

- `python3 holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/py/clock.py 1RB0RB_1LC0LE_1RD1LB_1RA0RD_1LB0LF_0LB--- tmcheck 2e10` — compare with `tmrun` at every visit (a few minutes).
- `python3 holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/py/clock.py 1RB0RB_1LC0LE_1RD1LB_1RA0RD_1LB0LF_0LB--- run 1000` — the phases up to 10^1000 steps.
- `python3 holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/py/gen_clock.py 1RB0RB_1LC0LE_1RD1LB_1RA0RD_1LB0LF_0LB---` — writes `lean/Rules.lean` and `lean/Clock.lean`.

## Next steps

Describe P^(2^k) on the words of the run in closed form (the word holds a counter that P counts down), accelerate a
phase end, and read off the map from one phase to the next.

## Pages

- [`pages/holdouts/1RB0RB_1LC0LE_1RD1LB_1RA0RD_1LB0LF_0LB---/explainer.html`](../../pages/holdouts/1RB0RB_1LC0LE_1RD1LB_1RA0RD_1LB0LF_0LB---/explainer.html)
- [`pages/holdouts/1RB0RB_1LC0LE_1RD1LB_1RA0RD_1LB0LF_0LB---/proof-status.html`](../../pages/holdouts/1RB0RB_1LC0LE_1RD1LB_1RA0RD_1LB0LF_0LB---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RB_1LC0LE_1RD1LB_1RA0RD_1LB0LF_0LB---/lean/check.sh
./tmrun 1RB0RB_1LC0LE_1RD1LB_1RA0RD_1LB0LF_0LB--- 20000000000 at B L 1500
python3 holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/py/clock.py 1RB0RB_1LC0LE_1RD1LB_1RA0RD_1LB0LF_0LB--- tmcheck 2e10
```
