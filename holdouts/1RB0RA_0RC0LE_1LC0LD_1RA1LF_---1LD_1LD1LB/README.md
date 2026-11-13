# 1RB0RA_0RC0LE_1LC0LD_1RA1LF_---1LD_1LD1LB

bbchallenge id 65692. One of the six-state holdouts whose halting from blank tape is open. Family: **clock and word map (block grows by 2, the word is rewritten by 2^k excursions)** (with the four other clock machines of this batch).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RA |
| B | 0RC | 0LE |
| C | 1LC | 0LD |
| D | 1RA | 1LF |
| E | --- | 1LD |
| F | 1LD | 1LB |

## What it does

At every visit of the left end in state F the tape is `F>0 1^L 0 W`: a block of L ones and a word W of short
blocks. One step earlier the head was in state D on the first 1, one cell to the right: write `J(k, W)` for
`D>1 1^(2+2k-1) 0 W`.

**The clock.** `0 0 J(k, W)` reaches `J(k+1, W')` two cells to the left, where `W' = P^(2^k)(W)` for one fixed map
`P` on words. One application of P (a *P-step*) is one trip of the head into the word and back:
`L 0^2 1 B> W` → `L D> 1^2 0 W'`. The tick `k` is: the sweep (`0 0 D> 1^(2+2k) 0` → `1 0^(3+2k) 1 B>`),
one P-step, the ticks `0, ..., k-1` (each eats two of the zeros the sweep left), and the merge (`1 0 D>1` → `D>1 1 1`).
Its step count is `E + 11·2^k − 2`, E the total cost of the 2^k P-steps. Proved in Lean for every k and every word, whenever the 2^k P-steps all come back.

**The word.** A string of the blocks `1` and `1^3`; P rewrites a front part of variable length. It is not a plain
binary counter (the words do not repeat with period 2^j); its numeration is not identified.
Every phase measured ends at a word `1 1 3 3 … 3 1 0 0` (a counter with all digits 3); the last blocks of the
phases grow by a factor of about 1.7 (8, 18, 30, 54, 94, 158, 268, 454).

**Phases.** A phase ends when a P-step does not come back (the front of the word has run out): the head goes left
over the unfinished recursion, the block is dissolved into the word, and a new phase starts from a short block.
Phases of the exact accelerated run with blocks of 8 or more:

| starts at step | block | last tick at step | block | ticks |
|---|---|---|---|---|
| 1,156 | 1^2 | 2,166 | 1^8 | 4 |
| 3,515 | 1^2 | 21,905 | 1^18 | 9 |
| 25,610 | 1^2 | 2,457,732 | 1^30 | 15 |
| 4,198,429 | 1^2 | 4,852,948,973 | 1^54 | 27 |
| 7,862,920,640 | 1^2 | 5.084·10^15 | 1^94 | 47 |
| 6.155·10^15 | 1^2 | 2.183·10^25 | 1^158 | 79 |
| 3.947·10^25 | 1^2 | 7.867·10^41 | 1^268 | 134 |
| 1.349·10^42 | 1^2 | 7.791·10^69 | 1^454 | 227 |

The run was followed to 8.229·10^69 steps (10 phases; block 1^184 at the last visit followed): no halt.

**Halting.** The only halting transition is E on 0. E is entered only from B on 1 (0LE), and B from A on 0 (1RB, after which E reads the 1 that A just wrote, so no halt) or from F on 1 (1LB): the machine halts exactly when F reads a 1 with `0 1` to its left, `0 1 F>1`. A normal tick cannot halt (it is proved to reach its end), so a halt can only come
at a phase end. Open: a closed form for P^(2^k) on the words that occur, what a phase end builds, and whether one
ever halts.

## Status

Open.

- Lean, kernel (`lean/Clock.lean`): `tick` (the clock for every k and every word, for each tick whose 2^k P-steps all come back, with the exact step count),
  `tick_left_end`; from `lean/Rules.lean` (`rule_sweep`, `rule_merge`, written by
  `holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/py/gen_clock.py` with `bbtools.symtm.prove`).
- Lean, kernel (`lean/Sweeps.lean`): the sweep rules of the self-loops.
- Lean, kernel (`lean/HaltPred.lean`, written by `python3 ../1RB0LD_0RC---_1LD0RF_0LE0RA_0RA1LF_0LA1LB/py/halt_pred.py 1RB0RA_0RC0LE_1LC0LD_1RA1LF_---1LD_1LD1LB 1 2 3`):
  every configuration that halts after exactly 1, 2 or 3 more steps; `halt_iff_2`: the machine halts two steps later exactly from `0 1 F>1`.
- Lean (`lean/Blank.lean`): the halting configurations (`step_none_iff`), no halt in 10,000 steps by the kernel, in
  10,000,000 by `native_decide`.
- Trusted computation: `holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/py/clock.py` (the tick done at once, P computed by running the machine
  and memoized) gives the same time, block and word as `tools/c/tmrun.c` at every visit of the left end in the
  first 2·10^10 steps (`tmcheck`), and follows the run through 10 phases to 8.229·10^69 steps without a halt.
- ngramcps (widths 2–6), `bbtools.ctl` and `bbtools.invariants` (earlier batch runs): nothing.

## Scripts

- `python3 holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/py/clock.py 1RB0RA_0RC0LE_1LC0LD_1RA1LF_---1LD_1LD1LB tmcheck 2e10` — compare with `tmrun` at every visit (a few minutes).
- `python3 holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/py/clock.py 1RB0RA_0RC0LE_1LC0LD_1RA1LF_---1LD_1LD1LB run 1000` — the phases up to 10^1000 steps.
- `python3 holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/py/gen_clock.py 1RB0RA_0RC0LE_1LC0LD_1RA1LF_---1LD_1LD1LB` — writes `lean/Rules.lean` and `lean/Clock.lean`.

## Next steps

Describe P^(2^k) on the words of the run in closed form (the word holds a counter that P counts down), accelerate a
phase end, and read off the map from one phase to the next.

## Pages

- [`pages/holdouts/1RB0RA_0RC0LE_1LC0LD_1RA1LF_---1LD_1LD1LB/explainer.html`](../../pages/holdouts/1RB0RA_0RC0LE_1LC0LD_1RA1LF_---1LD_1LD1LB/explainer.html)
- [`pages/holdouts/1RB0RA_0RC0LE_1LC0LD_1RA1LF_---1LD_1LD1LB/proof-status.html`](../../pages/holdouts/1RB0RA_0RC0LE_1LC0LD_1RA1LF_---1LD_1LD1LB/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RA_0RC0LE_1LC0LD_1RA1LF_---1LD_1LD1LB/lean/check.sh
./tmrun 1RB0RA_0RC0LE_1LC0LD_1RA1LF_---1LD_1LD1LB 20000000000 at F L 1500
python3 holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/py/clock.py 1RB0RA_0RC0LE_1LC0LD_1RA1LF_---1LD_1LD1LB tmcheck 2e10
```
