# 1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE

bbchallenge id 131953. One of the six-state holdouts whose halting from blank tape is open. Family: **clock and word map (block grows by 2, the word is rewritten by 2^k excursions)** (with the four other clock machines of this batch).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RA |
| B | 0LC | 0RE |
| C | 1LE | 1LD |
| D | 0LE | --- |
| E | 1LF | 0LC |
| F | 1RA | 1LE |

## What it does

At every visit of the left end in state E the tape is `E>0 1^L 0 W`: a block of L ones and a word W of short
blocks. One step earlier the head was in state F on the first 1, one cell to the right: write `J(k, W)` for
`F>1 1^(3+2k-1) 0 W`.

**The clock.** `0 0 J(k, W)` reaches `J(k+1, W')` two cells to the left, where `W' = P^(2^k)(W)` for one fixed map
`P` on words. One application of P (a *P-step*) is one trip of the head into the word and back:
`L 0^3 1 B> W` → `L F> 1^3 0 W'`. The tick `k` is: the sweep (`0 0 F> 1^(3+2k) 0` → `1 0^(4+2k) 1 B>`),
one P-step, the ticks `0, ..., k-1` (each eats two of the zeros the sweep left), and the merge (`1 0 F>1` → `F>1 1 1`).
Its step count is `E + 12·2^k − 2`, E the total cost of the 2^k P-steps. Proved in Lean for every k and every word, whenever the 2^k P-steps all come back.

**The word.** P counts down: the front of the word is a gadget of period 8, followed by a binary counter in the
4-cell digits `1 0 1 0` (0) and `1 1 1 0` (1), least significant first, that P^8 decreases by one. A phase ends
when the counter has run out (the front reads `1 0 0` or `1 1 0`).

**Phases.** A phase ends when a P-step does not come back (the front of the word has run out): the head goes left
over the unfinished recursion, the block is dissolved into the word, and a new phase starts from a short block.
Phases of the exact accelerated run with blocks of 9 or more:

| starts at step | block | last tick at step | block | ticks |
|---|---|---|---|---|
| 1,445 | 1^1 | 2,985 | 1^13 | 7 |
| 4,154 | 1^1 | 11,188 | 1^13 | 7 |
| 31,418 | 1^1 | 143,586 | 1^25 | 13 |
| 198,015 | 1^1 | 8,071,467 | 1^37 | 19 |
| 11,970,070 | 1^1 | 451,987,952 | 1^49 | 25 |
| 669,385,415 | 1^1 | 258,411,079,219 | 1^67 | 34 |
| 385,756,391,164 | 1^1 | 2.827·10^12 | 1^67 | 34 |
| 4.033·10^12 | 1^1 | 1.387·10^15 | 1^91 | 46 |
| 2.071·10^15 | 1^1 | 1.387·10^18 | 1^111 | 56 |
| 2.740·10^18 | 1^1 | 3.693·10^22 | 1^139 | 70 |
| 7.299·10^22 | 1^1 | 1.731·10^26 | 1^163 | 82 |
| 3.420·10^26 | 1^1 | 8.851·10^30 | 1^193 | 97 |
| 1.749·10^31 | 1^1 | 4.396·10^39 | 1^253 | 127 |
| 8.689·10^39 | 1^1 | 3.787·10^49 | 1^319 | 160 |
| 7.485·10^49 | 1^1 | 6.361·10^56 | 1^367 | 184 |
| 1.257·10^57 | 1^1 | 1.084·10^67 | 1^435 | 218 |
| 2.103·10^67 | 1^1 | 1.541·10^82 | 1^535 | 268 |
| 2.990·10^82 | 1^1 | 7.227·10^103 | 1^679 | 340 |

The run was followed to 2.363·10^194 steps (30 phases; block 1^1279 at the last visit followed): no halt.

**What a phase does to the word** (exact accelerated run, every phase to 10^60 steps). At almost every phase end
from step 2,985 on the next phase starts with a word of |W| + L + 2 cells (L the last block; exceptions +3, +4 and
+14), keeping only a short tail (2 to 29 cells) of the old word. Over a phase the word changes at its front (cells
1, 5, 9, … of the counter) and in a group of cells near its end. No simple rule for the phase-to-phase map was found,
so non-halting does not yet reduce to a short statement.

**Halting.** The only halting transition is D on 1, and D is entered only from C on 1 (1LD): the machine halts exactly when C reads a 1 whose left neighbour is a 1, `1 C>1`. A normal tick cannot halt (it is proved to reach its end), so a halt can only come
at a phase end. Open: a closed form for P^(2^k) on the words that occur, what a phase end builds, and whether one
ever halts.

## Status

Open.

- Lean, kernel (`lean/Clock.lean`): `tick` (the clock for every k and every word, for each tick whose 2^k P-steps all come back, with the exact step count),
  `tick_left_end`; from `lean/Rules.lean` (`rule_sweep`, `rule_merge`, written by
  `holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/py/gen_clock.py` with `bbtools.symtm.prove`).
- Lean, kernel (`lean/Sweeps.lean`): the sweep rules of the self-loops.
- Lean, kernel (`lean/HaltPred.lean`, written by `python3 ../1RB0LD_0RC---_1LD0RF_0LE0RA_0RA1LF_0LA1LB/py/halt_pred.py 1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE 1 2 3`):
  every configuration that halts after exactly 1, 2 or 3 more steps; `halt_iff_1`: the machine halts one step later exactly from `1 C>1`.
- Lean (`lean/Blank.lean`): the halting configurations (`step_none_iff`), no halt in 10,000 steps by the kernel, in
  10,000,000 by `native_decide`.
- Trusted computation: `holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/py/clock.py` (the tick done at once, P computed by running the machine
  and memoized) gives the same time, block and word as `tools/c/tmrun.c` at every visit of the left end in the
  first 2·10^10 steps (`tmcheck`), and follows the run through 30 phases to 2.363·10^194 steps without a halt.
- ngramcps (widths 2–6), `bbtools.ctl` and `bbtools.invariants` (earlier batch runs): nothing.

## Scripts

- `python3 holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/py/clock.py 1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE tmcheck 2e10` — compare with `tmrun` at every visit (a few minutes).
- `python3 holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/py/clock.py 1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE run 1000` — the phases up to 10^1000 steps.
- `python3 holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/py/gen_clock.py 1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE` — writes `lean/Rules.lean` and `lean/Clock.lean`.

## Next steps

Describe P^(2^k) on the words of the run in closed form (the word holds a counter that P counts down), accelerate a
phase end, and read off the map from one phase to the next.

## Pages

- [`pages/holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/explainer.html`](../../pages/holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/explainer.html)
- [`pages/holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/proof-status.html`](../../pages/holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/lean/check.sh
./tmrun 1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE 20000000000 at E L 1500
python3 holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/py/clock.py 1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE tmcheck 2e10
```
