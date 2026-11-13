# 1RB0RA_1RC0LC_0LD1RF_1RA1LE_1LD0LB_0RE---

bbchallenge id 180313. One of the six-state holdouts whose halting from blank tape is open. Family: **clock and word map (block grows by 2, the word is rewritten by 2^k excursions)** (with the four other clock machines of this batch).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RA |
| B | 1RC | 0LC |
| C | 0LD | 1RF |
| D | 1RA | 1LE |
| E | 1LD | 0LB |
| F | 0RE | --- |

## What it does

At every visit of the left end in state E the tape is `E>0 1^L 0 W`: a block of L ones and a word W of short
blocks. One step earlier the head was in state D on the first 1, one cell to the right: write `J(k, W)` for
`D>1 1^(3+2k-1) 0 W`.

**The clock.** `0 0 J(k, W)` reaches `J(k+1, W')` two cells to the left, where `W' = P^(2^k)(W)` for one fixed map
`P` on words. One application of P (a *P-step*) is one trip of the head into the word and back:
`L 0^3 1 B> W` → `L D> 1^3 0 W'`. The tick `k` is: the sweep (`0 0 D> 1^(3+2k) 0` → `1 0^(4+2k) 1 B>`),
one P-step, the ticks `0, ..., k-1` (each eats two of the zeros the sweep left), and the merge (`1 0 D>1` → `D>1 1 1`).
Its step count is `E + 12·2^k − 2`, E the total cost of the 2^k P-steps. Proved in Lean for every k and every word, whenever the 2^k P-steps all come back.

**The word.** After a leading block 3, a binary counter in the digits `1 1` (0) and `3` (1) that P steps by one;
a phase ends when it has run through (the word starts `3 1 1 1 1 …`).

**Phases.** A phase ends when a P-step does not come back (the front of the word has run out): the head goes left
over the unfinished recursion, the block is dissolved into the word, and a new phase starts from a short block.
Phases of the exact accelerated run with blocks of 9 or more:

| starts at step | block | last tick at step | block | ticks |
|---|---|---|---|---|
| 314 | 1^1 | 788 | 1^9 | 5 |
| 1,219 | 1^1 | 9,859 | 1^17 | 9 |
| 12,742 | 1^1 | 20,594 | 1^9 | 5 |
| 29,047 | 1^1 | 592,569 | 1^29 | 15 |
| 1,151,462 | 1^1 | 286,370,582 | 1^47 | 24 |
| 568,269,797 | 1^1 | 3,126,277,397 | 1^47 | 24 |
| 5,654,290,236 | 1^1 | 8.032·10^13 | 1^83 | 42 |
| 1.597·10^14 | 1^1 | 2.083·10^19 | 1^119 | 60 |
| 4.142·10^19 | 1^1 | 3.493·10^26 | 1^167 | 84 |
| 6.946·10^26 | 1^1 | 5.888·10^33 | 1^215 | 108 |
| 1.170·10^34 | 1^1 | 3.237·10^45 | 1^293 | 147 |
| 6.436·10^45 | 1^1 | 1.779·10^57 | 1^371 | 186 |
| 3.538·10^57 | 1^1 | 2.051·10^75 | 1^491 | 246 |
| 4.079·10^75 | 1^1 | 3.968·10^100 | 1^659 | 330 |
| 7.891·10^100 | 1^1 | 1.287·10^133 | 1^875 | 438 |
| 2.560·10^133 | 1^1 | 1.176·10^180 | 1^1187 | 594 |
| 2.339·10^180 | 1^1 | 2.817·10^232 | 1^1535 | 768 |

The run was followed to 2.419·10^242 steps (19 phases; block 1^1601 at the last visit followed): no halt.

**What a phase does to the word** (exact accelerated run, every phase to 10^60 steps). From the phase that starts at
step 29,047 on, the word at the last visit of a phase differs from the word at the first visit of that phase in
exactly two cells: cell 1 (the front digit `1 0 1 0` becomes `1 1 1 0`) and cell |W|−8; the 2^(k+1)−1 trips of the
whole phase undo each other everywhere else. At every phase end the next phase starts with a word of exactly
|W| + L + 7 cells (L the last block: the block is dissolved into the word), and from step 9,859 on its last 7 cells
are those of the old word. The rest of the new word is not a simple insertion: the dissolved block is mixed into the
whole word (the two words agree only in their first cell and their last 7). A model where the counter value of the
word drops by 2^k per tick (digits `1 0 1 0`, `1 0 1 1` = 0 and `1 1 1 0`, `1 1 1 1` = 1, least significant first) fits only 52 of the 355 ticks up to 10^30 steps. So the phase-to-phase map is not
simple, and non-halting does not yet reduce to a short arithmetic statement.

**Halting.** The only halting transition is F on 1, and F is entered only from C on 1 (1RF): the machine halts exactly when C reads a 1 followed by another 1, `C>1 1`. A normal tick cannot halt (it is proved to reach its end), so a halt can only come
at a phase end. Open: a closed form for P^(2^k) on the words that occur, what a phase end builds, and whether one
ever halts.

## Status

Open.

- Lean, kernel (`lean/Clock.lean`): `tick` (the clock for every k and every word, for each tick whose 2^k P-steps all come back, with the exact step count),
  `tick_left_end`; from `lean/Rules.lean` (`rule_sweep`, `rule_merge`, written by
  `holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/py/gen_clock.py` with `bbtools.symtm.prove`).
- Lean, kernel (`lean/Sweeps.lean`): the sweep rules of the self-loops.
- Lean, kernel (`lean/HaltPred.lean`, written by `python3 ../1RB0LD_0RC---_1LD0RF_0LE0RA_0RA1LF_0LA1LB/py/halt_pred.py 1RB0RA_1RC0LC_0LD1RF_1RA1LE_1LD0LB_0RE--- 1 2 3`):
  every configuration that halts after exactly 1, 2 or 3 more steps; `halt_iff_1`: the machine halts one step later exactly from `C>1 1`.
- Lean (`lean/Blank.lean`): the halting configurations (`step_none_iff`), no halt in 10,000 steps by the kernel, in
  10,000,000 by `native_decide`.
- Trusted computation: `holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/py/clock.py` (the tick done at once, P computed by running the machine
  and memoized) gives the same time, block and word as `tools/c/tmrun.c` at every visit of the left end in the
  first 2·10^10 steps (`tmcheck`), and follows the run through 19 phases to 2.419·10^242 steps without a halt.
- ngramcps (widths 2–6), `bbtools.ctl` and `bbtools.invariants` (earlier batch runs): nothing.

## Scripts

- `python3 holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/py/clock.py 1RB0RA_1RC0LC_0LD1RF_1RA1LE_1LD0LB_0RE--- tmcheck 2e10` — compare with `tmrun` at every visit (a few minutes).
- `python3 holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/py/clock.py 1RB0RA_1RC0LC_0LD1RF_1RA1LE_1LD0LB_0RE--- run 1000` — the phases up to 10^1000 steps.
- `python3 holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/py/gen_clock.py 1RB0RA_1RC0LC_0LD1RF_1RA1LE_1LD0LB_0RE---` — writes `lean/Rules.lean` and `lean/Clock.lean`.

## Next steps

Describe P^(2^k) on the words of the run in closed form (the word holds a counter that P counts down), accelerate a
phase end, and read off the map from one phase to the next.

## Pages

- [`pages/holdouts/1RB0RA_1RC0LC_0LD1RF_1RA1LE_1LD0LB_0RE---/explainer.html`](../../pages/holdouts/1RB0RA_1RC0LC_0LD1RF_1RA1LE_1LD0LB_0RE---/explainer.html)
- [`pages/holdouts/1RB0RA_1RC0LC_0LD1RF_1RA1LE_1LD0LB_0RE---/proof-status.html`](../../pages/holdouts/1RB0RA_1RC0LC_0LD1RF_1RA1LE_1LD0LB_0RE---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RA_1RC0LC_0LD1RF_1RA1LE_1LD0LB_0RE---/lean/check.sh
./tmrun 1RB0RA_1RC0LC_0LD1RF_1RA1LE_1LD0LB_0RE--- 20000000000 at E L 1500
python3 holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/py/clock.py 1RB0RA_1RC0LC_0LD1RF_1RA1LE_1LD0LB_0RE--- tmcheck 2e10
```
