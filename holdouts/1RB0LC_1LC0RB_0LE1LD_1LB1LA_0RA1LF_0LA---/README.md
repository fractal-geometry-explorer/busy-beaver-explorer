# 1RB0LC_1LC0RB_0LE1LD_1LB1LA_0RA1LF_0LA---

bbchallenge id 74449. One of the six-state holdouts whose halting from blank tape is open. Family: **clock and word map (block grows by 3)**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LC |
| B | 1LC | 0RB |
| C | 0LE | 1LD |
| D | 1LB | 1LA |
| E | 0RA | 1LF |
| F | 0LA | --- |

## What it does

At every visit of the left end in state B on a 0 the tape is `B>0 1^L 0 W`: a block of L ones and a word W of short
blocks. One step earlier the head was in state D on a **0** one cell to the right (D writes the 1 and moves left):
write `J(k, W)` for `D>0 1^(3+3k) 0 W`, so that the visit has `L = 4+3k`.

**The clock.** `0 0 0 J(k, W)` reaches `J(k+1, W')` three cells to the left, where `W' = P^(2^k)(W)` for one fixed
map `P` on words. One application of P (a *P-step*) is one trip of the head through the word and back:
`L 0^4 B> 0 W` → `L D> 0 1^3 0 W'`. The tick `k` is: the sweep (`0 0 0 D> 0 1^(3+3k) 0` → `0 1 0^(5+3k) B> 0`,
the block becomes 0s), one P-step, the ticks `0, ..., k-1` (each eats three of the zeros the sweep left), and the
merge (`0 1 0 D>0` → `D>0 1 1 1`). Its step count is `E + 16·2^k − 3`, E the total cost of the 2^k P-steps.
**Proved in Lean for every k and every word, whenever the 2^k P-steps all come back** (`lean/Clock.lean`), the same clock as the five machines of
`holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE` with growth 3 and the head on the 0 left of the block
(`py/gen_clock.py` of that folder now takes the growth, the head cell and the shape of the sweep as parameters).

Unlike in that family, a P-step is long: it inverts every block of the word on its way right (`1^n` → `0^n`
between single 1s) and restores it on the way back, with small ticks of the same kind inside (`0 0 0 D>0 1^3`
deep in the word), so P reads the whole word; the accelerated run computes P with those inner ticks done at once.

**Phases.** A phase ends when a P-step does not come back. Phases of the exact accelerated run with 3 or more ticks
(`py/clock.py` of the clock family, checked against `tools/c/tmrun.c` at every visit of the left end in the first
2·10^10 steps):

| starts at step | block | last tick at step | block | ticks |
|---|---|---|---|---|
| 461 | 1^3 | 711 | 1^9 | 3 |
| 1,396 | 1^4 | 7,695 | 1^19 | 6 |
| 3,246,458 | 1^22 | 14,139,344 | 1^34 | 5 |
| 51,738,209 | 1^4 | 13,776,774,060 | 1^55 | 18 |
| 213,231,975,889 | 1^22 | 1.412·10^13 | 1^61 | 14 |

Phases do not always restart from a short block (1^22 twice). Between the last two the run does something new: the
visits at steps 26,873,638,645 and 53,065,176,208 still have the block 1^55, while the next block of the word grows
by 3 (`1^55 0 1^11` → `1^55 0 1^14` → `1^55 0 1^17`, `tools/c/tmrun.c`) and the time doubles: a clock on the second
block, whose ticks have `1^55 0` on their left instead of three 0s and so are not covered by the theorem. The same
happens after step 1.412·10^13: the accelerated run then advances by small ticks only (about 2.5·10^10 steps a
second) and was stopped at step 1.46·10^13.

**Halting.** The only halting transition is F on 1. F is entered only from E on 1 (1LF), and E only from C on 0 (0LE): the machine halts exactly when C reads a 0 with two 1s to its left, <code>1 1 C&gt;0</code>. A normal tick cannot halt (it is proved to reach its end), so a halt can only come where a P-step does not come back.

**Open:** a closed form for P on the words that occur, the second-level clock seen after a phase, and whether
`1 1 C>0` can ever occur.

## Status

Open.

- Lean, kernel (`lean/Clock.lean`): `tick` (the clock for every k and every word, for each tick whose 2^k P-steps all come back, with the exact step count),
  `tick_left_end`; from `lean/Rules.lean` (`rule_sweep`, `rule_merge`, written by
  `holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/py/gen_clock.py` with `bbtools.symtm.prove`).
- Lean, kernel (`lean/Sweeps.lean`): the sweep rules of the self-loops.
- Lean, kernel (`lean/HaltPred.lean`, written by `python3 ../1RB0LD_0RC---_1LD0RF_0LE0RA_0RA1LF_0LA1LB/py/halt_pred.py 1RB0LC_1LC0RB_0LE1LD_1LB1LA_0RA1LF_0LA--- 1 2 3`):
  every configuration that halts after exactly 1, 2 or 3 more steps; `halt_iff_2`: the machine halts two steps later exactly from `1 1 C>0`.
- Lean (`lean/Blank.lean`): the halting configurations (`step_none_iff`), no halt in 10,000 steps by the kernel, in
  10,000,000 by `native_decide`.
- Trusted computation: `holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/py/clock.py` gives the same time, block
  and word as `tools/c/tmrun.c` at every visit of the left end in the first 2·10^10 steps (45 visits, `tmcheck`), and
  follows the run to step 1.46·10^13 without a halt.
- Trusted computation: `py/clocktest.py` — tick k = 2^k applications of P, k = 0..9 in the phase from step 51,738,209
  (by running the machine, before the proof).
- C (`tools/c/tmrun.c`): no halt in 1.2·10^11 steps.
- ngramcps (widths 2–6), `bbtools.ctl` and `bbtools.invariants` (earlier batch runs): nothing.

## Scripts

- `python3 holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/py/clock.py 1RB0LC_1LC0RB_0LE1LD_1LB1LA_0RA1LF_0LA--- tmcheck 2e10` — compare with `tmrun` at every visit (about 15 minutes).
- `python3 holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/py/clock.py 1RB0LC_1LC0RB_0LE1LD_1LB1LA_0RA1LF_0LA--- run 14` — the phases up to 10^14 steps (slow after 1.4·10^13).
- `python3 holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/py/gen_clock.py 1RB0LC_1LC0RB_0LE1LD_1LB1LA_0RA1LF_0LA---` — writes `lean/Rules.lean` and `lean/Clock.lean`.
- `python3 py/clocktest.py 1RB0LC_1LC0RB_0LE1LD_1LB1LA_0RA1LF_0LA--- B 1000000000 51738209 3` — the clock test;
  `py/clocktest2.py` is the general form (any end of the tape, a prefix before the block, blocks of a repeated word),
  used for the three digit machines of batch 4.

## Next steps

Prove the second-level tick (`1^a 0 D>0 1^(3+3j) 0 W`, the left context `1^a 0` instead of `0 0 0`) the same way and
add it to the accelerated run, to follow the run past 1.4·10^13 steps; then describe P in closed form.

## Pages

- [`pages/holdouts/1RB0LC_1LC0RB_0LE1LD_1LB1LA_0RA1LF_0LA---/explainer.html`](../../pages/holdouts/1RB0LC_1LC0RB_0LE1LD_1LB1LA_0RA1LF_0LA---/explainer.html)
- [`pages/holdouts/1RB0LC_1LC0RB_0LE1LD_1LB1LA_0RA1LF_0LA---/proof-status.html`](../../pages/holdouts/1RB0LC_1LC0RB_0LE1LD_1LB1LA_0RA1LF_0LA---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LC_1LC0RB_0LE1LD_1LB1LA_0RA1LF_0LA---/lean/check.sh
./tmrun 1RB0LC_1LC0RB_0LE1LD_1LB1LA_0RA1LF_0LA--- 20000000000 at B L 1500
```
