# 1RB0LA_0RC0RF_0RD0RA_1LD0LE_0LA1LE_---1LB

bbchallenge id 77933. One of the six-state holdouts whose halting from blank tape is open. Family: **hole-wandering solid block** (twin of [`1RB0LA_0RC---_0RD0RF_1LD0LE_0LA1LE_0RA0LA`](../1RB0LA_0RC---_0RD0RF_1LD0LE_0LA1LE_0RA0LA/README.md)).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LA |
| B | 0RC | 0RF |
| C | 0RD | 0RA |
| D | 1LD | 0LE |
| E | 0LA | 1LE |
| F | --- | 1LB |

## Status

Open. Proved in Lean (kernel): the round pieces (`lean/Rules.lean`, from `py/rules.py`) and the whole round from
an even first block (`round_mod4`, `round_mod2` in `lean/Round.lean`), the same theorems as for
1RB0LA_0RC---_0RD0RF_1LD0LE_0LA1LE_0RA0LA. Generated: halting configurations, no halt in 10^4 (kernel) / 10^7 (`native_decide`)
steps. C: no halt in 10^9 steps.

## What it does

Same macro structure as 1RB0LA_0RC---_0RD0RF_1LD0LE_0LA1LE_0RA0LA (see its README): at the left end in state E the tape is
blocks of 1s with single 0s between them; a round is a sweep (`0 C> (11)^n` → `(01)^n 0 C>`, here by B, C, A), a
glider (`0 0 D> 1^n` → `1^n 0 0 D>`) from an even block to the next hole, which reappears 3 cells left, and one more
glider per two pairs. Even rounds are identical in both machines (the round [16, 20] → [24, 15] takes 715 steps in
each), proved: [4K, a, b, ...] → [a+K, 3K+3+b, ...], [4K+2, a, b, ...] → [a+K, 3K+6+b, ...]. All 329 even rounds in
10^9 steps follow it (`py/rounds.py` on a `tmrun ... at E L` log): 660 round starts, all single holes after step 204,
2–5 blocks.

The machines differ in the odd rounds. The sweep through a hole after an odd stretch, `C>1 0 1 1` → `0 1 0 C>1`, is
the same; on `C>1 0 1 0` (a block of a single 1) this machine goes C1→0RA, A0→1RB, B1→0RF and F reads 0: **halt**.
So a halt needs a sweep from an odd stretch to meet a block of length 1. After step 2,136 no round start has had a
block shorter than 12 in 10^9 steps. Odd rounds add 4–28 ones (the twin: 4–18).

Growth: round cost ≈ 1.5·x·a ~ w², gain 3–28 ones, so width ~ t^(1/3) (3,867 cells at 10^9 steps).

## Later

1. Shares the plan of 1RB0LA_0RC---_0RD0RF_1LD0LE_0LA1LE_0RA0LA: write the odd rounds as rules (sweep through holes, gliders over the
   marks), then a block-list map and an invariant. Here the invariant must also keep every block longer than 1.

## First look

Growth class **power/power** (left: power, exponent 0.331; right: power,
exponent 0.332). After 1,000,000,000 steps: 3,867 cells visited (1,355 left of the
start, 1,822 right), 3,172 ones.

- left, step 967,436,269: `A>0 0^2 1^1479 0 1^2307`
- left, step 983,437,816: `A>0 0^2 1^959 0 1^2868`
- right, step 967,452,731: `1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 `
- right, step 983,451,241: `1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 `

## Pages

- [`pages/holdouts/1RB0LA_0RC0RF_0RD0RA_1LD0LE_0LA1LE_---1LB/explainer.html`](../../pages/holdouts/1RB0LA_0RC0RF_0RD0RA_1LD0LE_0LA1LE_---1LB/explainer.html)
- [`pages/holdouts/1RB0LA_0RC0RF_0RD0RA_1LD0LE_0LA1LE_---1LB/proof-status.html`](../../pages/holdouts/1RB0LA_0RC0RF_0RD0RA_1LD0LE_0LA1LE_---1LB/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LA_0RC0RF_0RD0RA_1LD0LE_0LA1LE_---1LB/lean/check.sh
python3 holdouts/1RB0LA_0RC0RF_0RD0RA_1LD0LE_0LA1LE_---1LB/py/rules.py | diff - holdouts/1RB0LA_0RC0RF_0RD0RA_1LD0LE_0LA1LE_---1LB/lean/Rules.lean
gcc -O2 -o /tmp/tmrun tools/c/tmrun.c && /tmp/tmrun 1RB0LA_0RC0RF_0RD0RA_1LD0LE_0LA1LE_---1LB 1000000000 at E L 100000 > /tmp/el.txt
python3 holdouts/1RB0LA_0RC0RF_0RD0RA_1LD0LE_0LA1LE_---1LB/py/rounds.py /tmp/el.txt
```

## Accelerated run

Trusted computation: `python3 tools/py/bbtools/rleaccel.py 1RB0LA_0RC0RF_0RD0RA_1LD0LE_0LA1LE_---1LB 2 194600000` runs 194,600,000 macro steps from blank tape without a halt, more than 3.34·10^11
machine steps (tape: 26,988 cells). The simulator codes the tape in runs, crosses a run in one step and jumps cycles whose
one-cycle rule it has first proved symbolically; it is tested cell for cell against direct runs
(`tools/tests/test_rleaccel.py`).
