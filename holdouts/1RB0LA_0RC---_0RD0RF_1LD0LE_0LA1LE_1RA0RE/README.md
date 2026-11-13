# 1RB0LA_0RC---_0RD0RF_1LD0LE_0LA1LE_1RA0RE

bbchallenge id 25624. One of the six-state holdouts whose halting from blank tape is open. Family: **hole-wandering solid block** (relative of [`1RB0LA_0RC---_0RD0RF_1LD0LE_0LA1LE_0RA0LA`](../1RB0LA_0RC---_0RD0RF_1LD0LE_0LA1LE_0RA0LA/README.md); here the odd rounds are the simple ones).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LA |
| B | 0RC | --- |
| C | 0RD | 0RF |
| D | 1LD | 0LE |
| E | 0LA | 1LE |
| F | 1RA | 0RE |

## Status

Open. Proved in Lean (kernel): the round pieces (`lean/Rules.lean`, from `py/rules.py`), the sweep by induction
and the whole round from an odd first block (`sweep`, `round_mod3`, `round_mod1` in `lean/Round.lean`). Generated:
halting configurations, no halt in 10^4 (kernel) / 10^7 (`native_decide`) steps. C: no halt in 10^9 steps.

## What it does

At the left end in state E the tape is blocks of 1s with single 0s between them (step 996,038,575:
`E>0 1^646 0 1^2825 0 1^438`). A round:

- **start** (`start`): `E> 0 1 1 1` → `1 0 A> 0 0 1`: the first two 1s become a pair of 0s;
- **sweep** (`pair`, `sweep`): `A> 0 0 1 1 1` → `1 0 A> 0 0 1`, 6 steps a pair (one cell of look-ahead, so the
  n-fold sweep is an induction rather than a shift rule);
- **odd end** (`endodd`): `A> 0 0 1 0 1^(a+3) 0 1` → `1 E> 0 1^(a+2) 0 1 1 1 1`: the hole is filled, the pair runs on as
  a glider (`glide`, 5 steps a cell) to the next hole, which reappears 3 cells left;
- **gliders** (`cycle`, iterated in `gliders`): two `1 0` pairs make the next glider; each moves the hole 3 cells left;
  `last`/`last2` finish at the left end.

Proved: [4K+3, a, b, ...] → [a+K, 3K+6+b, ...] and [4K+1, a, b, ...] → [a+K−1, 3K+6+b, ...] (Lean: second block
≥ 3 resp. 5, third block present; b = 0 checked numerically). All 344 odd rounds in 10^9 steps follow them; all 668
round starts after step 7 have single holes (2–5 blocks) (`py/rounds.py`).

Even first blocks: the pair of 0s passes through the hole into the next block; those rounds add 4–23 ones and are
not yet rules. Halting needs B on a 1, i.e. C on a 1 followed by `0 0 1`. Growth: round cost ≈ 1.5·x·a ~ w², gain
3–23 ones, so width ~ t^(1/3) (3,914 cells at 10^9).

Towards an invariant: from each of the 4,616 round starts `0? 1^a1 (0 1^ai)*` (a1 ≥ 1, ai ≥ 2) of at most 20 cells
the round ends on the same class except one (`11011101101101111111` → `0 1^3 0 1 0 1^25 0 1^9`; `py/classround.py`).
No finite-automata-reduction certificate with up to 8 DFA states on either side.

## Later

1. Rules for the even rounds (the sweep through a hole after an even block, and the gliders over the mark it leaves).
2. An invariant on the block list kept by every round; with all rounds proved, non-halting by induction on rounds.
   The same plan serves 1RB0LA_0RC---_0RD0RF_1LD0LE_0LA1LE_0RA0LA (where the even rounds are the proved ones).

## First look

Growth class **power/power** (left: power, exponent 0.337; right: power,
exponent 0.321). After 1,000,000,000 steps: 3,914 cells visited (1,341 left of the
start, 1,841 right), 3,756 ones.

- left, step 962,722,794: `E>0 1^1517 0 1^2361`
- left, step 980,967,219: `E>0 1^2514 0 1^1374`
- right, step 974,695,118: `1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 `
- right, step 993,550,399: `1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 `

## Pages

- [`pages/holdouts/1RB0LA_0RC---_0RD0RF_1LD0LE_0LA1LE_1RA0RE/explainer.html`](../../pages/holdouts/1RB0LA_0RC---_0RD0RF_1LD0LE_0LA1LE_1RA0RE/explainer.html)
- [`pages/holdouts/1RB0LA_0RC---_0RD0RF_1LD0LE_0LA1LE_1RA0RE/proof-status.html`](../../pages/holdouts/1RB0LA_0RC---_0RD0RF_1LD0LE_0LA1LE_1RA0RE/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LA_0RC---_0RD0RF_1LD0LE_0LA1LE_1RA0RE/lean/check.sh
python3 holdouts/1RB0LA_0RC---_0RD0RF_1LD0LE_0LA1LE_1RA0RE/py/rules.py | diff - holdouts/1RB0LA_0RC---_0RD0RF_1LD0LE_0LA1LE_1RA0RE/lean/Rules.lean
gcc -O2 -o /tmp/tmrun tools/c/tmrun.c && /tmp/tmrun 1RB0LA_0RC---_0RD0RF_1LD0LE_0LA1LE_1RA0RE 1000000000 at E L 100000 > /tmp/el.txt
python3 holdouts/1RB0LA_0RC---_0RD0RF_1LD0LE_0LA1LE_1RA0RE/py/rounds.py /tmp/el.txt
python3 holdouts/1RB0LA_0RC---_0RD0RF_1LD0LE_0LA1LE_1RA0RE/py/classround.py 1RB0LA_0RC---_0RD0RF_1LD0LE_0LA1LE_1RA0RE 20
```

## Accelerated run

Trusted computation: `python3 tools/py/bbtools/rleaccel.py 1RB0LA_0RC---_0RD0RF_1LD0LE_0LA1LE_1RA0RE 2 191800000` runs 191,800,000 macro steps from blank tape without a halt, more than 3.56·10^11
machine steps (tape: 27,928 cells). The simulator codes the tape in runs, crosses a run in one step and jumps cycles whose
one-cycle rule it has first proved symbolically; it is tested cell for cell against direct runs
(`tools/tests/test_rleaccel.py`).
