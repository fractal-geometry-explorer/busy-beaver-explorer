# 1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_---0RB

bbchallenge id 145825. Group G01. **Block stack machine**: the tape is a stack of blocks of 1s; P(n) → P((3n+7)/2) for odd n, and a halving
recursion with pushes and pops for even n that ends in a halt, a provable endless loop, or a new P. Open;
probably non-halting. The model is proved in Lean; no halt in 650 rounds (more than 10^9,700 steps).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LE |
| B | 1LB | 1RC |
| C | 0RF | 0RD |
| D | 1RE | 0LA |
| E | 1LA | 1RE |
| F | --- | 0RB |

## What it does

Two kinds of configuration (k ≥ 0 stack blocks S1 … Sk, all blocks of 1s separated by `00`):

    P(n)          = 0^inf E> 0 0 1^n 0 1 0^inf                                (head at the left end)
    E(S, p, q, r) = 0^inf 1^S1 00 … 1^Sk 00 1^p 00 1^q 0 1^r E> 0^inf          (head at the right end)

P(n) goes to E([], 2, n−2, 2) in 5n − 6 steps. Then each sweep of the head (right to left and back) does:

| case | next | steps |
|---|---|---|
| q ≥ 4 | (p+2, q−2, r+1) | 8q + 4r − 9 |
| q = 3 | (p+2, 1, r+1) | 4r + 15 |
| q = 2, r = 1 | (p+2, 3, 1) | 31 |
| q = 2, r = 2 | **halt** | 21 (with the halting transition) |
| q = 2, r ≥ 3 | push p+2; (1, r−2, 1) | 8r |
| q = 1, stack S'·x | (S', x, p+r+4, 1) (pop) | 8r + 22 |
| q = 1, empty stack | P(p+r+4) | 3p + 11r + 35 |

From (p, 2, 3) the machine pushes p+2, works on (1, 1, 1), pops back to (p+2, 6, 1) and is at (p+6, 2, 3)
again: once (q, r) = (2, 3) occurs it never halts. So each round from P(n) ends in a halt, in this endless loop,
or in a new P. For odd n the round is P(n) → P((3n+7)/2); for even n the q block runs down to 2 with r = n/2 and
the recursion starts. From blank tape: P(1) at step 9, P(5) at 51, then n = 11, 20, 67, 104, 277, 419, 632,
2070, 5378, 11434, 24303, 36458, 77479 (step 8,252,212,075), …

Executable model: `py/model.py` (`run_P`); the same model as a Lean function: `sweep` in `lean/Orbit.lean`.

**Halting condition.** The machine halts iff some round of the orbit reaches (q, r) = (2, 2) before any
(2, 3).

**Heuristic.** For random P(n) with d digits the next round halts with frequency 4.4% (d = 6), 2.7% (8),
2.0% (10), 1.0% (12), 0.55% (15), 0.25% (20) (and loops forever with frequency 1.5%, …, 0.03%): roughly
∝ d^−2.3. The run's n has thousands of digits after 650 rounds (round 157 alone took n from 814 to 7,705 bits),
so a later halt looks very unlikely. No probability model is worked out.

## What is proved

| level | result | where |
|---|---|---|
| kernel | halting configurations; no halt in 10⁴ steps (10⁷ by native_decide) | `lean/Blank.lean` |
| kernel | 12 local rules (generated) | `lean/Rules.lean` from `py/rules.py` |
| kernel | crossing lemmas `cross_l` (E moves the hole left, 3 steps per 1) and `cross_r` (B moves right, 5 per 1), by induction; every row of the table above for all S, p, q, r (`round`, `rounds`, `sweep_q3`, `sweep_q2r1`, `sweep_halt`, `sweep_push`, `sweep_pop`, `sweep_pop_nil`, `to_P`, `from_P`) | `lean/Model.lean`, `lean/Orbit.lean` |
| kernel | `sweep` (one model step, j rounds at once) is sound for every input; `orbit fuel k 5` is sound; blank → P(5) in 51 steps | `sweep_sound`, `orbit_sound`, `init_P5` |
| kernel | 80 P-rounds without a halt, > 10¹⁰⁰ steps | `orbit_kernel`, `kernel_bound` |
| native | 650 P-rounds without a halt, > 10⁹⁷⁰⁰ steps (n has 16,129 bits) | `orbit_native`, `native_bound` |
| trusted | the model reproduces all 14 P-events of the real run up to 10¹⁰ steps, steps exact | `py/model.py blank 1e10`, `c/pevents.c` |
| trusted | (q, r) = (2, 3) loops forever | `py/model.py` (not in Lean) |
| heuristic | halting frequency per round falls like d^−2.3 | `py/model.py frac 4000` |
| open | does it halt? | |

`symtm` cannot cross the blocks of 1s by itself (crossing `1^k E> 0` reads the cell left of each copy:
`1 1 E> 0 → 1 E> 0 1`), hence the two hand-written crossing inductions.

## Reproduce

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_---0RB/lean/check.sh          # ~1 min
python3 holdouts/1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_---0RB/py/rules.py > holdouts/1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_---0RB/lean/Rules.lean
python3 holdouts/1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_---0RB/py/model.py blank 1e10
gcc -O2 -o pevents holdouts/1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_---0RB/c/pevents.c && ./pevents 10000000000    # ~4 min
python3 holdouts/1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_---0RB/py/model.py far 650                                # ~2 min
python3 holdouts/1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_---0RB/py/model.py frac 4000                              # slow for large d
```

## Further work

- Prove in Lean that (q, r) = (2, 3) loops forever (a one-line induction on the cycle); it would give a
  non-halting proof if the run ever got there.
- Understand the even-n recursion (its depth and the size of the result) well enough for a real probability
  estimate; round 651 is not finished after 3·10⁸ model operations.

## Pages

- [`pages/holdouts/1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_---0RB/explainer.html`](../../pages/holdouts/1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_---0RB/explainer.html)
- [`pages/holdouts/1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_---0RB/proof-status.html`](../../pages/holdouts/1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_---0RB/proof-status.html)
