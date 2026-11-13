# 1RB1LF_1LC0RD_---1LA_0LA0RE_1LA1RA_1LB0LD

bbchallenge id 176107. One of the six-state holdouts whose halting from blank tape is open.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LF |
| B | 1LC | 0RD |
| C | --- | 1LA |
| D | 0LA | 0RE |
| E | 1LA | 1RA |
| F | 1LB | 0LD |

## What it does

Family: **Collatz-like (4n/3) with a tail stack.**

The run is a sequence of *rounds*. At the start of each round the whole tape is

    D> 0 0 111 0 1^n T

the head at the left end in state D, a block of `n` ones and a short *tail* `T` (a word starting with 0) on the
right; blank on both sides. Blank tape reaches `n = 3`, `T` empty after 51 steps.

* **Sweeps.** After 60 steps the tape is `A> 0 11 0 11 0 1^(n+3) T`. Each sweep runs right to the block of ones,
  takes three ones from it and comes back: `A> 0 11 0 11 0 (1110)^k 1^(m+3) T` becomes
  `A> 0 11 0 11 0 (1110)^(k+1) 1^m T` in 10k + 45 steps (on the way right the blocks `1110` are written as `1100`,
  on the way back restored). The tape grows by one cell on the left per sweep: the left side grows like
  sqrt(steps).
* **End of round.** Write `n = c + 1 + 3t` with `c` in {0, 1, 2}. After the sweeps 1, 2 or 3 ones are left; the
  head turns each of the `t` counting blocks into four ones, works on the tail, and the next round starts with
  `n' = 4t + d` ones and a new tail `T'`, where `(d, T')` depends only on `(T, c)`. Only here does the tape reach
  one cell further right, once per round, and rounds grow by a factor of about (4/3)^2 in length: the right side
  grows like log(steps).

The tail map, for the tails the run visits most (`c = 0` and `c = 2` act the same for every tail seen):

| tail T | blocks of ones | c = 0 or 2 | c = 1 |
|---|---|---|---|
| (empty) | | 4t+11, empty | 4t+7, `011` |
| `011` | 2 | 4t+11, `011` | 4t+7, `010111` |
| `010111` | 1, 3 | 4t+19, empty | 4t+11, `01101` |
| `01101` | 2, 1 | 4t+23, empty | 4t+7, `0110111` |
| `0110111` | 2, 3 | 4t+11, `01101` | 4t+7, `0101111111` |
| `0101111111` | 1, 7 | 4t+27, empty | 4t+11, `01101011` |

So `n` is multiplied by about 4/3 each round (`n -> 4 floor((n-1)/3) + d`), and the tail is a small stack: a round
with `n ≡ 2 (mod 3)` pushes it one shape deeper, the other rounds keep it or pop it back. From blank tape:
n = 3, 11, 19, 35, 51, 83, 115, 163, 227, 307, 427, ... with tails empty, empty, 011, 011, 010111, empty, 011, ...

**Halting.** The sweeps and the common round ends never halt, but some deep tails do: the end of the round runs into
C reading 0. The nearest halting tail found (`py/roundmap.py graph`) has blocks of ones 2, 1, 1, 1, 2
(`0110101010 11`) with `c = 0` or `2`; it is 36 rounds from the empty tail, 29 of them pushes. Lean checks that the
round start with 57 ones and that tail halts (`halting_round`, and `roundMap_halt` for the map).

**The round map, for every tail (Lean).** After the sweeps the tape is `0 11 0 11 0 111 (0111)^t 0 1^c T`. Whatever
the tail, the head only crosses the long run of counting blocks *whole*, in one of six ways:

| state | direction | block before | block after |
|---|---|---|---|
| A | right | `0111` | `1001` |
| D | right | `1101` | `0110` |
| A | left | `1001` | `1101` |
| F | left | `0110` | `1111` |
| C | left | `1001` | `1111` |
| D | left | `0110` | `0111` |

So the round end is computed by a small simulator (`lean/Zone.lean`, `py/zonemap.py`) that keeps one counting block
on each side, steps cell by cell at the two ends and jumps over the `t - 2` blocks between by a shift rule. It never
looks at `t`, and gives the round map

    roundMap (n, T) = (4 (t - 2) + N, T')   with (N, T') computed from T and c alone,   or halt,   or stuck

(`stuck`: the head met the block in a way the six rules do not cover, or the fuel ran out; never seen). Lean proves
that the answer is what the machine does, for all `n >= 7` and every word `T` (`round_next`, `round_halt`), and the
reduction (`halts_iff`): **if the map never answers `stuck` along the orbit of `(11, empty)`, the machine halts
from blank tape iff the orbit reaches a halting round.** Unconditionally, a halting round in the orbit gives a halt
(`halts_of_orbit`) and an orbit that never ends gives a run that never halts (`not_halts_of_orbit`).

**Orbit.** 2·10^6 rounds of the map from blank tape (n then has 249,880 digits) never reach a halting tail, and the
map always answers. Only 26 tails occur: empty and `011` in 78% of the rounds, each further level about three times
rarer; the deepest has five blocks of ones (2, 1, 2, 1, 3).

**Heuristic.** With `c` uniform and independent between rounds (it is, empirically, for each tail), the tail is a
recurrent Markov chain, and an excursion from the empty tail hits a halting tail with probability between about
10^-18 (the shortest path alone) and 10^-13 (no halting mass found with paths pruned below 10^-13). So the model
halts with probability 1, but only after some 10^13 to 10^18 rounds, when `n` has more than 10^12 digits. Like
Antihydra, the question is about the base-3 digits of an orbit of a 4/3-type map, and out of reach.

## Status

Open; reduced to the orbit of the round map. Lean, all by the kernel:

* `lean/Blank.lean` (generated): the halting configurations (`step_none_iff`); no halt in 10,000 steps by the
  kernel, in 10,000,000 by `native_decide`.
* `lean/Rules.lean` (generated by `py/rules.py` with `tools/py/bbtools/symtm.py`): `start`, `sweep0`, `sweep`, and
  the round ends `end_e1` ... `end_b3` for the tails empty (`e`), `011` (`a`), `010111` (`b`), for all `k`.
* `lean/Round.lean`: the sweeps by induction (`sweeps`, `to_end`); the round map `next` on the three tails and
  `round`; `blank_to_round`: blank tape reaches `R0 3 []` in 51 steps; `halting_round`: a round start with a deep
  tail halts.
* `lean/Zone.lean` (generic in the machine): the simulator around one long repeated block and its soundness for
  every number of copies (`arun_sound`, `arun_halt`).
* `lean/Reduction.lean`: the six shift rules, `roundMap`, `round_next`, `round_halt`, `orbit`, `halts_iff`,
  `halts_of_orbit`, `not_halts_of_orbit`; `first_rounds`: the map answers for the first 500 rounds of the orbit
  (kernel evaluation); `orbit_10`: after ten rounds, 579 ones and the empty tail.

Computed: `py/zonemap.py` is the Lean round map in Python: `check 3000` compares it with a plain simulation of the
round (`py/roundmap.py`, two values of `t` per case) on 7,947 cases (tail, c), no mismatch, 4 halting cases, never
stuck; `orbit 2000000` (about 25 minutes). `py/roundmap.py check 22`: the plain round map against the machine for 22
rounds (1.4·10^8 steps); `graph 3000`: the tail graph and its halting tails. C (`tools/c/triage.c`): no halt in 10^9
steps.

## For later

* Remove the hypothesis of `halts_iff`: prove that the simulator never answers `stuck`. That needs a description of
  the reachable tails (they are words `0 1^a1 0 1^a2 ...`; the tail map acts on the first few blocks like a small
  machine of its own: e.g. `[2, 1, x] -> [2, 1, x - 5]`, `[2, x] -> [2, x - 2]`, pushes `[2, x] -> [2, 3, x - 3]`),
  or a proof that the head can only meet the block in the six ways listed.
* Characterise the halting tails (all found so far contain `2, 1, 1, ..., 1, 2`) and compute the excursion
  halting probability exactly (the pruned DP in `py/roundmap.py`-style code is a start).

## Pages

- [`pages/holdouts/1RB1LF_1LC0RD_---1LA_0LA0RE_1LA1RA_1LB0LD/explainer.html`](../../pages/holdouts/1RB1LF_1LC0RD_---1LA_0LA0RE_1LA1RA_1LB0LD/explainer.html)
- [`pages/holdouts/1RB1LF_1LC0RD_---1LA_0LA0RE_1LA1RA_1LB0LD/proof-status.html`](../../pages/holdouts/1RB1LF_1LC0RD_---1LA_0LA0RE_1LA1RA_1LB0LD/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LF_1LC0RD_---1LA_0LA0RE_1LA1RA_1LB0LD/lean/check.sh   # about 2 minutes
python3 holdouts/1RB1LF_1LC0RD_---1LA_0LA0RE_1LA1RA_1LB0LD/py/zonemap.py check 500
python3 holdouts/1RB1LF_1LC0RD_---1LA_0LA0RE_1LA1RA_1LB0LD/py/zonemap.py orbit 100000
python3 holdouts/1RB1LF_1LC0RD_---1LA_0LA0RE_1LA1RA_1LB0LD/py/roundmap.py check 22
```
