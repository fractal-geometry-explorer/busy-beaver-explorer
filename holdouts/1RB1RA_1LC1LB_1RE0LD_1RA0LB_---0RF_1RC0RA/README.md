# 1RB1RA_1LC1LB_1RE0LD_1RA0LB_---0RF_1RC0RA

bbchallenge id 139325. A BB(6) holdout, group G10 (one side of the tape grows like the square root of the step count, the other more slowly).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RA |
| B | 1LC | 1LB |
| C | 1RE | 0LD |
| D | 1RA | 0LB |
| E | --- | 0RF |
| F | 1RC | 0RA |

Family: **unary blocks split in halves, Collatz-like**. Decision: **open**, now reduced in Lean to an explicit map on
lists of block lengths.

## What it does

The tape is always a list of blocks of 1s. Left of the head the blocks are separated by one `0`, right of it by
`00`. The head works through the blocks from left to right, one **pass** at a time. With the head in state E on the
first cell of a block `1^b`:

- every round trip inside the block removes two of its 1s and gives one to the block on its left and one to the
  block on its right (`l_round`: 2b + 3 steps for a block of b);
- **b odd** (b = 2j + 1): after j round trips one 1 is left. It becomes a new finished block `11`, and the head goes
  on to the next block, which has grown by j;
- **b even** (b = 2j + 2): after j round trips the head turns back. On the way to the left end every finished
  block loses a 1 and its separator `0` becomes `00` (a block of a single 1 merges its two neighbours instead);
  at the left end the next pass starts;
- **b = 0** (E reads 0): the machine **halts**.

One pass, from the run (steps 2,313 to 3,633; `E>` is the head on the first cell of the block after it):

```
1 E> 1^11 00 1^30 00 1^8                    11 = 2*5+1: 5 to each side, a block 11, go on
1^6 0 11 E> 1^35 00 1^8                     35 = 2*17+1
1^6 0 1^19 0 11 E> 1^25                     25 = 2*12+1: the last block; 12 ones start a new last block
1^6 0 1^19 0 1^14 0 11 E> 1^12              12 = 2*5+2: even, turn back
1^6 0 1^19 0 1^14 0 1^7 B> 0 1^8
B> 0 1^4 00 1^18 00 1^13 00 1^6 00 1^9      back at the left end: the next pass
```

### The map

Two kinds of configuration, each a list of numbers (`fs`: the blocks left of the head, nearest first; `rest`: the
blocks further right):

    e fs b rest  =  ... 0 1^f2 0 1^f1  E> 1^b 00 1^c 00 ...
    s fs m rest  =  ... 0 1^f2 0 1^f1  B> 0 1^m 00 ...

and the map G (c = first entry of `rest`, 0 if there is none; `inc j` adds j to the first entry of a list,
`inc j [] = [j]`):

| from | to |
|---|---|
| `e fs 0 rest` | halt |
| `e fs (2j+1) (c :: rest)` | `e (2 :: inc j fs) (c + j) rest` |
| `e fs (2j+2) (c :: rest)` | `s (inc j fs) (c + j + 3) rest` |
| `s (f+2 :: fs) m rest` | `s fs f (m+1 :: rest)` |
| `s (1 :: g :: fs) m rest` | `s fs (g + m + 3) rest` |
| `s (0 :: fs) m rest`, `s [] m rest` | `e (inc 1 fs) (m + 1) rest` |

Blank tape reaches `s [] 3 []` (`B> 0 111`) after 8 steps.

## Halting

The blocks right of the head are never empty, so `e fs 0 rest` can only come from `e fs 1 []`: the machine halts
exactly when a pass gets through every block (all of them odd when the head arrives) to the right end of the tape
**and the last block is `1^(2^k − 1)`**. That block is halved, 2^k − 1 → 2^(k−1) − 1 → ... → 1 → 0, and E reads 0
(`last_block_halts`). Any other last block ends in an even number and the head turns back.

So halting is a question about the binary digits of one number at the moments a pass reaches the right end: a
Collatz-like question. Counting: a pass reaches the right end about once in 140 applications of G (7.1 million times
in the first 10^9), and the last block is then a large part of the tape (median: 0.6 of all the 1s). If these
numbers behaved like random ones, the chance of hitting 2^k − 1 would add up to an expected 0.02 to 0.03 halts each
time the tape doubles, for ever: about one expected halt over the run so far, so seeing none is unremarkable, and
a halt is neither excluded nor likely soon (a heuristic). The closest call: at application 219,298 the last block
was 49,151 = `1011111111111111` in binary.

## What is proved (Lean, kernel unless said otherwise)

- `lean/Rules.lean`, `lean/Leaves.lean` (written by `py/rules.py`, `py/leaves.py` with `bbtools.symtm.prove`): the
  block crossings and the eight leaf rules (one round trip, the two ends of a block, the steps of the way back), for
  all block lengths and any tape around them.
- `lean/Map.lean` (by hand):
  - `rounds`: j round trips, by induction;
  - `G_sem`: for every configuration x of the two kinds, if `G x = some y` the machine goes from x to y in at
    least one step, and if `G x = none` it halts from x;
  - **`halts_iff : HaltsFromBlank ↔ ∃ n, orbitFrom (.s [] 3 []) n = none`**: the machine halts from blank tape if and
    only if the orbit of `s [] 3 []` under G reaches a halting configuration. Nothing is assumed;
  - `G_none_iff`: the halting configurations of G are exactly `e fs 0 rest`;
  - `last_block_halts`: from `e fs (2^(k+1) − 1) []` the orbit halts after k + 2 applications.
- `lean/Orbit.lean`: the orbit does not halt in its first 20,000 applications (kernel) and its first 10^7
  applications (`native_decide`); by the step counts of `c/gs.c` the latter is 5.3·10^17 steps of the machine.
- `lean/Blank.lean` (generated): the halting configurations; no halt in 10^4 steps (kernel), 10^7 (`native_decide`).

## Computed (trusted, not proved)

- `c/gs.c` runs the same map with exact step counts (128-bit): **no halt in the first 2·10^10 applications of G,
  which is 2,646,836,962,671,316,587,651,578,601 steps of the machine**; the tape then holds 8,670,747,376 ones in about 5 to 40 blocks. The step counts are
  checked against a direct simulation (`py/gmap.py check`).
- `py/gmap.py check 1500`: the first 1,500 configurations of the orbit agree with a direct run of the machine cell
  by cell, at the steps the map says (5.5·10^6 steps).

## Open

Whether the orbit ever reaches a pass that ends on a last block `1^(2^k − 1)`. No invariant is known that would
exclude it (the 2-adic valuations of "last block + 1" at the right end are distributed geometrically, like those of
random numbers), and the run so far has not found one.

## Reproduce

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RA_1LC1LB_1RE0LD_1RA0LB_---0RF_1RC0RA/lean/check.sh
cd holdouts/1RB1RA_1LC1LB_1RE0LD_1RA0LB_---0RF_1RC0RA
python3 py/rules.py | diff - lean/Rules.lean && python3 py/leaves.py | diff - lean/Leaves.lean   # generated files are current
python3 py/gmap.py check 1500          # the map against the machine
python3 py/gmap.py run 40              # the orbit, with step counts
gcc -O2 -o gs c/gs.c && ./gs 1e10      # 45 s; 1e12 takes about 80 minutes
```

## Pages

- [`pages/holdouts/1RB1RA_1LC1LB_1RE0LD_1RA0LB_---0RF_1RC0RA/explainer.html`](../../pages/holdouts/1RB1RA_1LC1LB_1RE0LD_1RA0LB_---0RF_1RC0RA/explainer.html)
- [`pages/holdouts/1RB1RA_1LC1LB_1RE0LD_1RA0LB_---0RF_1RC0RA/proof-status.html`](../../pages/holdouts/1RB1RA_1LC1LB_1RE0LD_1RA0LB_---0RF_1RC0RA/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RA_1LC1LB_1RE0LD_1RA0LB_---0RF_1RC0RA/lean/check.sh
```
