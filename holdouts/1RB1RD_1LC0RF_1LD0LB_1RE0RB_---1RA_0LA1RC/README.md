# 1RB1RD_1LC0RF_1LD0LB_1RE0RB_---1RA_0LA1RC

bbchallenge id 92170. One of the six-state holdouts whose halting from blank tape is open (group G07).
Family: **nested counters with growth about 15/7 (levels of ones and 7-cell words), halting only at the right edge (Lean)**. Decision: **open**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RD |
| B | 1LC | 0RF |
| C | 1LD | 0LB |
| D | 1RE | 0RB |
| E | --- | 1RA |
| F | 0LA | 1RC |

## What it does

With `a = 1111110`, the tape is a list of levels `1^X a 00 a^Y` (plus a few short words). On the last level, every 8
visits of the right end (state C):  `1^X a 00 a^Y  ->  1^(X+15) a 00 a^(Y-1)`  (step 1.589e9: X = 30874, 30889, ...,
31009 as Y runs from 9 to 0). When Y = 0 the head rebuilds runs of ones into runs of words (about one word per 7 ones)
and another level becomes active (e.g. `1^54794 a 00 a^10924` at step 9.5e9). Sizes grow by about 15/7 per round,
with remainders mod 7 steering the rebuilds: a multi-counter Collatz-like system.

Sample (step 7,293,164,582, the 50,000th visit of the right end in C, 133,715 cells):

    11111 000 a 1111 a 00 1^39759 a 00 a^7934 1111 a 00 1^34254 a 00 a^584 11111 0 11111 0000 10

### Shift rules (proved)

`lean/Rules.lean` (written by `py/rules.py` with `bbtools.symtm.prove`, checked by the kernel) proves the four moves
the head is made of, for every n:

- `walk`: C walks left over a run of ones, five steps a cell, changing nothing;
- `words_left`: C walks left through a block `(0111111)^(n+1)`: every 0 moves one cell to the right;
- `glider`: the three cells `110` with B on the first pass a block `a^n` to the right and leave it unchanged;
- `ones_to_words`: E, moving right, turns a run `1^(7+6n)` into `1011 11 (101111)^n` and stands on its last 1.

The level cycle `1^(x+1) 000 a^(y+2) 11111 0 1111 0 1^12 B>  ->  1^(x+16) 000 a^(y+1)` (same tail, 144y + 598
steps) is a chain of 21 such pieces; its Lean term is too heavy for one kernel theorem, so it is proved by the
symbolic replay below, not in Lean.

### An exact accelerated simulator

`py/ws.py` keeps each side of the head as a stack of entries `[len, mult]` (mult words `1^len 0`), with exact big
integers, and moves a whole run of ones or a whole block of equal words at once (the moves above, found and cached
per (state, word) by a bounded direct run). `py/cyc.py` adds **cycle jumps**: when the same shape of the stacks comes
back three times with the numbers changing linearly, it replays the stretch once more with the changing numbers
replaced by variables (`py/lin.py`: affine forms `b + m*y`, y >= 0; any comparison that is not decided for all y, or
any halt, makes the attempt fail) and, if the replay closes, applies the cycle k times at once, with k the largest
count for which every decreasing number stays above its base. So every jump is proved for all values of its
variables before it is used; about 4,700 such rules appear.

Checks: `py/test_ws.py` compares `ws.Sim` with a cell-by-cell run at all 431,269 macro configurations of the first
2·10^7 steps (0 mismatches); `py/test_cyc.py` compares the accelerated run with the plain `ws.Sim` run at every
sample point the accelerated run stops at, up to 10^10 steps (7,807 points, all equal; the 7,808th lies past the
plain run's end).

### How far it was run

`py/far.py 1RB1RD_1LC0RF_1LD0LB_1RE0RB_---1RA_0LA1RC 240` (four minutes): **no halt in 2^8269 steps** (the step count has
8,270 bits; far.py prints the bit length; about 10^2489), with 181 million macro steps and 81,000 cycle jumps; the tape is then 14 to 24 entries
of the stacks (levels), its numbers of about 8,000 bits each. A longer run (`far.py ... 570`, 9.5 minutes) reached **2^17783 steps** (a step count of 17,784 bits, about 10^5353; 397 million macro steps, 180,000
jumps, 7,200 cycle rules) without a halt.

The levels behave as described: the main jumps are `X + 15, Y - 1` (144Y + 5206 steps), `X + 15, Y - 3, Z + 2`,
`X + 5, Y - 2, Z + 1` and `X + 5, Z + 1, Y - 2` on the active level and its neighbour, and every few levels a run of
ones is rebuilt into words.

## Where it can halt

The halting transition is E0, reached only as D0 -> 1RE. A closed tape language from windows of 4 cells
(`lean/EdgeCert.lean`, checked by `decide` in `lean/Edge.lean`) proves that **the machine halts from blank tape
exactly when E steps onto the blank region past the right end of the tape** (`halts_iff_edge`), that is, when D
reads the blank cell just right of the tape. With windows of 7 cells (`python3 -m bbtools.ctl ... 7`, closed, 22,365
abstract configurations; not in Lean) the halt also needs the 7 cells left of E to be ones: the tape must end in a
run of at least six ones that A reads to its end (A1 -> 1RD, D0 -> 1RE, E0 halts).

**The last run decides, by its length mod 6.** Let the head enter the last run of ones of the tape, `1^r` followed
by blank, moving right. A direct check for r <= 300 (`py/lastrun.py`; for E, `ones_to_words` extends it to all r) gives: in state
E it halts iff r ≡ 2 (mod 6), in state A iff r ≡ 1 (mod 6); in every other state, and for the other remainders, the
head turns back left without a halt. In the run (all macro configurations of the first 2^38 (2.7·10^11) steps of `ws.Sim` and
of the accelerated run to 2^4025 steps outside its jumps) the head, moving right inside the last run with r ones
still ahead, is never in state A with r ≡ 1 or in E with r ≡ 2; r is at most 15, and the head always reaches the
blank past the end in state B. The last run is short (`... 11111 0 1111 0 1^12` most of the time, also `1^13`,
`1^11`, `1^6`, `1`), so a halt needs the head to come to that short tail in the wrong phase, which is what the
remainders of the rebuilds would have to arrange.

## Status

Open.

- **Kernel:** `step_none_iff`, `blank_runs_kernel` (`lean/Blank.lean`); `halts_iff_edge` (`lean/Edge.lean`);
  `walk`, `words_left`, `glider`, `ones_to_words` (`lean/Rules.lean`). **native_decide:** `blank_runs_native`
  (10^7 steps).
- **Trusted:** no halt in 1.2·10^10 steps (`tools/c`, direct run); **no halt in 2^17783 steps** (2^8269 in four minutes) with the accelerated
  simulator (`py/ws.py`, `py/cyc.py`: exact integers, every cycle jump proved by a symbolic replay before use; checked
  against direct simulation as above). The last-run criterion (mod 6): a finite check for r <= 300, for E extended to all r by `ones_to_words`.
- **Heuristic:** the level cycle as a closed formula, the rebuild rule (about 7 ones per word, growth 15/7), and the
  observation that the head never comes to the last run in a halting phase.

## Next steps

Write the level map as one exact function: the shape of the stacks at the start of each level (a few dozen shapes
appear) and the affine map of its numbers, with the case split by the remainders mod 7 (and mod 6 for the tail); then
show (or refute) that the tail `5 4 12` is always entered in a non-halting phase. The accelerator already lists the
proved cycle rules (`Acc.rules`), so the map can be read off them; proving it in Lean needs the level cycle split into
kernel-sized pieces (the 21-piece chain was too heavy as one term).

## Pages

- [`pages/holdouts/1RB1RD_1LC0RF_1LD0LB_1RE0RB_---1RA_0LA1RC/explainer.html`](../../pages/holdouts/1RB1RD_1LC0RF_1LD0LB_1RE0RB_---1RA_0LA1RC/explainer.html)
- [`pages/holdouts/1RB1RD_1LC0RF_1LD0LB_1RE0RB_---1RA_0LA1RC/proof-status.html`](../../pages/holdouts/1RB1RD_1LC0RF_1LD0LB_1RE0RB_---1RA_0LA1RC/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RD_1LC0RF_1LD0LB_1RE0RB_---1RA_0LA1RC/lean/check.sh
(cd tools/py && python3 -m bbtools.ctl 1RB1RD_1LC0RF_1LD0LB_1RE0RB_---1RA_0LA1RC 4 lean H92170 Blank) | diff - holdouts/1RB1RD_1LC0RF_1LD0LB_1RE0RB_---1RA_0LA1RC/lean/EdgeCert.lean
cd holdouts/1RB1RD_1LC0RF_1LD0LB_1RE0RB_---1RA_0LA1RC/py
python3 rules.py | diff - ../lean/Rules.lean
python3 test_ws.py 1RB1RD_1LC0RF_1LD0LB_1RE0RB_---1RA_0LA1RC 2e7       # ws.Sim against a cell-by-cell run
python3 test_cyc.py 1RB1RD_1LC0RF_1LD0LB_1RE0RB_---1RA_0LA1RC 1e10     # accelerated against plain ws.Sim
python3 far.py 1RB1RD_1LC0RF_1LD0LB_1RE0RB_---1RA_0LA1RC 240           # the accelerated run, 4 minutes
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0RE_1LC0LE_---1LD_1LE1LB_1RA0LF_0RD1LA`](../1RB0RE_1LC0LE_---1LD_1LE1LB_1RA0LF_0RD1LA/README.md): rename A→D, B→E, C→A, D→B, E→C, F→F and exchange left and right; it is this table started in state C, in a mirror

<!-- end of related machines -->
