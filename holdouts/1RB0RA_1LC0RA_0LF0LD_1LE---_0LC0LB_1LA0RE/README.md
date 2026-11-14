# 1RB0RA_1LC0RA_0LF0LD_1LE---_0LC0LB_1LA0RE

bbchallenge id 142609, a six-state holdout of group G05 (growth class fixed/sqrt). **Open.** The machine is a
*sweep counter*: the tape is a row of blocks of `10`s, every sweep adds one 1 to the youngest block (which therefore
counts the sweeps) and makes one small change further left, at a place set by the binary digits of the sweep number,
like a binary counter whose digits are pairs of blocks. Lean proves ten whole-sweep rules for all block lengths and that
the run reaches them; no halt in 1.03·10^11 (103,079,215,104) steps.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RA |
| B | 1LC | 0RA |
| C | 0LF | 0LD |
| D | 1LE | --- |
| E | 0LC | 0LB |
| F | 1LA | 0RE |

## What it does

**The tape.** At the start of every sweep the head is in state B on the blank cell right of the tape and the tape is

    0^inf (10)^n1 0 (10)^n2 0 ... 0 (10)^nk 1 B>0

blocks of `10`s, each followed by one extra 0, the last ending in a bare 1. The *count* of a block is its number of
1s (n_i, and n_k + 1 for the last). Example (step 12,451): counts 4 2 3 4 0 5 27 12 4 26 (an empty block is two extra
0s side by side).

**The head's moves.** In state C the head runs left over `10`s, shifting every 1 one cell left (C, D, E, B in turn, four
steps per `1010`); in A/B it runs right shifting them back (four steps per `1010`); in the region it works on it
zigzags left, crossing a `1010` in 12 steps (in deeper sweeps 28, 60, ... steps: the zigzag nests).

**One sweep** runs left over the last block, works through a few more blocks and returns. What it does depends only on
the parities of the counts it meets (E even, O odd), read from the right. Proved in Lean for all values (counts written
last first; an inner count is 2y+4 or 2y+5 with y >= 0, the last 2c+5 or 2c+6):

| parities (last \| inner, nearest first) | change of the counts | steps | Lean |
|---|---|---|---|
| E \| O E, E \| O O | +1, +1, -1 | 8c + 16y1 + 76 | `sweep_E_OE`, `sweep_E_OO` |
| E \| E E E, E \| E E O | +1, -1, +2, -1 | 8c + 16y1 + 16y2 + 104 | `sweep_E_EEE`, `sweep_E_EEO` |
| E \| E O E E, E \| E O E O | +1, -1, 0, +2, -1 | 8c + 16(y1+y2+y3) + 148 | `sweep_E_EOEE`, `sweep_E_EOEO` |
| O \| E E E E, O \| E E E O | +1, 0, 0, +1, -1 | 8c + 16y1 + 32y2 + 16y3 + 168 | `sweep_O_EEEE`, `sweep_O_EEEO` |
| O \| E O O E | +1, 0, 0, +1, -1 | 8c + 16y1 + 32y2 + 16y3 + 200 | `sweep_O_EOOE` |
| O \| E E O E E | +1, 0, 0, -1, +2, -1 | 8c + 16y1 + 32y2 + 16y3 + 16y4 + 212 | `sweep_O_EEOEE` |

A symbolic search over all parity patterns of up to seven blocks (`bbtools.symtm`, script in `py/gen_rules.py`'s
style) gives the same two shapes at every depth: a *move* (one block +1, its left neighbour -1) or a *split* (one
block -1, a block further left +2 and its left neighbour -1, with odd blocks in between skipped).

**The emergent behaviour: a binary counter of block pairs.** Number the blocks from the right, the last being block 0,
and let n be the sweep number (the count of the last block). In the 31,158 sweeps of the first 2·10^9 steps, apart
from a handful where the number of blocks changes, every sweep was a move M_k (block 2k+1 +1, block 2k+2 -1) or a split
S_k,j (block 2k+1 -1, block 2k+2+j +2, block 2k+3+j -1), where **k is the number of trailing zeros of n in binary**:

| n | change |
|---|---|
| 1 mod 4 | M_0 |
| 3 mod 4 | S_0,j |
| 2 mod 4 | M_1 or S_1,j |
| 4 mod 8 | M_2 or S_2,j |
| 2^k · odd | M_k or S_k,j |

(frequencies 7789 M_0, 3894 S_0,0, 3893 M_1, 1948 S_1,0, 1946 S_0,1, 1946 M_2, ...). So the pair of blocks 2k+1, 2k+2
is the k-th binary digit of the counter, touched half as often as the pair before; a split hands a 1 further left like
a carry, and the near-right blocks cycle through a few values (3/4, 12-14, 23-27, ...). When a carry gets to the left
end, a few new blocks of 3s and 4s appear there; the sweeps that reached the leftmost 1 were 2, 3, 4, 6, 7, 8, 10, 12, 16, 32, 48, 64, 160, 192, 448, 1472, 1984, 2496, 3008, 3520, 11712, 28096, 60864 and 126400 (none more up to sweep 226,517). The number of
blocks grows very slowly (22 after 4.6·10^6 steps, 38 after 3.2·10^10).

**Where it can halt.** The only halting transition is D1: C, running left, erases a 1 and moves onto another 1. Over
runs of `10` this never happens and no sweep rule above does it. A halt needs a sweep over short blocks (counts below
4, including empty blocks) or a carry arriving at the left end to put two 1s side by side in front of C.

## Status and evidence

**Lean, kernel** (`lean/Rules.lean`, written by `py/gen_rules.py` with `bbtools.symtm.prove`): the ten whole-sweep
rules of the table, for every value of the counts and every tape left of the blocks involved.

**Lean, `native_decide`** (`lean/Reach.lean`, written by `py/gen_reach.py`): `reach_2183`, from blank tape the machine
reaches the sweep start with counts 27, 12, 4, 10 after 2,183 steps; `sweep_2367`, the next sweep is `sweep_E_EEO`.
`lean/Blank.lean`: `step_none_iff` (halting = D1), no halt in 10^4 (kernel) and 10^7 (`native_decide`) steps.

**Computed (trusted)**: `c/sweeps.c` runs 1.03·10^11 (103,079,215,104) steps (226,517 sweeps) without a halt, printing the sweeps that reach the
leftmost 1.

**Heuristic**: the binary-counter description above (checked on 31,158 sweeps, not proved for all).

**Open**: whether the machine halts. A proof of non-halting would need (1) the sweep rules for every parity pattern
(an induction over the skipped blocks, the same two shapes at every depth), (2) the rules for short blocks and for the
left end, and (3) an invariant showing that the counter never produces a short-block pattern that halts.

## Reproduce

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RA_1LC0RA_0LF0LD_1LE---_0LC0LB_1LA0RE/lean/check.sh
python3 holdouts/1RB0RA_1LC0RA_0LF0LD_1LE---_0LC0LB_1LA0RE/py/gen_rules.py      # rewrites lean/Rules.lean
python3 holdouts/1RB0RA_1LC0RA_0LF0LD_1LE---_0LC0LB_1LA0RE/py/gen_reach.py      # rewrites lean/Reach.lean
gcc -O2 -o sweeps holdouts/1RB0RA_1LC0RA_0LF0LD_1LE---_0LC0LB_1LA0RE/c/sweeps.c && ./sweeps 103079215104
```

## Layout

| path | what it is |
|---|---|
| `lean/Machine.lean`, `lean/Blank.lean` | the machine and bounded runs (generated) |
| `lean/Rules.lean` | ten whole-sweep rules (generated by `py/gen_rules.py`) |
| `lean/Reach.lean` | blank tape to the first generic sweep (generated by `py/gen_reach.py`) |
| `c/sweeps.c` | plain simulator counting sweeps, reporting left-end sweeps |

## Deciders tried (F11, 13 November 2026)

None closes. Each reaches a halting configuration in its abstraction, which says nothing about halting.

- n-gram CPS (`tools/c/ngramcps.c`), equal widths on both sides: a halting local configuration is reached with plain up to width 24, history 1 up to width 20, history 2 up to width 24, history 3 up to width 22, LRU history up to width 22 (larger widths ran out of the 150 s or 60 million configuration budget).
- n-gram CPS with every cell tagged by its position mod p: fails for p = 2 up to width 20, p = 3 up to width 20, p = 4 up to width 20, p = 6 up to width 20.
- n-gram CPS where each side also carries the state of a small automaton that has read that side from the far end (every automaton with up to 3 states on both sides, or 4 states on one side), with position mod 1..4 and widths 4, 6, 8: no closed set without a halt in all 120 parameter sets.
- Run-length windows (the K nearest runs of equal macro cells on each side, run lengths kept exactly below T and mod M above): fails for all 72 parameter sets (cells of 1 to 4 bits, K = 2, 4, 6, T = 2, 4, M = 1, 2, 4).
- Two-automaton closed tape language by SAT (a deterministic automaton reading each side inward, n states each, CaDiCaL): no solution for n = 2..7; n = 8 not finished in 150 s.

## Where a halt can come from

`lean/Route.lean` (kernel, written by `py/route.py`): `halt_route`, two steps before any halt the machine is in one
of: B with 1 two left, 1 left, 0 under the head; E with 1 two left, 1 left, 0 under the head.

## Pages

- [`pages/holdouts/1RB0RA_1LC0RA_0LF0LD_1LE---_0LC0LB_1LA0RE/explainer.html`](../../pages/holdouts/1RB0RA_1LC0RA_0LF0LD_1LE---_0LC0LB_1LA0RE/explainer.html)
- [`pages/holdouts/1RB0RA_1LC0RA_0LF0LD_1LE---_0LC0LB_1LA0RE/proof-status.html`](../../pages/holdouts/1RB0RA_1LC0RA_0LF0LD_1LE---_0LC0LB_1LA0RE/proof-status.html)

## For later

Make the counter exact: describe the sweep as a finite transducer on the parity sequence of the blocks (the symbolic
search in the style of `py/gen_rules.py` already shows the two shapes at every depth), prove the families with an
induction over the skipped odd blocks, add the short-block and left-end cases, and then look for an invariant of the
block pairs (they cycle through few values near the right end) that excludes two adjacent 1s in front of C.

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB---_0RC0RF_0RD0RA_1RE0LB_1LF0LE_1RC0LE`](../1RB---_0RC0RF_0RD0RA_1RE0LB_1LF0LE_1RC0LE/README.md): rename A→E, B→F, C→C, D→A, E→B, F→D and exchange left and right; it is this table started in state D, in a mirror

<!-- end of related machines -->
