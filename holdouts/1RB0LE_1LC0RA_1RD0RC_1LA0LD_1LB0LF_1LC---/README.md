# 1RB0LE_1LC0RA_1RD0RC_1LA0LD_1LB0LF_1LC---

bbchallenge id 69718, group G08. Whether it halts from blank tape is **open**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LE |
| B | 1LC | 0RA |
| C | 1RD | 0RC |
| D | 1LA | 0LD |
| E | 1LB | 0LF |
| F | 1LC | --- |

## What it does

A two-sided bouncer. At the left end the tape is a mix of runs of the word `001011` and short blocks like
`000 10 11 0 11 0 11`; at the right end it is stretches of `1010…` separated by `00`. C erases blocks of 1s going
right and D erases them going left; the rest of each sweep is irregular, and the mixture of words shows no order.

The machine halts only when F reads a 1; F is entered from E reading a 1, so `1 E> 1` halts, and `1 1 A> 1`,
`1 1 1 D> 0`, `1 1 C> 0 0` lead there.

## What is proved, and where

- `lean/Blank.lean` (generated): the halting configurations; no halt in 10⁴ steps (kernel) and 10⁷ (`native_decide`).
- `lean/Rules.lean` (kernel, written by `py/rules.py`): `erase_C`, `erase_D` and the halting situations.
- `c/visits.c` (trusted, our code): in the first 2·10⁸ steps the machine is in state F 111,044 times, always on a 0.

## What is open, next steps

The question itself; no macro structure is known.

**Later**: set aside after the first pass.

## Deciders tried (F11, 13 November 2026)

None closes. Each reaches a halting configuration in its abstraction, which says nothing about halting.

- n-gram CPS (`tools/c/ngramcps.c`), equal widths on both sides: a halting local configuration is reached with plain up to width 18, history 1 up to width 20, history 2 up to width 16, history 3 up to width 18, LRU history up to width 6 (larger widths ran out of the 150 s or 60 million configuration budget).
- n-gram CPS with every cell tagged by its position mod p: fails for p = 2 up to width 16, p = 3 up to width 16, p = 4 up to width 16, p = 6 up to width 20.
- n-gram CPS where each side also carries the state of a small automaton that has read that side from the far end (every automaton with up to 3 states on both sides, or 4 states on one side), with position mod 1..4 and widths 4, 6, 8: no closed set without a halt in all 120 parameter sets.
- Run-length windows (the K nearest runs of equal macro cells on each side, run lengths kept exactly below T and mod M above): fails for all 72 parameter sets (cells of 1 to 4 bits, K = 2, 4, 6, T = 2, 4, M = 1, 2, 4).
- Two-automaton closed tape language by SAT (a deterministic automaton reading each side inward, n states each, CaDiCaL): no solution for n = 2..7; n = 8 not finished in 150 s.

## Where a halt can come from

`lean/Route.lean` (kernel, written by `py/route.py`): `halt_route`, two steps before any halt the machine is in one
of: A with 1 two left, 1 left, 1 under the head.

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LE_1LC0RA_1RD0RC_1LA0LD_1LB0LF_1LC---/lean/check.sh
python3 holdouts/1RB0LE_1LC0RA_1RD0RC_1LA0LD_1LB0LF_1LC---/py/rules.py     # rewrites lean/Rules.lean
python3 holdouts/1RB0LE_1LC0RA_1RD0RC_1LA0LD_1LB0LF_1LC---/py/turns.py 3e6 50
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0RF_1RC0LE_1LD0LC_1RE0RD_1LB0RA_1RC---`](../1RB0RF_1RC0LE_1LD0LC_1RE0RD_1LB0RA_1RC---/README.md): rename A→E, B→B, C→C, D→D, E→A, F→F and exchange left and right; it is this table started in state E, in a mirror

<!-- end of related machines -->
