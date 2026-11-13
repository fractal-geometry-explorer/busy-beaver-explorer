# 1RB---_0RC0LA_1LD0RB_1LE0LB_1LF0LC_1LB1RE

bbchallenge id 55079, group G08 (two-sided square-root growth). Whether it halts from blank tape is **open**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | --- |
| B | 0RC | 0LA |
| C | 1LD | 0RB |
| D | 1LE | 0LB |
| E | 1LF | 0LC |
| F | 1LB | 1RE |

## What it does

A two-sided bouncer that keeps its tape in two encodings of one list of numbers j₁, j₂, …:

- at the **left end** the tape is *dense*: blocks `1^(4j+3)` separated by single 0s;
- at the **right end** it is *sparse*: the words `x = 0101` and `y = 0001`, block j written `x^j y`.

The rightward pass is a straight translation: C walks right and turns each `1^(4j+3) 0` into `(1010)^j 1000`
(read from the other side, `x^j y`), the same number of cells (`pass_block`). The leftward trip is a zig-zag: the
head eats one sparse word, runs right to the end of the dense block it is building and comes back. It does not
rebuild the same blocks: the list is scrambled on each round trip, like a carry rippling through it, and a few cells
are added at each end. Over many trips the list looks random (the space-time diagram is noise), and the width grows
like the square root of the step count (35,832 cells after 10⁹ steps).

The machine halts only when A reads a 1, which happens exactly after `A> 0 1` or `1 B> 1` (`halt_A`, `halt_B`).

## What is proved, and where

- `lean/Blank.lean` (generated): the halting configurations; no halt in 10⁴ steps (kernel) and 10⁷ (`native_decide`).
- `lean/Rules.lean` (kernel, written by `py/rules.py`): the rightward pass over any dense block (`pass_block`,
  `pass_pair`, `pass_end`) and the two halting situations (`halt_A`, `halt_B`).
- `lean/Route.lean` (kernel, written by `py/route.py`): `halt_route`, every configuration two steps before a
  halt is `A> 0 1`, `1 1 D> 1` or `1 1 F> 0`.
- `py/forms.py` (heuristic, our code): the dense/sparse forms at every turn of a run, and the lists j (`show`). In the
  first 5·10⁶ steps (464 round trips), 72,012 of the 72,345 blocks strictly inside the dense lists have length 4j+3
  (235 have 4j+1, 98 are even: made near the left end and carried along).

## What is open, next steps

The question itself. The content behaves like a cellular automaton; window closed tape languages (K ≤ 7, tried for
the whole group) and run-length languages with run lengths mod 4 (tried here, K ≤ 11 runs) still allow a halt.
Next: derive the leftward zig-zag as a transducer on the words x, y (it reads the sparse list right to left with a
small carry state) and look for a regular invariant of the composed map, i.e. an automaton on the list of j's that
is closed under one round trip and excludes `A> 0 1` / `1 B> 1`.

**Later**: this machine is unlikely to yield to a structural proof without a new idea; it was set aside after the
first pass.

## Deciders tried (F11, 13 November 2026)

None closes. Each reaches a halting configuration in its abstraction, which says nothing about halting.

- n-gram CPS (`tools/c/ngramcps.c`), equal widths on both sides: a halting local configuration is reached with plain up to width 24, history 1 up to width 24, history 2 up to width 24, history 3 up to width 24, LRU history up to width 7 (larger widths ran out of the 150 s or 60 million configuration budget).
- n-gram CPS with every cell tagged by its position mod p: fails for p = 2 up to width 20, p = 3 up to width 20, p = 4 up to width 16, p = 6 up to width 20.
- n-gram CPS where each side also carries the state of a small automaton that has read that side from the far end (every automaton with up to 3 states on both sides, or 4 states on one side), with position mod 1..4 and widths 4, 6, 8: no closed set without a halt in all 120 parameter sets.
- Run-length windows (the K nearest runs of equal macro cells on each side, run lengths kept exactly below T and mod M above): fails for all 72 parameter sets (cells of 1 to 4 bits, K = 2, 4, 6, T = 2, 4, M = 1, 2, 4).
- Two-automaton closed tape language by SAT (a deterministic automaton reading each side inward, n states each, CaDiCaL): no solution for n = 2..8; n = 9 not finished in 150 s.

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB---_0RC0LA_1LD0RB_1LE0LB_1LF0LC_1LB1RE/lean/check.sh
python3 holdouts/1RB---_0RC0LA_1LD0RB_1LE0LB_1LF0LC_1LB1RE/py/route.py        # rewrites lean/Route.lean
python3 holdouts/1RB---_0RC0LA_1LD0RB_1LE0LB_1LF0LC_1LB1RE/py/rules.py     # rewrites lean/Rules.lean
python3 holdouts/1RB---_0RC0LA_1LD0RB_1LE0LB_1LF0LC_1LB1RE/py/forms.py 5e6 # the two forms along the run
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0LE_1RC0RE_1RD0RA_1RE1LC_0LA0RF_1LE---`](../1RB0LE_1RC0RE_1RD0RA_1RE1LC_0LA0RF_1LE---/README.md): rename A→F, B→E, C→A, D→B, E→C, F→D and exchange left and right; it is this table started in state C, in a mirror
- [`1RB0RD_1RC0RE_1RD1LB_0LE0RF_1RA0LD_1LD---`](../1RB0RD_1RC0RE_1RD1LB_0LE0RF_1RA0LD_1LD---/README.md): rename A→F, B→D, C→E, D→A, E→B, F→C and exchange left and right; it is this table started in state D, in a mirror

**Same tapes at another pace (observed, not proved).** Leave the states aside and compare only the tape and the place of the head. Then a large part of the first 10^7 configurations of this machine are configurations of the machines below, in the same order and up to the end of the run. The steps at which they occur differ, the tables are not renamings of each other, and equal tapes with different states may be continued differently, so this does not tie the halting questions together.

- [`1RB---_0RC0LA_1LD0RB_1LE1LD_1LF0LC_1LB1RE`](../1RB---_0RC0LA_1LD0RB_1LE1LD_1LF0LC_1LB1RE/README.md): 9,588,057 configurations, the last at step 10,000,000 here and step 9,588,056 there

<!-- end of related machines -->
