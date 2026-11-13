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

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB---_0RC0LA_1LD0RB_1LE0LB_1LF0LC_1LB1RE/lean/check.sh
python3 holdouts/1RB---_0RC0LA_1LD0RB_1LE0LB_1LF0LC_1LB1RE/py/route.py        # rewrites lean/Route.lean
python3 holdouts/1RB---_0RC0LA_1LD0RB_1LE0LB_1LF0LC_1LB1RE/py/rules.py     # rewrites lean/Rules.lean
python3 holdouts/1RB---_0RC0LA_1LD0RB_1LE0LB_1LF0LC_1LB1RE/py/forms.py 5e6 # the two forms along the run
```
