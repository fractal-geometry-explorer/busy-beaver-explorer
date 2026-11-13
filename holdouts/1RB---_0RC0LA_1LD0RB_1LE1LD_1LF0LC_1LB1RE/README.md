# 1RB---_0RC0LA_1LD0RB_1LE1LD_1LF0LC_1LB1RE

bbchallenge id 24506, group G08. Whether it halts from blank tape is **open**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | --- |
| B | 0RC | 0LA |
| C | 1LD | 0RB |
| D | 1LE | 1LD |
| E | 1LF | 0LC |
| F | 1LB | 1RE |

## What it does

A two-sided bouncer that keeps its tape in two encodings of one list of numbers j₁, j₂, …:

- at the **left end** the tape is *dense*: blocks `1^(4j+3)` separated by single 0s;
- at the **right end** it is *sparse*: the words `0101` and `0001`.

The rightward pass is a straight translation: C walks right and turns each `1^(4j+3) 0` into `(1010)^j 1000`, the
same number of cells (`pass_block`). The leftward trip is a zig-zag that rebuilds dense blocks, but the list is
scrambled on each round trip, and a few cells are added at each end. It shares states A, B, C (and so this pass)
with `1RB---_0RC0LA_1LD0RB_1LE0LB_1LF0LC_1LB1RE`, analysed in its own folder; only D differs.

The machine halts only when A reads a 1, which happens exactly after `A> 0 1` or `1 B> 1` (`halt_A`, `halt_B`).

## What is proved, and where

- `lean/Blank.lean` (generated): the halting configurations; no halt in 10⁴ steps (kernel) and 10⁷ (`native_decide`).
- `lean/Rules.lean` (kernel, written by `py/rules.py`): the rightward pass over any dense block (`pass_block`,
  `pass_pair`, `pass_end`, and `pass_b` seen from B) and the two halting situations (`halt_A`, `halt_B`).
- `py/turns.py` (heuristic, our code): the tape at every turn. In the first 5·10⁶ steps, 303,706 of the 306,037
  blocks strictly inside the dense tapes have length 4j+3.
- `c/visits.c` (trusted, our code): in the first 2·10⁸ steps the machine is in state A 23,410,519 times, always on a 0.

## What is open, next steps

The question itself. The content behaves like a cellular automaton; window closed tape languages (K ≤ 7, tried
for the whole group) and NGramCPS (n ≤ 10, tried here) still allow a halt. Next: write the leftward zig-zag as a
transducer on the sparse words and look for a regular invariant of the composed map that excludes `A> 0 1`.

**Later**: unlikely to yield to a structural proof without a new idea; set aside after the first pass.

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB---_0RC0LA_1LD0RB_1LE1LD_1LF0LC_1LB1RE/lean/check.sh
python3 holdouts/1RB---_0RC0LA_1LD0RB_1LE1LD_1LF0LC_1LB1RE/py/rules.py     # rewrites lean/Rules.lean
python3 holdouts/1RB---_0RC0LA_1LD0RB_1LE1LD_1LF0LC_1LB1RE/py/turns.py 5e6 100   # every 100th turn of the first 5·10⁶ steps
```
