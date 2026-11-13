# 1RB0LE_1RC0RE_1RD0RA_1RE1LC_0LA0RF_1LE---

bbchallenge id 48565, group G08. Whether it halts from blank tape is **open**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LE |
| B | 1RC | 0RE |
| C | 1RD | 0RA |
| D | 1RE | 1LC |
| E | 0LA | 0RF |
| F | 1LE | --- |

## What it does

The mirror image of the dense/sparse translators (like `1RB---_0RC0LA_1LD0RB_1LE1LD_1LF0LC_1LB1RE`): at the right
end the tape is dense, blocks `1^(4j+3)` separated by single 0s; at the left end it is sparse, the words `01`,
`0001`, `00`. Going left, E with a 0 ahead turns each `11` into `10` (`left_E`); going right, A turns each `0101`
into `1110` (`right_A`). The list of block lengths is scrambled on every round trip.

The machine halts only when F reads a 1: `E> 1 1` halts at once, `1 F> 0`, `B> 1 1 1` and `D> 0 1 1` after two
steps.

## What is proved, and where

- `lean/Blank.lean` (generated): the halting configurations; no halt in 10⁴ steps (kernel) and 10⁷ (`native_decide`).
- `lean/Rules.lean` (kernel, written by `py/rules.py`): `left_E`, `right_A` and the halting situations.
- `py/turns.py` (heuristic): in the first 5·10⁶ steps, 273,318 of the 275,315 blocks strictly inside the dense
  tapes have length 4j+3.
- `c/visits.c` (trusted, our code): in the first 2·10⁸ steps the machine is in state F 22,449,902 times, always on a 0.

## What is open, next steps

The question itself, as for the whole dense/sparse family.

**Later**: set aside after the first pass.

## Where a halt can come from

`lean/Route.lean` (kernel, written by `py/route.py`): `halt_route`, two steps before any halt the machine is in one
of: B with 1 under the head, 1 right, 1 two right; D with 0 under the head, 1 right, 1 two right; F with 1 left, 0 under the head.

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LE_1RC0RE_1RD0RA_1RE1LC_0LA0RF_1LE---/lean/check.sh
python3 holdouts/1RB0LE_1RC0RE_1RD0RA_1RE1LC_0LA0RF_1LE---/py/rules.py     # rewrites lean/Rules.lean
python3 holdouts/1RB0LE_1RC0RE_1RD0RA_1RE1LC_0LA0RF_1LE---/py/turns.py 5e6 100
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB---_0RC0LA_1LD0RB_1LE0LB_1LF0LC_1LB1RE`](../1RB---_0RC0LA_1LD0RB_1LE0LB_1LF0LC_1LB1RE/README.md): rename A→C, B→D, C→E, D→F, E→B, F→A and exchange left and right; it is this table started in state F, in a mirror
- [`1RB0RD_1RC0RE_1RD1LB_0LE0RF_1RA0LD_1LD---`](../1RB0RD_1RC0RE_1RD1LB_0LE0RF_1RA0LD_1LD---/README.md): rename A→E, B→A, C→B, D→C, E→D, F→F; it is this table started in state B

**Same tapes at another pace (observed, not proved).** Leave the states aside and compare only the tape and the place of the head. Then a large part of the first 10^7 configurations of this machine are configurations of the machines below, in the same order and up to the end of the run. The steps at which they occur differ, the tables are not renamings of each other, and equal tapes with different states may be continued differently, so this does not tie the halting questions together.

- [`1RB1LE_0LC0RF_1RD0LB_1RE1RD_1RA0RC_1LB---`](../1RB1LE_0LC0RF_1RD0LB_1RE1RD_1RA0RC_1LB---/README.md): 9,589,851 configurations, the last at step 10,000,000 here and step 9,589,854 there

<!-- end of related machines -->
