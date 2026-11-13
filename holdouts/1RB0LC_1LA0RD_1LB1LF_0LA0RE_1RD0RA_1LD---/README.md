# 1RB0LC_1LA0RD_1LB1LF_0LA0RE_1RD0RA_1LD---

bbchallenge id 105641. A BB(6) holdout, group G10 (one side of the tape grows like the square root of the step count, the other more slowly). Analysed by hand from the generated folder.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LC |
| B | 1LA | 0RD |
| C | 1LB | 1LF |
| D | 0LA | 0RE |
| E | 1RD | 0RA |
| F | 1LD | --- |

## What it does

**A period-3 background.** After a sweep to the right the tape repeats `100`; a sweep to the left turns each
`100` into `110` (`001` into `101`, `010` into `011`). The leftward sweeps are shift rules, proved in
`lean/Rules.lean`.

**Walls and groups.** The phase of the repetition slips at walls `000`. The right end at step 1,925,758,219
(width 50,930):

```
(100)^117 (010)^115 (001)^115 000 (100)^127 (010)^111 (001)^111 000 (100)^111 (010)^111 (001)^111 000
  ... 000 (100)^7 (010)^7 (001)^7 000 (100)^7 (010)^5 (001)^3 000 (100)^5 (010)^5 (001)^5 000
  (100)^7 (0100100100)^4 1 (0010)^3 0
```

There are 96 groups `(100)^a (010)^b (001)^c` with a ≈ b ≈ c, and the group sizes form a staircase falling from
about 115 to about 5, by about 2 per group with plateaus. Earlier the steps were larger (domain lengths 206, 194,
182, 170, ... at step 2.2·10^8).

## Halting

The only halting transition is F1, reached as `1 C>1` (C reads 1, moves left onto a 1). The sweeps never produce it
inside a domain; it would have to arise at a wall. There is no rule yet for how the walls move.

## What is proved

- `lean/Blank.lean` (generated): the halting configurations; no halt in 10^4 steps (kernel) and 10^7 (`native_decide`).
- `lean/Rules.lean` (from `py/rules.py`, kernel): the three leftward shift rules `a_left`, `b_left`, `c_left`.
- Computed (`tools/c/triage.c`): no halt in 10^9 steps.

Everything else on this page is heuristic: read off runs of up to 2·10^9 steps (`tools/c/tokrun.c`), not proved.

## For later

- Find the rule of a single sweep at a wall (what `000` between two domains becomes, and how far it moves), then the
  rule for a group of three domains; that would turn the staircase into a counter with an explicit carry.

## Reproduce

```sh
python3 holdouts/1RB0LC_1LA0RD_1LB1LF_0LA0RE_1RD0RA_1LD---/py/rules.py | diff - holdouts/1RB0LC_1LA0RD_1LB1LF_0LA0RE_1RD0RA_1LD---/lean/Rules.lean   # the rules file is current
gcc -O2 -o tokrun tools/c/tokrun.c
./tokrun 1RB0LC_1LA0RD_1LB1LF_0LA0RE_1RD0RA_1LD--- 400000000 x=0 LR 2000 | tail -4   # the tape each time the head extends it (x is a 0)
```

## Pages

- [`pages/holdouts/1RB0LC_1LA0RD_1LB1LF_0LA0RE_1RD0RA_1LD---/explainer.html`](../../pages/holdouts/1RB0LC_1LA0RD_1LB1LF_0LA0RE_1RD0RA_1LD---/explainer.html)
- [`pages/holdouts/1RB0LC_1LA0RD_1LB1LF_0LA0RE_1RD0RA_1LD---/proof-status.html`](../../pages/holdouts/1RB0LC_1LA0RD_1LB1LF_0LA0RE_1RD0RA_1LD---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LC_1LA0RD_1LB1LF_0LA0RE_1RD0RA_1LD---/lean/check.sh
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB---_0RC0LF_1LD0RE_1RC0LB_1RD1RA_1LB0LC`](../1RB---_0RC0LF_1LD0RE_1RC0LB_1RD1RA_1LB0LC/README.md): rename A→C, B→D, C→E, D→B, E→F, F→A and exchange left and right; it is this table started in state F, in a mirror
- [`1RB0LC_1LA0RD_0RB0LF_1RA1RE_1RC---_1LC0LB`](../1RB0LC_1LA0RD_0RB0LF_1RA1RE_1RC---_1LC0LB/README.md): rename A→B, B→A, C→D, D→C, E→F, F→E and exchange left and right; it is this table started in state B, in a mirror

<!-- end of related machines -->
