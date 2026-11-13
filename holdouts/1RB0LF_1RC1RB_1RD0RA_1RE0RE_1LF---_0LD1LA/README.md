# 1RB0LF_1RC1RB_1RD0RA_1RE0RE_1LF---_0LD1LA

bbchallenge id 139893. One of the six-state holdouts whose halting from blank tape is open.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LF |
| B | 1RC | 1RB |
| C | 1RD | 0RA |
| D | 1RE | 0RE |
| E | 1LF | --- |
| F | 0LD | 1LA |

## What it does

**Tape**: blocks of ones separated by single zeros. **Sample point**: C on a 0 at the right end (rare deep sweeps).
At step 9,704,124 the block lengths begin `3 19 3x2 7 3x2 15 11 3 27 3x3 11 23 3 7 ...` (`7` = 1^7 0, `3x2` = two
blocks 1^3 0). Each sweep rewrites the blocks by local rules (Lean shift rules in `lean/Rules.lean`), like a 1D
cellular automaton; the space-time picture shows Sierpinski-like triangles. Tape length 4,852 / 15,028 / 47,528 at
10^7 / 10^8 / 10^9 steps (about 1.5 sqrt t). Deep sweeps to the right end come in clusters about 3.1x apart.

**Twin**: at all 42 right-end C0 events in 10^9 steps the tape is identical to that of
1RB0LE_1RC1RB_1RD0RA_0RE---_1LF1LA_1LA1LF at its 42 events, at 1.5 times the step count (observed, `c/tok.c`).

**Halting**: E on a 1 is the only halt; E comes only from D moving right, and D from C on a 0 (moving right) or F on
a 0 (moving left, which leaves a 0 under E). So it halts iff `C> 0 0 1` or `C> 0 1 1` occurs (`halt_shape0`,
`halt_shape1`). C reads a 0 only at the right end (42 times in 10^9 steps), with blank to its right.

## Status

Open.

- **Lean, kernel** (`lean/Rules.lean`, from `py/rules.py`): `b_run`, `a_right`, `b_right`, `a_left`, `f_left`,
  `d_left`, `halt_shape0`, `halt_shape1`, `halt_after_shape`. `lean/Blank.lean`: no halt in 10^7 steps.
- **Trusted**: no halt in 10^9 steps; near-miss counts (`c/nbhd.c`); identical right-end tapes with the twin.
- **Heuristic**: growth and deep-sweep spacing.

## Notes for later

- Prove the simulation relation with 1RB0LE_1RC1RB_1RD0RA_0RE---_1LF1LA_1LA1LF (a map between configurations, three
  steps here for two there on average); then the two holdouts stand or fall together.
- Both need an invariant saying C never reads a 0 inside the tape: e.g. that the zeros stay single and C is only
  entered from B on a 0 at the right end.

## Reproduce

```sh
gcc -O2 -o tok holdouts/1RB0LF_1RC1RB_1RD0RA_1RE0RE_1LF---_0LD1LA/c/tok.c && ./tok 1RB0LF_1RC1RB_1RD0RA_1RE0RE_1LF---_0LD1LA 1000000000 C 0 R 0 1000 0 | cut -d'|' -f2 | md5sum
./tok 1RB0LE_1RC1RB_1RD0RA_0RE---_1LF1LA_1LA1LF 1000000000 C 0 R 0 1000 0 | cut -d'|' -f2 | md5sum   # same hash
gcc -O2 -o nbhd holdouts/1RB0LF_1RC1RB_1RD0RA_1RE0RE_1LF---_0LD1LA/c/nbhd.c && ./nbhd 1RB0LF_1RC1RB_1RD0RA_1RE0RE_1LF---_0LD1LA 1000000000 C 0
python3 holdouts/1RB0LF_1RC1RB_1RD0RA_1RE0RE_1LF---_0LD1LA/py/rules.py > holdouts/1RB0LF_1RC1RB_1RD0RA_1RE0RE_1LF---_0LD1LA/lean/Rules.lean
```

## Where a halt can come from

`lean/Route.lean` (kernel, written by `py/route.py`): `halt_route`, two steps before any halt the machine is in one
of: C with 0 under the head, 1 two right.

## Pages

- [`pages/holdouts/1RB0LF_1RC1RB_1RD0RA_1RE0RE_1LF---_0LD1LA/explainer.html`](../../pages/holdouts/1RB0LF_1RC1RB_1RD0RA_1RE0RE_1LF---_0LD1LA/explainer.html)
- [`pages/holdouts/1RB0LF_1RC1RB_1RD0RA_1RE0RE_1LF---_0LD1LA/proof-status.html`](../../pages/holdouts/1RB0LF_1RC1RB_1RD0RA_1RE0RE_1LF---_0LD1LA/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LF_1RC1RB_1RD0RA_1RE0RE_1LF---_0LD1LA/lean/check.sh
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB---_0RC1RD_1LA0LA_1LE0RB_1LF1LE_1LC0LD`](../1RB---_0RC1RD_1LA0LA_1LE0RB_1LF1LE_1LC0LD/README.md): rename A→D, B→E, C→F, D→C, E→A, F→B and exchange left and right; it is this table started in state E, in a mirror
- [`1RB0RE_1RC0RC_1LD---_0LB1LE_1RF0LD_1RA1RF`](../1RB0RE_1RC0RC_1LD---_0LB1LE_1RF0LD_1RA1RF/README.md): rename A→E, B→F, C→A, D→B, E→C, F→D; it is this table started in state C
- [`1RB0RB_1LC---_0LA1LD_1RE0LC_1RF1RE_1RA0RD`](../1RB0RB_1LC---_0LA1LD_1RE0LC_1RF1RE_1RA0RD/README.md): rename A→D, B→E, C→F, D→A, E→B, F→C; it is this table started in state D
- [`1RB1RA_1RC0RF_1RD0RD_1LE---_0LC1LF_1RA0LE`](../1RB1RA_1RC0RF_1RD0RD_1LE---_0LC1LF_1RA0LE/README.md): rename A→F, B→A, C→B, D→C, E→D, F→E; it is this table started in state B

**Same tapes at another pace (observed, not proved).** Leave the states aside and compare only the tape and the place of the head. Then a large part of the first 10^7 configurations of this machine are configurations of the machines below, in the same order and up to the end of the run. The steps at which they occur differ, the tables are not renamings of each other, and equal tapes with different states may be continued differently, so this does not tie the halting questions together.

- [`1RB0LE_1RC1RB_1RD0RA_0RE---_1LF1LA_1LA1LF`](../1RB0LE_1RC1RB_1RD0RA_0RE---_1LF1LA_1LA1LF/README.md): 4,986,200 configurations, the last at step 10,000,000 here and step 6,657,506 there

<!-- end of related machines -->
