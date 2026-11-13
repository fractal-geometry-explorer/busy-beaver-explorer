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

## Pages

- [`pages/holdouts/1RB0LF_1RC1RB_1RD0RA_1RE0RE_1LF---_0LD1LA/explainer.html`](../../pages/holdouts/1RB0LF_1RC1RB_1RD0RA_1RE0RE_1LF---_0LD1LA/explainer.html)
- [`pages/holdouts/1RB0LF_1RC1RB_1RD0RA_1RE0RE_1LF---_0LD1LA/proof-status.html`](../../pages/holdouts/1RB0LF_1RC1RB_1RD0RA_1RE0RE_1LF---_0LD1LA/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LF_1RC1RB_1RD0RA_1RE0RE_1LF---_0LD1LA/lean/check.sh
```
