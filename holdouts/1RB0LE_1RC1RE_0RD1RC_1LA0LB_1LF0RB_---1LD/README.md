# 1RB0LE_1RC1RE_0RD1RC_1LA0LB_1LF0RB_---1LD

bbchallenge id 45924. One of the six-state holdouts whose halting from blank tape is open.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LE |
| B | 1RC | 1RE |
| C | 0RD | 1RC |
| D | 1LA | 0LB |
| E | 1LF | 0RB |
| F | --- | 1LD |

## What it does

**Sample point**: the whole tape is one run of ones, `F> 1^N` (head on the leftmost 1, blank elsewhere). From blank
tape this happens with N = 8 (step 43), then

    8, 22, 42, 58, 90, 148, 218, 298, 410, 554, 746, 1002, 1344, 1558, 2090, 2794, 3738, 4992, 6674, 8906,
    11882, 15850, 21146, 28202, 37610, 50154 (step 1,796,208,166), 89188, 132216, 146976, 348442

Since the phase from `F> 1^N` depends only on N, the machine is the iteration of a map f on these N.

**One phase** (example N = 90): the first sweep turns 1^90 into blocks `1110` (`e_halve`: each `11` becomes `01`, then
the left sweep fills them); merging sweeps group three blocks into one (`e_triple`, `d_triple`): 1^3 0 -> 1^11 0 ->
1^35 0 -> ... (3a+2), while the block count divides by 3, the leftovers piling up on the left; then the tape fills
with ones again: 1^148 after 8,047 steps. So f depends on the base-3 digits of N. For most N, 3 f(N) - 4N is small
(22 or 34 when N = 2 or 8 mod 12, 38 when N = 10 or 22 mod 36, ...), i.e. f(N) ~ 4N/3; N divisible by high powers of 3
jump further (f(16) = 90, f(35) = 240, f(50154) = 89188).

**Halting**: F on a 0 is the only halt; F needs E on a 0 entered from A on a 1, and A comes only from D on a 0. So it
halts iff D reads a 0 with `1 0 0` to its left (`halt_shape`). In 10^9 steps D read a 0 62,593 times, never with
`1 0 0` to its left (closest: `1 0 1`, 32,865 times).

**The decisive fact so far**: for every N from 1 to 6,000 the phase from `F> 1^N` returns to an all-ones tape without
halting (`c/phasemap.c`). So no N at all is known to be dangerous; if none is, the machine never halts.

## Status

Open.

- **Lean, kernel** (`lean/Orbit.lean`): the samples 1^8 (step 43), 1^90 (5,156), 1^148 (13,203) from blank tape.
  **native_decide**: 1^4992 (step 17,659,931), 1^8906 (56,708,301).
- **Lean, kernel** (`lean/Rules.lean`, from `py/rules.py`): `blank_to_8`, `e_halve`, `e_triple`, `d_triple`,
  `halt_shape` (`0 0 1 D> 0` reaches F on a 0 in 3 steps), `halt_after_shape`.
- **Trusted**: the phase map for every N <= 6,000 (no halt); the orbit above to N = 348,442 (3.5·10^11 steps);
  the near-miss count (`c/nbhd.c`).
- **Heuristic**: the base-3 description of a phase.

## Notes for later

- Prove that no phase halts: write the phase as a recursion on the base-3 regrouping (stage j has blocks
  1^(3^j·4−1)... with the leftover pile) and check each stage's local rules. This would settle the machine (never
  halts). The symbolic prover gets stuck on the change of period between sweeps (`0101` -> `1110` -> 12-cell words),
  so it needs hand-made rules for each stage, parametrized by the stage.
- The orbit beyond 348,442 can be pushed with `c/phasemap.c` (each phase costs about N^2 steps).

## Reproduce

```sh
gcc -O2 -o phasemap holdouts/1RB0LE_1RC1RE_0RD1RC_1LA0LB_1LF0RB_---1LD/c/phasemap.c && ./phasemap 6000 20000000000      # f(N) for N <= 6000 (minutes)
./phasemap 50154 400000000000 50154                                                # one phase of the orbit
gcc -O2 -o nbhd holdouts/1RB0LE_1RC1RE_0RD1RC_1LA0LB_1LF0RB_---1LD/c/nbhd.c && ./nbhd 1RB0LE_1RC1RE_0RD1RC_1LA0LB_1LF0RB_---1LD 1000000000 D 0
python3 holdouts/1RB0LE_1RC1RE_0RD1RC_1LA0LB_1LF0RB_---1LD/py/rules.py > holdouts/1RB0LE_1RC1RE_0RD1RC_1LA0LB_1LF0RB_---1LD/lean/Rules.lean
```

## Pages

- [`pages/holdouts/1RB0LE_1RC1RE_0RD1RC_1LA0LB_1LF0RB_---1LD/explainer.html`](../../pages/holdouts/1RB0LE_1RC1RE_0RD1RC_1LA0LB_1LF0RB_---1LD/explainer.html)
- [`pages/holdouts/1RB0LE_1RC1RE_0RD1RC_1LA0LB_1LF0RB_---1LD/proof-status.html`](../../pages/holdouts/1RB0LE_1RC1RE_0RD1RC_1LA0LB_1LF0RB_---1LD/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LE_1RC1RE_0RD1RC_1LA0LB_1LF0RB_---1LD/lean/check.sh
```
