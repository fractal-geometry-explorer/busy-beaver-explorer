# 1RB0RE_1RC---_0RD0RC_1LE1LF_1LD1RA_1RC0LF

bbchallenge id 92948. A Collatz-like map that multiplies by powers of 3/2: phase starts [1] (10)^x 1110 go to x' ≈ (3/2)^k·x, with k set by the low binary digits of x; the orbit from blank tape stays in the decoded cases for 63 phases, up to x ≈ 2.2·10^15.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RE |
| B | 1RC | --- |
| C | 0RD | 0RC |
| D | 1LE | 1LF |
| E | 1LD | 1RA |
| F | 1RC | 0LF |

## What it does

Phase start `P(pre, x)`: the tape `[1] (10)^x 1 1 1 0` with D at the right end (blank to the right); `pre` = 1 when the
leading 1 is there. The run from blank tape is at P(1, 3) after 34 steps, P(0, 9) after 139, P(1, 18) after 520.

**Rounds** (proved, `lean/Rules.lean`): `(10)^(x+2) 1110 (00)^g 00 D>` → `(10)^x 1110 (00)^(g+3) 00 D>` in 4g + 26
steps (and `first_round` from no gap): two `10`s leave the stack, six 0s join the gap. At the end the gap becomes the
new stack.

**Phase map** (checked by simulation for all 225 decoded cases with x ≤ 120, `py/phasemap.py`):

| from | to |
|---|---|
| P(0, x) | P(x mod 2, 3⌊x/2⌋ + 6) |
| P(1, 2i+1) | P(0, 3i + 6) |
| P(1, 4i+2) | P(1, 9i + 15) |
| P(1, 8i) | P(1, 27i + 18) |
| P(1, 8i+4) | splits further: 32i+20 → P(0, 243i+202), 32i+28 → P(0, 243i+264) (i ≤ 3); 4 → P(0, 193), 12 → P(1, 3771), 36 → P(1, 492); 44, 68 > 10^8 steps |

Slopes 3/2, 9/4, 27/8, ..., 243/32. The blank orbit: P(1,3), P(0,9), P(1,18), P(1,51), P(0,81), P(1,126), P(1,294),
P(1,672), P(1,2286), P(1,5154), P(1,11607), P(0,17415), P(1,26127), P(0,39195), ... (agrees with the run to
1.8·10^9 steps), 63 phases in the decoded cases, to P(1, 2162240868156300) ≡ 4 (mod 8).

## Halting

Only B1 halts; B is entered only from A0, A only from E1: halts iff `E> 1 0 1`. Not seen in any run. CTL K = 3..6:
halts remain; n-gram CPS 3..7 fails.

## Notes for later

- Prove the phase ends (the gap is turned into a stack one `10` at a time; needs an induction with the intermediate
  shape) and the P(1, ·) levels; find the general rule for P(1, 2^k·odd).

## Pages

- [`pages/holdouts/1RB0RE_1RC---_0RD0RC_1LE1LF_1LD1RA_1RC0LF/explainer.html`](../../pages/holdouts/1RB0RE_1RC---_0RD0RC_1LE1LF_1LD1RA_1RC0LF/explainer.html)
- [`pages/holdouts/1RB0RE_1RC---_0RD0RC_1LE1LF_1LD1RA_1RC0LF/proof-status.html`](../../pages/holdouts/1RB0RE_1RC---_0RD0RC_1LE1LF_1LD1RA_1RC0LF/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RE_1RC---_0RD0RC_1LE1LF_1LD1RA_1RC0LF/lean/check.sh
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB---_0RC0RB_1LD1LE_1LC1RF_1RB0LE_1RA0RD`](../1RB---_0RC0RB_1LD1LE_1LC1RF_1RB0LE_1RA0RD/README.md): rename A→F, B→A, C→B, D→C, E→D, F→E; it is this table started in state B

<!-- end of related machines -->
