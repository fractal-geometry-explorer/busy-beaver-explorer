# 1RB0LD_0RC1RA_1RD1RE_1LA0LE_0RA0RF_1RC---

bbchallenge id 47099. One of the six-state holdouts whose halting from blank tape is open (group G05, growth class
fixed/sqrt).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LD |
| B | 0RC | 1RA |
| C | 1RD | 1RE |
| D | 1LA | 0LE |
| E | 0RA | 0RF |
| F | 1RC | --- |

## Status

**Open.** A multi-level counter: the tape is a stack of levels `1^n (01)^m`, and each level is a counter of the same
kind as the one below it, advanced only when the one below ends an epoch with two ones left. The common rules are
proved for all sizes; which rule comes next depends on the size of level 1 modulo 3.

- Lean, kernel (`lean/Blank.lean`): the halting configurations (`step_none_iff`), no halt in 10,000 steps.
- Lean, `native_decide` (`lean/Blank.lean`): no halt in 10,000,000 steps.
- Lean, kernel (`lean/Rules.lean`, namespace `H47099`): `start` (blank tape to `(01)^9 C>` in 89 steps), `trip`,
  `trips` (k trips by induction), and the epoch ends `zero_blank`, `zero_dec`, `zero_merge`, `two_blank`,
  `two_trip`, `two_dec`, `two_merge`, all for every size and with exact step counts.
- Trusted (C, `tools/c/triage.c`): no halt in 10⁹ steps.
- Trusted (`py/stack.py`, exact integers): following those rules from blank tape, no halt in the first 10^39417
  steps (37,692 epochs in two minutes). 37,691 epoch ends are instances of the Lean rules; one (a carry into level 3)
  was computed by plain simulation with level 1 cut down and extrapolated linearly. The first 9 epochs
  (2.96·10¹⁰ steps) agree with the plain C simulator `c/canon.c` (`py/stack.py check 9`).
- Heuristic: the rule for levels 3 and up (below), seen in every simulated case with m ≥ 5.
- Open: halting.

## The stack

Whenever the head is in state C at the right end with a 1 to its left, the tape is

    0^∞ [1^n_k (01)^m_k 0] … [1^n_2 (01)^m_2 0] 1^n_1 (01)^m_1 C> 0^∞

No level has n = 1: `0 1 (01)^m` is `(01)^(m+1)` on the level above. Blank tape counts as levels `(0, 0)`.

**Trips** (`trip`): `1^(n+3) (01)^(m+1) C>` → `1^n (01)^(m+6) C>` in 6m + 45 steps. So level 1 `(n, m)` becomes
`(r, m + 5k)` with n = 3k + r, in k(6m + 24) + 15k² steps (`trips`).

**Epoch end**, with level 1 = `(r, M)`:

| r | level 2 | result | rule |
|---|---|---|---|
| 0 | `(n₂, m₂)`, m₂ ≥ 1 | level 1 `(2M+7, 3)`, level 2 `(n₂, m₂−1)` | `zero_dec` |
| 0 | `(n₂, 0)` | level 1 `(2M+6+n₂, 3)`, level 2 removed | `zero_merge`, `zero_blank` |
| 1 | any | pop: level 2 becomes `(n₂, m₂+M+1)`, the new level 1 | (same tape) |
| 2 | `(n₂+3, q)` | level 2 `(n₂, q+7)` (popped if n₂ = 1), level 1 `(2M−4, 3)` | `two_trip` |
| 2 | `(0, q)`, q ≥ 4 | level 2 `(2q+5, 6)` taking a `01` from level 3, or `(2q+4+n₃, 6)` absorbing it; level 1 `(2M−8, 3)` | `two_dec`, `two_merge`, `two_blank` |
| 2 | `(2, q)` | carry: level 3 takes a step, level 2 `(2q−6, 6)` or `(2q−10, 6)`, level 1 `(2M−8, 3)` | not in Lean |

The same table holds at every level k ≥ 2 when the level below ends with two ones (trip +7 instead of +5, rebuild
`(2m+5, 6)` / `(2m+4+p, 6)`, carry `(2m−6, 6)` after a trip above, `(2m−10, 6)` otherwise), for m ≥ 5; with m ≤ 4
a carry does something else (tabulated only by simulation, see `py/stack.py`). So this is a counter whose digits
are counters of the same kind, each run one step per carry from below.

Each epoch multiplies level 1 by about 10/3 and the step count by about 11. First epochs (step, new level 1):
170 `1^24`, 1,683 `1^92`, 17,146 `1^298` (level 2 `1^4 (01)^6` pushed), 173,477 `1^1028`, 1,949,244 `1^3418`, …
The stack stays shallow because level 1 pops whenever its size is 1 mod 3; in 37,692 epochs there was one carry
into level 3 (epoch 30,402).

## Halting

The machine halts only when state F reads a 1. No proved rule does. Plain simulation of all 8,064 epoch ends with
level 1 large and up to two small levels (n ∈ {0, 2, …, 7}, m ≤ 8) found no halt. A non-halting proof would need
the carry and the short-level cases as rules too, and an invariant on the stacks that can arise; the order of the
cases follows the residues mod 3 of sizes growing by 10/3, which is Collatz-like.

## Reproduce

```sh
python3 holdouts/1RB0LD_0RC1RA_1RD1RE_1LA0LE_0RA0RF_1RC---/py/gen_rules.py > holdouts/1RB0LD_0RC1RA_1RD1RE_1LA0LE_0RA0RF_1RC---/lean/Rules.lean
python3 holdouts/1RB0LD_0RC1RA_1RD1RE_1LA0LE_0RA0RF_1RC---/py/stack.py check 8     # stack simulator vs plain C (c/canon.c)
python3 holdouts/1RB0LD_0RC1RA_1RD1RE_1LA0LE_0RA0RF_1RC---/py/stack.py run 120     # one line per epoch for two minutes
```

## Pages

- [`pages/holdouts/1RB0LD_0RC1RA_1RD1RE_1LA0LE_0RA0RF_1RC---/explainer.html`](../../pages/holdouts/1RB0LD_0RC1RA_1RD1RE_1LA0LE_0RA0RF_1RC---/explainer.html)
- [`pages/holdouts/1RB0LD_0RC1RA_1RD1RE_1LA0LE_0RA0RF_1RC---/proof-status.html`](../../pages/holdouts/1RB0LD_0RC1RA_1RD1RE_1LA0LE_0RA0RF_1RC---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LD_0RC1RA_1RD1RE_1LA0LE_0RA0RF_1RC---/lean/check.sh
```

## For later

- Prove the carry rule (level 2 with two ones) in Lean: it is the same pass as `two_trip`/`two_dec` with one more
  level, so a symbolic run with level 3 as a context should do it. Then tabulate the short-level cases (m ≤ 4).
- With all cases as rules, look for an invariant on reachable stacks, or a reachable stack that halts.
- A Lean check of the run itself: chain `start`, `trips` and the epoch rules for the first epochs (as `native_decide`
  over the stack, with a proof that each stack step is a rule instance).

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB---_1RC1RE_1LD0LE_1RF0LC_0RD0RA_0RB1RD`](../1RB---_1RC1RE_1LD0LE_1RF0LC_0RD0RA_0RB1RD/README.md): rename A→D, B→F, C→B, D→C, E→E, F→A; it is this table started in state F
- [`1RB1RE_1LC0LE_1RD0LB_0RA1RC_0RC0RF_1RA---`](../1RB1RE_1LC0LE_1RD0LB_0RA1RC_0RC0RF_1RA---/README.md): rename A→C, B→D, C→A, D→B, E→E, F→F; it is this table started in state C
- [`1RB0RE_1LC0RA_0LD1LB_1LA1LE_0LB0LF_1LD---`](../1RB0RE_1LC0RA_0LD1LB_1LA1LE_0LB0LF_1LD---/README.md): rename A→B, B→C, C→D, D→A, E→E, F→F and exchange left and right; it is this table started in state D, in a mirror

<!-- end of related machines -->
