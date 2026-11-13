# 1RB0RA_0RC0LD_1LA1RF_1LE1LD_1LB1RE_---1RA

bbchallenge id 48098. One of the six-state holdouts whose halting from blank tape is open. Family: **nested binary
counter with resets** (siblings with the prefix `1RB0RA_0RC0L`).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RA |
| B | 0RC | 0LD |
| C | 1LA | 1RF |
| D | 1LE | 1LD |
| E | 1LB | 1RE |
| F | --- | 1RA |

## What it does

Write `K(n, c)` for the tape `B>0 1^(2n+1) 0 1^c` right of the head, and call `0 1 1` a *frame*. At every visit of
the left end in state B the tape is `B>0 1^(2k+1) 0 1^b 0 1^c ...`: a counter block and a *list* of blocks `b, c, ...`.

**The counter.** `M_k`: `0 0 K(k, c)` → `K(k+1, c)`, two cells to the left, whenever `c ≥ k`, in `3·2^(k+2) − 6`
steps. It is a recursion: `M_k` = P (split the block, leaving a frame `0 1 1` and `0^(2k−4)`, one cell taken from
`c`), then `M_1, ..., M_(k−2)` (each eats two of the 0s), then `G(1, k−1)`, where

    G(r, k):  0 0 (0 1 1)^r K(k, c)  →  K(r+k+1, c+r)        (c ≥ k)

is P, `M_1..M_(k−2)`, `G(r+1, k−1)`, and `G(r, 1)` is the collapse of the `r` frames (rules X0, Y, Z). `G(0, k)` is
`M_k`. So from `K(1, b)` at the left end the counter runs through `K(2, b)`, ..., `K(b+1, b)` in
`3·2^(b+3) − 6b − 24` steps.

**The resets.** At `K(b+1, b)` the next tick needs `b ≥ b+1`: the recursion runs out of the block `b` at its deepest
point and goes on into the rest of the list. A new list comes out (passing through an even block `B>0 1^(2m)`), and
the counter restarts at `K(1, ·)`. Lists at the start of the counter phases (exact simulator):

| phase | list | starts at step |
|---|---|---|
| 1 | 4 | 27 |
| 2 | 14, 5 | 1,507 |
| 3 | 35, 20 | 2,360,755 |
| 4 | 75, 41, 14, 5 | 3,298,537,245,315 |
| 5 | 165, 110, 19 | 26 digits |
| 6 | 335, 235, 42, 19 | 52 digits |
| 7 | 823, 428, 57, 5 | 125 digits |
| 8 | 1651, 893, 243, 135, 35, 20 | 250 digits |
| 9 | 3711, 2204, 317, 40, 14, 5 | 560 digits |

**Halting.** The only halt is F on 0; F is entered only from C on 1 and C only from B on 0, so the machine halts
exactly at `B>0 1 0`, i.e. `K(0, ·)` (both directions in Lean: `halt_iff_2`, `halts_blank_pred_2` in `lean/HaltPred.lean`). Counter steps only meet blocks of 3 or more, so a halt can only come from a
reset. None of the 9 resets made one.

**Open:** the reset map (list → next list) in closed form, and a proof that it never produces `B>0 1 0`.
Heuristically, resets come after ~`2^(2^n)` steps and each is a fresh chance; nothing here bounds that chance.

## Status

Open.

- Lean, kernel (`lean/Base.lean`, written by `bbtools.symtm.prove`): rules `ruleP`, `ruleM1`, `ruleX0`, `ruleY`,
  `ruleZ` for all values of their parameters.
- Lean, kernel (`lean/Recursion.lean`): `rule_G` (the recursion above, for every `k ≥ 1`, `r`, `c ≥ k`, all tapes
  around), hence `rule_M` (the counter tick) and `chain`; `rule_Yn`, `rule_X` (the collapse of `r` frames).
- Lean, kernel (`lean/HaltPred.lean`, written by `python3 ../1RB0LD_0RC---_1LD0RF_0LE0RA_0RA1LF_0LA1LB/py/halt_pred.py 1RB0RA_0RC0LD_1LA1RF_1LE1LD_1LB1RE_---1RA 1 2 3`):
  every configuration that halts after exactly 1, 2 or 3 more steps; `halt_iff_2`: exactly `B> 0 1 0`.
- Lean (`lean/Blank.lean`): the halting configurations (`step_none_iff`), no halt in 10,000 steps by the kernel,
  in 10,000,000 by `native_decide`.
- Trusted computation: `py/hybrid.py` (cell by cell, but `M_k`/`G(r,k)` done at once when `c ≥ k`) gives the same
  50 configurations at the same steps as `tools/c/tmrun.c` at every visit of the left end in state B in the first
  2·10⁹ steps; `py/resets.py` follows the run through 9 resets, to about 10^559 steps, with no halt. The step-count
  formula `TM(k) = 3·2^(k+2) − 6` is checked from the recursion for `k < 3000`.
- `bbtools.ctl` up to K = 5 and `bbtools.invariants`: nothing.

## Scripts

- `python3 py/hybrid.py 2e9` — the configurations at every visit of the left end in state B (compare with
  `tmrun M 2000000000 at B L 400`).
- `python3 py/resets.py 600` — the resets up to 10^600 steps (about 25 minutes).

## Next steps

Accelerate the even phase `B>0 1^(2m) 0 ...` and the frame type `0 1 1 0` that appears in it (both recursions of the
same kind), so that the reset becomes a short sequence of macro steps; then read off the reset map.

## Pages

- [`pages/holdouts/1RB0RA_0RC0LD_1LA1RF_1LE1LD_1LB1RE_---1RA/explainer.html`](../../pages/holdouts/1RB0RA_0RC0LD_1LA1RF_1LE1LD_1LB1RE_---1RA/explainer.html)
- [`pages/holdouts/1RB0RA_0RC0LD_1LA1RF_1LE1LD_1LB1RE_---1RA/proof-status.html`](../../pages/holdouts/1RB0RA_0RC0LD_1LA1RF_1LE1LD_1LB1RE_---1RA/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RA_0RC0LD_1LA1RF_1LE1LD_1LB1RE_---1RA/lean/check.sh
python3 holdouts/1RB0RA_0RC0LD_1LA1RF_1LE1LD_1LB1RE_---1RA/py/hybrid.py 2e9
```
