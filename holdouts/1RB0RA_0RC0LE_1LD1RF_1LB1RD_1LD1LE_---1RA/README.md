# 1RB0RA_0RC0LE_1LD1RF_1LB1RD_1LD1LE_---1RA

bbchallenge id 54294. One of the six-state holdouts whose halting from blank tape is open. Family: **nested binary
counter with resets** (siblings with the prefix `1RB0RA_0RC0L`).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RA |
| B | 0RC | 0LE |
| C | 1LD | 1RF |
| D | 1LB | 1RD |
| E | 1LD | 1LE |
| F | --- | 1RA |

## What it does

A sibling of [`1RB0RA_0RC0LD_1LA1RF_1LE1LD_1LB1RE_---1RA`](../1RB0RA_0RC0LD_1LA1RF_1LE1LD_1LB1RE_---1RA/README.md): with D and E swapped it is that machine with C0 = 1LE instead of 1LA. The
counter uses the same five rules with the same step counts (C0 is not used by them), so everything below about the
counter is the same; the resets differ.

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
| 1 | 5, 3 | 91 |
| 2 | 23, 12 | 72,177 |
| 3 | 51, 29, 5, 3 | 805,378,449 |
| 4 | 115, 74, 11 | 19 digits |
| 5 | 235, 165, 23, 12 | 37 digits |
| 6 | 489, 340, 57, 21, 11 | 75 digits |

**Halting.** The only halt is F on 0; F is entered only from C on 1 and C only from B on 0, so the machine halts
exactly at `B>0 1 0`, i.e. `K(0, ·)` (both directions in Lean: `halt_iff_2`, `halts_blank_pred_2` in `lean/HaltPred.lean`). Counter steps only meet blocks of 3 or more, so a halt can only come from a
reset. None of the 6 resets made one.

**Open:** the reset map (list → next list) in closed form, and a proof that it never produces `B>0 1 0`.
Heuristically, resets come after ~`2^(2^n)` steps and each is a fresh chance; nothing here bounds that chance.

## Status

Open.

- Lean, kernel (`lean/Base.lean`, written by `bbtools.symtm.prove`, with D for the sibling's E): rules `ruleP`, `ruleM1`, `ruleX0`, `ruleY`,
  `ruleZ` for all values of their parameters.
- Lean, kernel (`lean/Recursion.lean`): `rule_G` (the recursion above, for every `k ≥ 1`, `r`, `c ≥ k`, all tapes
  around), hence `rule_M` (the counter tick) and `chain`; `rule_Yn`, `rule_X` (the collapse of `r` frames).
- Lean, kernel (`lean/HaltPred.lean`, written by `python3 ../1RB0LD_0RC---_1LD0RF_0LE0RA_0RA1LF_0LA1LB/py/halt_pred.py 1RB0RA_0RC0LE_1LD1RF_1LB1RD_1LD1LE_---1RA 1 2 3`):
  every configuration that halts after exactly 1, 2 or 3 more steps; `halt_iff_2`: exactly `B> 0 1 0`.
- Lean (`lean/Blank.lean`): the halting configurations (`step_none_iff`), no halt in 10,000 steps by the kernel,
  in 10,000,000 by `native_decide`.
- Trusted computation: the sibling's `py/hybrid.py` with `machine=1RB0RA_0RC0LE_1LD1RF_1LB1RD_1LD1LE_---1RA` (cell by cell, but `M_k`/`G(r,k)` done at
  once when `c ≥ k`) gives the same 64 configurations at the same steps as `tools/c/tmrun.c` at every visit of the
  left end in state B (on a 0) in the first 2·10⁹ steps; its `py/resets.py` follows the run through 6 resets, to about
  10^75 steps, with no halt (stopped there: this machine's resets are slower in the Python simulator). The step-count
  formula `TM(k) = 3·2^(k+2) − 6` is checked from the recursion for `k < 3000`.
- `bbtools.ctl` up to K = 5 and `bbtools.invariants`: nothing.

## Scripts

- `python3 ../1RB0RA_0RC0LD_1LA1RF_1LE1LD_1LB1RE_---1RA/py/hybrid.py 2e9 1RB0RA_0RC0LE_1LD1RF_1LB1RD_1LD1LE_---1RA` — the configurations at every visit of the left end in state B.
- `python3 ../1RB0RA_0RC0LD_1LA1RF_1LE1LD_1LB1RE_---1RA/py/resets.py 75 1RB0RA_0RC0LE_1LD1RF_1LB1RD_1LD1LE_---1RA` — the resets up to 10^75 steps (seconds).

## Next steps

Accelerate the even phase `B>0 1^(2m) 0 ...` and the frame type `0 1 1 0` that appears in it in the sibling (both recursions of the
same kind), so that the reset becomes a short sequence of macro steps; then read off the reset map.

## Pages

- [`pages/holdouts/1RB0RA_0RC0LE_1LD1RF_1LB1RD_1LD1LE_---1RA/explainer.html`](../../pages/holdouts/1RB0RA_0RC0LE_1LD1RF_1LB1RD_1LD1LE_---1RA/explainer.html)
- [`pages/holdouts/1RB0RA_0RC0LE_1LD1RF_1LB1RD_1LD1LE_---1RA/proof-status.html`](../../pages/holdouts/1RB0RA_0RC0LE_1LD1RF_1LB1RD_1LD1LE_---1RA/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RA_0RC0LE_1LD1RF_1LB1RD_1LD1LE_---1RA/lean/check.sh
python3 holdouts/1RB0RA_0RC0LD_1LA1RF_1LE1LD_1LB1RE_---1RA/py/hybrid.py 2e9 1RB0RA_0RC0LE_1LD1RF_1LB1RD_1LD1LE_---1RA
```
