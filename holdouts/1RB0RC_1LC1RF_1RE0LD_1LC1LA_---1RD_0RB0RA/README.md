# 1RB0RC_1LC1RF_1RE0LD_1LC1LA_---1RD_0RB0RA

bbchallenge id 132224. One of the six-state holdouts whose halting from blank tape is open; analyzed by hand (group G02). The pages are built from [`status.json`](status.json).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RC |
| B | 1LC | 1RF |
| C | 1RE | 0LD |
| D | 1LC | 1LA |
| E | --- | 1RD |
| F | 0RB | 0RA |

## What it does

With the head in A at the left end and words `a = 10`, `b = 110`, `d = 010`, the tape is `a b`, one big block, and
a short tail:

    step 2,831,052,048:  A>a b d a^34948 0 d^23 a d^10 a^26 d^8 a^8 d^8 a^8 d^4 a^2 1
    step 2,851,126,369:  A>a b d^23325 a d^2 a^32 d^16 a^26 d^4 b d^7 a^8 d^4 a^8 1

The big block alternates between `d^Y` and `a^X` (observed): `d^Y` becomes `a^(2Y+2)` (Y = 17,473 → X = 34,948);
`a^X` becomes a d-block of about 2X/3, the remainder and a little of the tail settled in the tail (X = 34,948 →
Y = 23,325). So Y grows by about 4/3 per cycle: 61, 83, 137, 195, 261, 357, 481, 667, 887, 1239, 1675, 2247,
3009, 4025, 5375, 7171, 9565, 12953, 17473, 23325 (to 2.9·10^9 steps). The tail, a small counter, changes only at
the conversions (logarithmic side); the sweeps over the big block make the bouncer side.

Shift rules proved for every n (`lean/Rules.lean`): B crosses `(10)^n`, F crosses `(01)^n`, A turns `011` into
`110`, B turns `110` into `101` (all going right).

## Status

Open. The only halt is E reading a 0, right after C read a 0 and moved right; in 10^9 steps E was entered
5,798,513 times and always read a 1.

- Lean, kernel: shift rules (`lean/Rules.lean`); halting configurations, 10^4 steps (`lean/Blank.lean`).
  `native_decide`: 10^7 steps.
- Computed: no halt in 10^10 steps (`tools/c/tmrun.c`); `bbtools.ctl` K = 2..7 allows a halt; n-gram CPS fails.

## Notes for later

- Write the exact cycle map: X = 2Y + 2 on the d→a side (seen in most cycles; 61 → 120 and the cycles where the tail merges into the block differ),
  and on the a→d side the dependence on X mod 3 and on the tail. Then the halting question should become a
  question about that Collatz-like map (which tail states let C meet `00`).

## Pages

- [`pages/holdouts/1RB0RC_1LC1RF_1RE0LD_1LC1LA_---1RD_0RB0RA/explainer.html`](../../pages/holdouts/1RB0RC_1LC1RF_1RE0LD_1LC1LA_---1RD_0RB0RA/explainer.html)
- [`pages/holdouts/1RB0RC_1LC1RF_1RE0LD_1LC1LA_---1RD_0RB0RA/proof-status.html`](../../pages/holdouts/1RB0RC_1LC1RF_1RE0LD_1LC1LA_---1RD_0RB0RA/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RC_1LC1RF_1RE0LD_1LC1LA_---1RD_0RB0RA/lean/check.sh
```
