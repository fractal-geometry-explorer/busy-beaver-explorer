# 1RB1LB_1LC1LA_1RD0LB_1RA1RE_1RF0RD_---1RD

bbchallenge id 89641, a BB(6) holdout (group G06). Family: **5/2 Collatz-like counter feeding a carry chain**.
Open; it halts only if a carry ever runs through a tail of digits that grows by about one digit every three epochs.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LB |
| B | 1LC | 1LA |
| C | 1RD | 0LB |
| D | 1RA | 1RE |
| E | 1RF | 0RD |
| F | --- | 1RD |

## What it does

Everything happens left of the start. Write `a = 01`. An **epoch** starts at

    0^inf 1 B> 1 01 0101 1^5 a^Y T          T = 1^(5d1) a^e1 1^(5d2) a^e2 ... 1^4 a

a counter of `Y` a's and a tail `T` of digits `(d, e) = 1^(5d) a^e`, ending in the fixed word `1^4 a`. The first epoch
starts at step 494 with `Y = 5`, `T = (1,8)`.

**Rounds.** Between the left end and the counter there is a block of `X` ones (0 at the start of the epoch) and a
marker `0101` or `01`. With `c0 j Y R = 0^inf 1 B> 1 01 (1^10)^j 0101 1^5 a^Y R`:

* `round_a`: `c0 j Y R` -> `0^inf 1 B> 1 01 (1^10)^j 1^5 01 1^5 a^Y R` in 30j+19 steps;
* `round_b`: `0^inf 1 B> 1 01 (1^10)^j 1^5 01 1^5 a^(Y+2) R` -> `c0 (j+1) Y R` in 30j+51 steps;
* `epoch` (Epoch.lean, induction): `c0 j (Y+2k) R` reaches `c0 (j+k) Y R`.

Each round the head runs right through the block (`D> 11 -> 10 D>`), zigzags back turning the a's into ones, adds
five ones; every second round two a's of the counter are used. At the end of the counter the block holds
`X = 5Y+5` (Y even) or `5Y` (Y odd) ones, i.e. `X = 10j+5` with `j = floor(Y/2)`. An epoch costs about 3.75 Y^2
steps, which gives the square-root growth of the left side.

**Reset.** Then one sweep (states D/E) turns the `X` ones back into a's and runs into the tail: it passes a digit
exactly when its block of ones is odd and it has one a (`D> 1 0 1 -> 1 1 1 D>`), and otherwise turns back and
rewrites the front digits. The next epoch has

    Y' = 5 floor(Y/2) + c,   c in {0, 5, 10},   T' = F(T*)

where `T* = (1+d1, e1), (d2, e2), ...` for even Y (the counter's `1^5` merges into the first digit) and
`T* = (1,1), T` for odd Y, and `F` depends only on the front of `T*` (not on j). Proved shapes (Rules.lean, for all
j, k, e and tapes R; the reset starts at `0^inf 1 B> 1 01 (11)^(5j+7) 1 01 T*`):

| T* starts with | becomes | c | theorem |
|---|---|---|---|
| (2k+2, e+1) | (2k+3, e) | 0 | `reset_even` |
| (3, e+3) | (1,4) (1, e+1) | 5 | `reset_odd3` |
| (1,1) (1, e+3) | (2,2) (1, e+1) | 0 | `carry_one` |
| (1,1) (3, e+3) | (2,7) (1, e+1) | 0 | `carry_three` |

Other shapes seen (computed): `(d odd, e)` with even Y -> `(d+2, e-1)`; `(2i+1, e>=2)` -> `(1, 5i-1) (1, e-2)` with
c = 5; `(odd d, 1) (d2, e2)` passes the carry into the next digit, and so on. `py/epochs.py` computes F by running
the reset on the machine itself.

## Status

Open. Halting needs the reset sweep to read `1 0 0` (F0 is the only halt and F is entered only from `D> 1 0`), which
happens only if the sweep passes every digit of the tail and arrives out of step at the right end.

* `py/epochs.py --check 14`: the epoch map agrees with the plain (accelerated, exact) run for the first 13 epochs,
  7.3e11 steps.
* `py/epochs.py 4000`: 4,000 epochs, no halt; Y has 1,593 decimal digits, the tail 1,311 digits, and no reset changed
  more than the first three digits.
* Choosing the parity of Y freely at each epoch, halting is reachable from the real start within 10 epochs (e.g. at
  tail `(1,1)(19,0) 1^4`). So a non-halting proof must use the actual parities.
* Heuristic: with fair-coin parities the carry depth has an exponential tail (depth >= 5 a few times in 5,000
  epochs) while the tail grows linearly, so a halt is astronomically unlikely. The parities come from
  `Y -> 5 floor(Y/2) + c`, a Mahler-type 5/2 sequence: proving anything about them looks out of reach.

## For later

* Prove `F` completely (a finite list of parametric reset shapes plus the merge of `e = 0` digits), and the glue
  between `epoch` and the reset lemmas (re-bracketing `(1^10)^j 1^5` as `(11)^(5j+2) 1`).
* An invariant on the tail that a carry cannot cross for any parities is impossible (see above); a proof would need
  an argument about the 5/2 sequence.

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LB_1LC1LA_1RD0LB_1RA1RE_1RF0RD_---1RD/lean/check.sh
python3 holdouts/1RB1LB_1LC1LA_1RD0LB_1RA1RE_1RF0RD_---1RD/py/epochs.py --check 14
python3 holdouts/1RB1LB_1LC1LA_1RD0LB_1RA1RE_1RF0RD_---1RD/py/epochs.py 4000
```

Lean files: `lean/Machine.lean`, `lean/Blank.lean` (generated), `lean/Rules.lean` (`python3 lean/rules.py >
lean/Rules.lean`), `lean/Epoch.lean`.

## Pages

- [`pages/holdouts/1RB1LB_1LC1LA_1RD0LB_1RA1RE_1RF0RD_---1RD/explainer.html`](../../pages/holdouts/1RB1LB_1LC1LA_1RD0LB_1RA1RE_1RF0RD_---1RD/explainer.html)
- [`pages/holdouts/1RB1LB_1LC1LA_1RD0LB_1RA1RE_1RF0RD_---1RD/proof-status.html`](../../pages/holdouts/1RB1LB_1LC1LA_1RD0LB_1RA1RE_1RF0RD_---1RD/proof-status.html)
