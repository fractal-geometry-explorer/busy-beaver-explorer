# 1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA0LB_---0LC

bbchallenge id 24009. A BB(6) holdout whose halting from blank tape is open; listed on the bbchallenge wiki as *probviously halting* (mxdys, with 16 related holdouts of near-identical behaviour). Family: **Collatz-like epochs (y ↦ ⌈3y/2⌉ countdown)**. Decision: **open**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RA |
| B | 0RC | 1RC |
| C | 1LD | 0LF |
| D | 0LE | 1LE |
| E | 1RA | 0LB |
| F | --- | 0LC |

## What it does

The run returns again and again to

    X(n, m) = 0^∞ C>0 0^n 1^m 0 1 0^∞        (n even)

Between two of them the head fills the 0s with 1s from the left, two per round trip while the tape grows by one
cell at the left, and takes 1s off the `1^m` block. The rules (n ≥ 2 even):

| case | next |
|---|---|
| m ≥ 2, n ≡ 0 (mod 4) | X(3n/2 + 4, m − 1) |
| m ≥ 2, n ≡ 2 (mod 4) | X((3n + 10)/2, m − 2) |
| m = 1 | n ≡ 0: X(3n/2 + 4, 0); n ≡ 2: new epoch X(4, 3n/2 + 6) |
| m = 0 | n ≡ 0: new epoch X(4, 3n/2 + 5); n ≡ 2: **halt** |

With `y = n/2 + 4` the main rule is `y ↦ ⌈3y/2⌉`, m losing 1 (y even) or 2 (y odd). Every epoch starts at n = 4.
From blank tape: X(4, 5) after 50 steps; epochs start with m = 5, 57 (step 2,619), 210,273,201.

**The third epoch, computed exactly** (`py/epoch.py 210273201 22`, 35 s with gmpy2): 140,180,848 macro steps, the
number growing to 82 million bits; it ends at m = 1 with n ≡ 2 (mod 4), so the run does *not* halt there and a
fourth epoch starts with m = 3n/2 + 6, a number of 82,000,544 bits (about 24,684,623 decimal digits,
m mod 2^64 = 15369781771884450229).

How: the parities of t steps of `y ↦ ⌈3y/2⌉` depend only on `y mod 2^t`, since
`f^s(2^L h + l) = 3^s 2^(L−s) h + f^s(l)` for s ≤ L. `py/fastwalk.py` iterates the low half, combines with a power
of 3, and recurses (O(M(T) log T)). It agrees with plain iteration on epochs up to m = 10^5; two block sizes agree.

## Status

* Trusted: the rules (`py/macro.py check`, all even 2 ≤ n < 60, m < 12, against direct simulation); the first
  three epochs (`py/macro.py epochs`, `py/epoch.py`).
* Lean (`lean/Blank.lean`): the halting configurations, no halt in 10^4 steps (kernel), 10^7 (`native_decide`).
* Heuristic: with fair-coin parities an epoch halts with probability 1/3, so the machine halts with probability 1,
  after about 10^(10^7.39) macro steps or more.
* Open: the fourth epoch's end.

## Next steps

Lean proofs of the macro rules (fill pass and the two end rules with symtm and induction, as in Antihydra's
`Macro.lean`); a Lean statement "halts iff the epoch game halts". Deciding the machine is out of reach.

## Pages

- [`pages/holdouts/1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA0LB_---0LC/explainer.html`](../../pages/holdouts/1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA0LB_---0LC/explainer.html)
- [`pages/holdouts/1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA0LB_---0LC/proof-status.html`](../../pages/holdouts/1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA0LB_---0LC/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA0LB_---0LC/lean/check.sh
python3 holdouts/1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA0LB_---0LC/py/macro.py check && python3 holdouts/1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA0LB_---0LC/py/macro.py epochs
pip install gmpy2; python3 holdouts/1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA0LB_---0LC/py/epoch.py 210273201 22
```
