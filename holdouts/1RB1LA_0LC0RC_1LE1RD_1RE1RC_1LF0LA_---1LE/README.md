# 1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE

bbchallenge id 31371. One of the six-state holdouts. Analyzed by hand (group G02).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LA |
| B | 0LC | 0RC |
| C | 1LE | 1RD |
| D | 1RE | 1RC |
| E | 1LF | 0LA |
| F | --- | 1LE |

## What it does

Sample: the head in A at the left end of the tape on a blank cell. The tape is then always

    K(p, q) = 0^inf A> 0 1^p 0 1^q 0^inf

From blank tape: K(0,2) (step 7), K(2,1), K(4,1), K(7,1), K(2,7), K(10,1), K(16,1), K(25,1), K(11,16), K(4,24),
K(30,1), ..., K(241,1), K(119,124), K(58,186), K(273,1), ...

The map (all proved in Lean, with exact step counts):

    p = 2k+3 (odd):  K(p, q) -> K((p-3)/2, q + (p+5)/2)   in 2k^2 + 10k + 13 steps            (K_odd)
    p = 2k+2 (even): K(p, q) -> K(3p/2 + q, 1)            in q(4k+8) + 6k^2 + 22k + 15 steps   (K_even)
    p = 0:           K(0, q+1) -> K(2, q)                 in 7 steps                           (K_zero)
    p = 1:           halts                                                                     (K_one_halts)

Odd p: each pass (`inner_odd`) moves the 0 after the first block two cells left and adds a 1 on each side. Even p:
each pass (`inner_even`) shifts the first block one cell right, eating one 1 of the second block; once the second
block is gone, the block is taken apart at the blank end (`end_loop`): each round (`end_even` + two `inner_even`
passes) moves two of its ones past the end and adds three ones on its left, so 2m ones become 3m; `end_fin` walks
back to the left end.

## Halting

**Proved reduction** (`lean/Reduction.lean`). Let F be the map above (with F(1, q) = (1, q)), orbit n = F^n(0, 2)
and time n the step count (time 0 = 7). Then blank tape is at K(orbit n) at step time n (`reach`), and

* `halts_iff`: the machine halts from blank tape iff some orbit n has p = 1;
* `halts_iff_pow2`: iff some orbit n has q = 1 and p + 3 a power of two (u = p + 3 is halved by the odd rule, and
  every run of odd values starts at a sample K(p, 1));
* `halt_time_kernel` (`lean/LowerBound.lean`): if it halts, it runs more than 2^2073 steps (kernel evaluation of
  time 5000); `halt_time_native`: more than 2^80181 (time 200000, `native_decide`).

Checked: 200,000 iterations (`py/kmap.py 200000`, p of 40,089 bits) never hit a power of two. Heuristically (p near
X is 3 below a power of two with probability ~1/X, and p grows geometrically) it never halts. n-gram CPS (widths
3..7) fails.

## Lean

* `lean/Rules.lean` (from `py/rules.py`): `start`, `inner_odd`, `inner_even`, `end_odd0`, `end_odd`, `end_zero`,
  `end_even`, `end_even0`, `end_fin`.
* `lean/Macro.lean`: `K`, `odd_iter`, `K_odd`, `even_iter`, `end_loop`, `K_even`, `K_zero`, `K_one_halts`, `blank_K`.
* `lean/Reduction.lean`: `F`, `T`, `orbit`, `time`, `K_step`, `reach`, `halts_iff`, `halts_iff_pow2`,
  `time_lt_of_halts`.
* `lean/LowerBound.lean`: `go` (orbit and time in one pass), `halt_time_kernel`, `halt_time_native`.

## Notes for later

* The halting question is now exactly the number-theoretic one above; settling it would need a 2-adic / Collatz-type
  argument about the orbit of (0, 2).
* The kernel evaluation of the step count is fast up to 5,000 samples and much slower at 10,000.

## Pages

- [`pages/holdouts/1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE/explainer.html`](../../pages/holdouts/1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE/explainer.html)
- [`pages/holdouts/1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE/proof-status.html`](../../pages/holdouts/1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE/lean/check.sh
```
