# 1RB0RE_1LC0RA_1RF0RD_---1LE_0LB1LE_1LE1RC

bbchallenge id 127123. One of the six-state holdouts whose halting from blank tape is open (group G10). Family: **nested two-region bouncer (reset counter)**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RE |
| B | 1LC | 0RA |
| C | 1RF | 0RD |
| D | --- | 1LE |
| E | 0LB | 1LE |
| F | 1LE | 1RC |

## What it does

The core is a bouncer like 1RB0RB_1LC0LF_1RD0LB_1RE1RC_0RA---_1LA1RE: at the moments B is at the right end, the right
part of the tape is `1^x (10)^y 11` and one sweep takes two 1s and makes two `10` pairs:

    step 503,718,533   B  1^15760 (10)^619   11
    step 505,375,133   B  1^15160 (10)^1219  11
    step 905,614,293   B  (10)^16379 11            (the 1s are gone)
    step 1,442,420,983 B  1^32736 (10)^25 1^5 (10) 11

A reset rebuilds the 1s, about doubling the size. Around it sits a second level: from about 5·10^9 steps the tape is
`1^10 (10)^C 1^x (10)^y 11`, and every inner reset lowers C by an amount that grows by one each time:

    step  5,388,955,705   1^10 (10)^32666 1^9017  (10)^3265 11
    step  5,914,825,403   1^10 (10)^32652 1^21563 (10)^3007 11
    step  8,023,920,293   1^10 (10)^32637 1^46683 (10)^2463 11
    step 16,472,509,399   1^10 (10)^32621 1^96953 (10)^1345 11

With C = 32,751 the outer block lasts about 250 inner resets, each doubling the inner part: the next outer event is
about 2^250 steps away. Earlier, smaller outer blocks (64 and 13 pairs, `1^176 (10)^c ...` before 10^8 steps) ran out
the same way. A two-level counter: the run time explodes like a tower of doublings.

## Status

Proved in Lean (kernel):

- `lean/Edge.lean` (with `lean/EdgeCert.lean`, a closed tape language of windows of 4 cells from `bbtools.ctl`):
  every halt from blank tape is in state D with blank tape from the head on (`halt_at_edge`, `halts_iff_edge`);
  past the head, two 0s in a row occur only in the blank region (`right_no_double_zero`).
- `lean/Leaves.lean` (7 leaf rules by `bbtools.symtm.prove`, `py/gen_leaves.py`) and `lean/Top.lean` (by hand),
  with `P(x, y) = L 0 1^x 0 (10)^y 1 B>` and `D(m, c) = C> 0 (10)^m 1^c ...` at the left end:
  - `p_sweeps`: `P(x + 2b, y) -> P(x, y + 2b)` whatever `L` is (the bouncer works inside any context);
  - `top_reset`: with blank tape on the left, `P(1, y+2) -> D(1, 2y+12)`;
  - `round`: one doubling round `D(m, c+2m+6) -> D(2m+3, c+2)` (left block 1, 5, 13, 29, 61, ... = 2^(r+2) - 3),
    `rounds` / `reset_rounds`: any number of them; `rUse_closed`: r rounds from m use `2^(r+1)(m+3) - 2r - 2(m+3)` ones;
  - `d_halt`, **`reset_halts`**: a top-level reset `P(1, y)` halts for every `y = 2^j - j - 5` (j >= 4): after
    j - 2 rounds exactly two 1s are left and D runs onto blank tape. (`P(1, y) = (10)^(y+1) 1 B>` is the tank
    `(10)^y 11` with B on its last cell two steps later.)
- `lean/Level2.lean` (5 leaf rules in `lean/Level2Leaves.lean`, by `py/gen_level2.py`), with
  `K(C, y) = L (10)^C 0 (10)^y 1 B>` (an inner empty tank) and `G(C, u, k, c) = L (10)^C 1^u 0 A> 0 (10)^k 1^c`:
  - `round_end`: a top-level round D(q+j+1, 2j+6) that is too short leaves the outer stock `1^(2q+1)` and reaches
    `K(2j, 7)` (via `top_end`): the second level starts;
  - `g_entry` K(C+2, y) → G(C, 0, 0, 2y+7); `g_step` G(C, u+2, k, c+3) → G(C, u, k+2, c+1); `g_end`
    G(C+1, 0, k, c+5) → G(C, 2k+6, 0, c+1) (an inner round uses one outer pair); `g_term` G(C+1, u, k, 1) → the
    bouncer P(u, k+1), which sweeps to K(C+1, k+1+u);
  - **`inner_reset`**: the inner reset as a Lean function, `innerMap C y = some (C', y')` → K(C, y) reaches
    K(C', y'), for every tape on the left. `none` only when the outer block is too short (the outer event) or an
    inner round starts with exactly three 1s on the right (more nesting); both are not covered;
  - `tank_16379`, `tank_8187`: from the run's top-level tanks, the whole reset and the first inner resets
    (tanks 7, 19, 43, 91, 187; outer block 24, 20, 15, 9, 2 for 16379). The outer block drops by 2 + (number of
    inner rounds) per inner reset: 4, 5, 6, 7, ..., the slowly growing decrement seen in the run.
- `lean/Rules.lean`: three one-sweep rules from `bbtools.cycles` (`py/gen_rules.py`).

Trusted (direct simulation, `c/hscan.c`): from `(10)^y 11` on blank tape the machine halts for
y = 2^j - j - 5 (j = 4..11) and y = 12, and for no other y < 2500 within 3y² + 10^5 steps. The top-level empty
tanks of the run from blank tape were y = 8187 = 2^13 - 5 and y = 16379 = 2^14 - 5: by the round count above they
leave 2j + 2 ones after j - 2 rounds instead of 2 (a near miss by exactly j), and those ones start the second level.

Heuristic: the two-level structure above (read off the run to 2·10^10 steps); its inner resets are now the Lean
function `innerMap`, checked against plain runs as well (`(C, y) = (30, 40), (50, 333), (60, 1000)`, ...). Open: halting.

## For later

- Done: the end of the top-level rounds and the inner reset map (`lean/Level2.lean`). Next: the outer event (an inner
  round with no outer pair left: `0^inf 1^P 0 0 A> 0 1^c` returns to a top-level bouncer `1^x 0 (10)^y 1 B>`, by
  plain runs), the inner round with exactly three 1s, and the top-level reset from an even tank (x = 0); then the
  whole two-level map, and whether D can ever reach the right edge.
- Simulating to the next outer event is out of reach (about 2^250 steps); an argument has to be symbolic.
- Explain the near miss: top-level tanks at y = 2^j - 5 against halting values 2^j - j - 5. If the inner resets
  in the outer context also land at a fixed offset from their halting values, that would be the nonhalting argument.

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RE_1LC0RA_1RF0RD_---1LE_0LB1LE_1LE1RC/lean/check.sh
python3 holdouts/1RB0RE_1LC0RA_1RF0RD_---1LE_0LB1LE_1LE1RC/py/gen_level2.py H127123 > holdouts/1RB0RE_1LC0RA_1RF0RD_---1LE_0LB1LE_1LE1RC/lean/Level2Leaves.lean
```

## Pages

- [`pages/holdouts/1RB0RE_1LC0RA_1RF0RD_---1LE_0LB1LE_1LE1RC/explainer.html`](../../pages/holdouts/1RB0RE_1LC0RA_1RF0RD_---1LE_0LB1LE_1LE1RC/explainer.html)
- [`pages/holdouts/1RB0RE_1LC0RA_1RF0RD_---1LE_0LB1LE_1LE1RC/proof-status.html`](../../pages/holdouts/1RB0RE_1LC0RA_1RF0RD_---1LE_0LB1LE_1LE1RC/proof-status.html)
