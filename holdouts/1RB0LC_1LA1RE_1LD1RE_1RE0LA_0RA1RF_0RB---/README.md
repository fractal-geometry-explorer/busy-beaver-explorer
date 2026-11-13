# 1RB0LC_1LA1RE_1LD1RE_1RE0LA_0RA1RF_0RB---

bbchallenge id 162473. Group G01. **A 3/2-Collatz map with parity-triggered nested phases**, analysis only begun. Open.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LC |
| B | 1LA | 1RE |
| C | 1LD | 1RE |
| D | 1RE | 0LA |
| E | 0RA | 1RF |
| F | 0RB | --- |

## What it does

Sample the run when the head is in state C at the left end of the tape. The tape is then mostly

    X(n, t) = C> 000 (100)^n T        Y(n, t) = C> (100)^n T          T = 1 (t = 0) or 101 (t = 1)

with the single-number rules

    X(n, t), n odd   ->  X((3n+5)/2, t')        X(n, t), n even  ->  Y((3n+6)/2, t')     t' = t xor [n mod 4 in {0, 1}]
    Y(n, t), n even  ->  X((3n+4)/2, t')        (through Z(n) = C> 00 11 (001)^n T')    t' = t xor [n mod 4 = 0]

From blank tape: Y(2) at step 58, X(5), X(10), Y(18), X(29), X(46), Y(72), X(110), Y(168), X(254), Y(384), X(578),
Y(870), X(1307), …, X(9958), Y(14940), X(22412), Y(33621) at step 6.1·10⁹.

**Nested phases.** Y(n) with n odd starts a phase with a second number. Y(33621) went to
`C> 00 11 (001)^33621 01`, then `C> 000 (10)^2 (010)^50433 1` (y = (3n+3)/2), then `C> (100)^3 (010)^50432 01`, then
`C> 00 11 (001)^2 0 11 (001)^50432`. Because 50432 is even, the phase ended at X(75654) = X(3·50432/2 + 6) at step
3.1·10¹⁰. When the second number is odd as well, the phase nests deeper. From Y(3), for example, the run goes through
`C> 00 11 (001)^2 0 11 (001)^5 01`, `C> 000 (100)^4 (10)^2 (010)^8 1`, `C> (100)^9 (010)^5 01`, … before it comes
back to X(22). Whether the second number goes to y − 1 or y + 1 depends on the tail.

In the single-number regime Y(n) gets an odd n when the X before it has n ≡ 0 (mod 4), so about one Y-event in two
starts a nested phase. The halting transition (F1) must be reached inside a nested phase, if at all. The rules of
these phases are not yet written down, so neither the halting condition nor a heuristic is available yet.

## Nested phases, closed forms (second pass)

From Y(n, t) with n odd, the next single-number event (`py/nested.py`, C helper `c/single.c`):

| n | next | left-end moments |
|---|---|---|
| 4i+1 | X(9i + 9, t xor [i odd]) | 5 |
| 8i+7 | X(27i + 36, t xor [i odd]) | 8 |
| 8i+3 | deeper (Y(3) → X(22), Y(11) → X(51), Y(27) → Y(119), …) | 9–13 |

9/4 = (3/2)² and 27/8 = (3/2)³: each level runs the 3/2 rule once more on the second number, and the depth is set by
the powers of 2 in the numbers met. Every odd n < 400, both tails, comes back to the single-number form without
halting. **Twins:** mirroring and renaming states gives `1RB1LC_1LA0RD_0LB1LF_1RE1LC_1LC0RB_0LA---` (G02) and `1RB1LC_1LC0RF_0LF1LD_0LE---_1RF1LC_1LE0RA` (G06), the same
machine with other start states.

## What is proved

| level | result | where |
|---|---|---|
| kernel | the halting configurations (F1); no halt in 10⁴ steps | `lean/Blank.lean` (generated) |
| native | no halt in 10⁷ steps | `lean/Blank.lean` |
| trusted | the single-number rules: all 21 applicable X/Y-events of the blank run up to 4·10¹⁰ steps | `py/emap.py blank 4e10` |
| trusted | no halt within 10⁸ steps from X(n, t) or Y(n, t), n < 40 | `py/emap.py search 40` |
| trusted | nested phases: n = 4i+1 and 8i+7 in closed form; every odd n < 400 returns, no halt | `py/nested.py 400` |

## Reproduce

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LC_1LA1RE_1LD1RE_1RE0LA_0RA1RF_0RB---/lean/check.sh
cd holdouts/1RB0LC_1LA1RE_1LD1RE_1RE0LA_0RA1RF_0RB---/py
python3 emap.py blank 4e10        # about 6 min
python3 emap.py search 40         # a few minutes
```

## Further work

More than a day. The next steps:

- Write the nested phase as a rule on a list of numbers (with the tail bits), check it against direct simulation, and
  iterate the whole map.
- Find which nested configurations read F1 (halt), and estimate the halting chance.
- Compare with `1RB0LA_0RC1RD_0LD1RE_1LA0RF_0RD0LD_1RD---`, which has a similar single-number regime (X(n) → Y →
  X((9n+16)/4)) with block lists built from `(10)` and `(010)` when a parity test fails.

## Third pass

The macro simulator `c/msim.c` (a copy of the one in holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---, in
`../1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA/c/`; blocks of 6 cells; checked against the direct simulator at 10⁹ steps by `check_msim.py check`) runs
10¹⁸ steps from blank tape without a halt: `python3 ../1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA/py/check_msim.py run 1RB0LC_1LA1RE_1LD1RE_1RE0LA_0RA1RF_0RB--- 1e18` (2 to 5 minutes).
Direct simulation of every C-event at the left end to 3.1·10¹¹ steps (48 events) stays in the single-number forms
`C> 000 (100)^n T`, `C> (100)^n T`, `C> 001 (100)^n T` (n = 27, 43, 67, 103, 157, 238, 360, 542, 816, 1226, 1842,
2765, 4150, 6228, 9344, 14019, …, 106494, 159744, 239618) except for one nested phase, which passes through the
two-run lists `C> (100)^120 0 (100)^47208 101` and `C> 001 (100)^119 101 (100)^47208 101` (runs of `100` with
separators, as in the list form of 1RB0LC_1RC1RF_1LD0RA_1LE0LD_1RC0LA_0LA---).

No pushdown certificate with a small DFA exists: the reduction of `bb6-1RB0LF_1RC0LB/c/pds.c` (one side of the tape
exact, the other a DFA, post* saturation) reaches a halt for every DFA with at most 6 states, on either side
(`TM=1RB0LC_1LA1RE_1LD1RE_1RE0LA_0RA1RF_0RB--- ./pds 6 L`, then `R`; 1.5 minutes each).

## Pages

- [`pages/holdouts/1RB0LC_1LA1RE_1LD1RE_1RE0LA_0RA1RF_0RB---/explainer.html`](../../pages/holdouts/1RB0LC_1LA1RE_1LD1RE_1RE0LA_0RA1RF_0RB---/explainer.html)
- [`pages/holdouts/1RB0LC_1LA1RE_1LD1RE_1RE0LA_0RA1RF_0RB---/proof-status.html`](../../pages/holdouts/1RB0LC_1LA1RE_1LD1RE_1RE0LA_0RA1RF_0RB---/proof-status.html)
