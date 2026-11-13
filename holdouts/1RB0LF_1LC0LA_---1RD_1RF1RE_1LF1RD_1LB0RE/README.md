# 1RB0LF_1LC0LA_---1RD_1RF1RE_1LF1RD_1LB0RE

Group G08 (two-sided square-root growth). Whether it halts from blank tape is **open**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LF |
| B | 1LC | 0LA |
| C | --- | 1RD |
| D | 1RF | 1RE |
| E | 1LF | 1RD |
| F | 1LB | 0RE |

## What it does

Full sweeps. At the visits to the left end the tape is `0 (011)^4 (1011011011)^k` followed by an irregular region
with short runs of three-cell words, e.g. at step 1,160,914:

    [A]0 (011)^4 (1011011011)^72 (001)^3 (100)^4 (110)^3 0 111 0110010 (011)^3 10100110 111 ...

k grows steadily (21 at step 103,296; 172 at 6,990,882; 329 at 24,861,720) while the irregular rest stays between
156 and 426 cells (`py/shape.py 2.5e7 L 100`). All growth of the tape ends up in the regular part.

Passes (proved for any n): E moving right turns `(1101101101)^n` into `(1011110110)^n` (`pass_right`, 12 steps a
copy); A moving left turns it back, one cell shifted (`pass_left`, 50 steps a copy); D turns `(011)^n` into
`(101)^n` (`cross_D`); B moving left turns `(101)^n` into `(100)^n` (`cross_B`).

The only halt is C reading a 0; C is entered only from B reading a 0, so `0 B> 0` halts (`halt_B`). In the run B
reads a 0 only with a 1 to its left.

## What is proved, and where

- `lean/Blank.lean` (generated): the halting configurations; no halt in 10⁴ steps (kernel) and 10⁷ (`native_decide`).
- `lean/Rules.lean` (kernel, written by `py/rules.py`): the four passes; `halt_B`.
- `lean/Route.lean` (kernel, written by `py/route.py`): `halt_route`, every configuration two steps before a
  halt is `0 0 F> 0`.
- `py/shape.py`, `py/near_halt.py` (heuristic): compressed tapes at the end visits; neighbourhoods of B and C.

## What is open, next steps

A description of the irregular region: how it keeps its size and hands copies of `1011011011` to the left part.
Either an exact rule for that, or a closed set of patterns for the region (a CTL whose left part is the regular
language `0 (011)^4 (1011011011)^*`).

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LF_1LC0LA_---1RD_1RF1RE_1LF1RD_1LB0RE/lean/check.sh
python3 holdouts/1RB0LF_1LC0LA_---1RD_1RF1RE_1LF1RD_1LB0RE/py/route.py        # rewrites lean/Route.lean
python3 holdouts/1RB0LF_1LC0LA_---1RD_1RF1RE_1LF1RD_1LB0RE/py/rules.py              # rewrites lean/Rules.lean
python3 holdouts/1RB0LF_1LC0LA_---1RD_1RF1RE_1LF1RD_1LB0RE/py/shape.py 2.5e7 L 100 200
python3 holdouts/1RB0LF_1LC0LA_---1RD_1RF1RE_1LF1RD_1LB0RE/py/near_halt.py 1e6
```
