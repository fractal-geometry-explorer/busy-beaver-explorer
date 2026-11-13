# 1RB0LC_1LC0RB_0LE0LD_1LC---_0RA1LF_1LA1LF

Group G08 (two-sided square-root growth). Whether it halts from blank tape is **open**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LC |
| B | 1LC | 0RB |
| C | 0LE | 0LD |
| D | 1LC | --- |
| E | 0RA | 1LF |
| F | 1LA | 1LF |

## What it does

Full sweeps over a tape with two regular parts. At the turns at the left end, writing `a = 0011` and `b = 010111`:

      445,663  0 0 1 b a^13 0 1^3 a^7 0 1^2 0 1^3 b^161 0 1^4 b^2 0 1
      495,569  0 0 1 a^5 0 1^3 a^13 0 1 0 1^2 a^2 0 1^3 a^2 b^170 0 1^4 b^2 0 1
    2,965,211  0 0 1 a^22 0 1^3 a^18 0 1^2 0 1^3 b^442 0 1^4 b^2 0 1

The run `b^n` is the bulk of the tape; it gains one copy on most round trips (198 of the first 227 trips; 23 gain
two, 6 none). The left part of `a`-blocks and separators (`b`, `0 1^3`, `0 1^2`, `0 1 0 1^2`) is rewritten on each
trip like the low digits of a counter.

Later the left part stays a few runs (`(0011)^n`, `(0110)^n`, `(1100)^n` and `(1001)^n`, the same word rotated as the
sweeps shift it) with counts in the hundreds. At step 1,982,205,406 the tape at the left-end turn is
`C> (01)^4 (1100)^20 1 1 0 1 0 1^3 (0011)^111 0 1 (0110)^21 1^3 (0011)^71 0 1^3 (0011)^4 (010111)^12563 0 1^4 0 1 0 1^3 0 1 0 1^3 0 1`.
Sampled every 400 new left-end cells, one count moves by about 50 while b gains about 100 copies
(`py/turns.py` prints the same tapes).

Passes (all proved for any n): B moving right turns `0 0 (011101)^n` into `(010001)^n 0 0` (`pass_right_b`) and
`0 0 (1001)^n` into `(1010)^n 0 0` (`pass_right_a`); moving left, C turns `(000101)^n C> 0` into `C> 0 (101110)^n`
(`pass_left_b`) and E turns `(1010)^n E> 1` into `E> 1 (0011)^n` (`pass_left_a`).

The only halt is D reading a 1, and D is entered only from C reading a 1: `1 C> 1` halts (`halt_C`). In the run C
reads a 1 only as `100[1]111` (`py/near_halt.py`).

## What is proved, and where

- `lean/Blank.lean` (generated): the halting configurations; no halt in 10⁴ steps (kernel) and 10⁷ (`native_decide`).
- `lean/Rules.lean` (kernel, written by `py/rules.py`): the four passes for any n; `halt_C`.
- `lean/Route.lean` (kernel, written by `py/route.py`): `halt_route`, every configuration two steps before a
  halt is `1 1 A> 1`, `1 1 B> 0` or `1 1 D> 0`.
- `py/turns.py`, `py/near_halt.py` (heuristic): the tape as words at the end turns; what C sees when it reads a 1.

## What is open, next steps

The rule by which one round trip rewrites the left part (a counter whose digits are runs of `a`, with counts that
keep growing) and when it hands a `b` to the right part. Then an invariant that keeps a 0 to the left of C whenever
C reads a 1. Window-based closed tape languages (`tools/py/bbtools/ctl.py`, windows of 3 to 7 cells) find no closed
set. The template certificate of `1RB0LF_1LC0LA_1RA0RD_---1RE_1LA1RC_0LB0RC` (a finite table of round trips with two
linear counts) would need the counter's regimes first: here at least four counts on the left change together.

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LC_1LC0RB_0LE0LD_1LC---_0RA1LF_1LA1LF/lean/check.sh
python3 holdouts/1RB0LC_1LC0RB_0LE0LD_1LC---_0RA1LF_1LA1LF/py/route.py        # rewrites lean/Route.lean
python3 holdouts/1RB0LC_1LC0RB_0LE0LD_1LC---_0RA1LF_1LA1LF/py/rules.py      # rewrites lean/Rules.lean
python3 holdouts/1RB0LC_1LC0RB_0LE0LD_1LC---_0RA1LF_1LA1LF/py/turns.py 3e6 L  # the tape at the left-end turns
python3 holdouts/1RB0LC_1LC0RB_0LE0LD_1LC---_0RA1LF_1LA1LF/py/near_halt.py 1e6
```
