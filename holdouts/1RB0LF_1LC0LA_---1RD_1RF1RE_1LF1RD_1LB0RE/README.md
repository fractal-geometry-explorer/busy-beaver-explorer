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

## The engine (17 November 2026)

`c/engine.c` follows the run pass by pass (one pass per new leftmost cell). To 10^10 steps (47,331 passes):

- the tape at the left end is always `0 (011)^4 (1011011011)^k I`; k grew 6,777 times and shrank once (pass 255,
  52 to 51), and is 6,776 at the end: one block about every 7 passes;
- the rest I (the *engine*) stays between 126 and 520 cells after pass 100, and no engine, taken with its offset mod
  10 against the blocks, occurs twice;
- the first 33 to 70 cells of I are a 7-periodic *emitter*: from pass 300 on, I agrees with I seven passes earlier on
  at least its first 33 cells (usually 53 to 70); each period it hands one block to the left part. Right of it the
  engine looks random;
- 20 cells inside the block region the pass is always the same: the head crosses right once in D and left once in A
  (47,031 passes).

So the engine does not see k, and the run with one block more (the partner, `lean/Insert_1RB1RF1LC0RF1.lean`) has
the same engine forever unless the engine eats back through the blocks. `GoodPair` is exactly the claim that it never
does.

**No argument about the left part alone can prove that** (`py/shield.py`). Put a boundary at the end of the blocks,
or 30 cells into the emitter, take the contents the real run has there, and let an adversary send the head across
the boundary in any state a left move can enter (A, B, C, F). The set of reachable contents keeps growing (over
3,000), about 200 visits reach the left end in irregular ways, and over 1,000 halt. So a proof of `GoodPair` needs a
description of the engine, which is the open part of this machine: whatever settles `GoodPair` very likely also
settles halting.

## What is open, next steps

A description of the engine: how it keeps its size and why the emitter sends one block every 7 passes. Either an
exact rule for that, or a closed set of patterns for the engine (a CTL whose left part is the regular language
`0 (011)^4 (1011011011)^*`).

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LF_1LC0LA_---1RD_1RF1RE_1LF1RD_1LB0RE/lean/check.sh
python3 holdouts/1RB0LF_1LC0LA_---1RD_1RF1RE_1LF1RD_1LB0RE/py/route.py        # rewrites lean/Route.lean
python3 holdouts/1RB0LF_1LC0LA_---1RD_1RF1RE_1LF1RD_1LB0RE/py/rules.py              # rewrites lean/Rules.lean
python3 holdouts/1RB0LF_1LC0LA_---1RD_1RF1RE_1LF1RD_1LB0RE/py/shape.py 2.5e7 L 100 200
python3 holdouts/1RB0LF_1LC0LA_---1RD_1RF1RE_1LF1RD_1LB0RE/py/near_halt.py 1e6
gcc -O2 -o engine holdouts/1RB0LF_1LC0LA_---1RD_1RF1RE_1LF1RD_1LB0RE/c/engine.c && ./engine 1e10 20
python3 holdouts/1RB0LF_1LC0LA_---1RD_1RF1RE_1LF1RD_1LB0RE/py/shield.py 30 3e7 3000
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB1RF_1LC0RF_1LE0LD_1RC0LB_---1RA_1LB1RA`](../1RB1RF_1LC0RF_1LE0LD_1RC0LB_---1RA_1LB1RA/README.md): rename A→D, B→C, C→E, D→A, E→F, F→B; it is this table started in state D

<!-- end of related machines -->
