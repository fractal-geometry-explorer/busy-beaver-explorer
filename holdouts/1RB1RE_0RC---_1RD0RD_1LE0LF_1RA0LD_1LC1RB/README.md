# 1RB1RE_0RC---_1RD0RD_1LE0LF_1RA0LD_1LC1RB

bbchallenge id 8002. One mechanism, a drain, run at every scale: a block of 1s is drained two cells per sweep into pairs `01`; next to a block `0 (10)^c 1` the same sweep becomes the round of a ternary counter; a drain that ends with the wrong parity wipes its own block of 1s into a gap of 0s, and the run starts again from scratch inside the gap. It halts only if a drain ends exactly three cells short of the block to its right.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RE |
| B | 0RC | --- |
| C | 1RD | 0RD |
| D | 1LE | 0LF |
| E | 1RA | 0LD |
| F | 1LC | 1RB |

## What it does

Everything the machine does is one move, the **drain sweep**, applied to a few macro configurations. The left end of
the tape is blank; reading from the left:

| name | tape | |
|---|---|---|
| D(A,B) | `1^A (01)^B 0 C> 0 Z` | the drain, head at its right end in C |
| P(A,B) | `1^A (01)^B 1 1 1 0 C> 0 Z` | the parity tail |
| T(n) | `E> (01)^n Z` | the head at the left end in E |

Z, the **environment**, is everything to the right: a row of blocks `0^g (10)^c 1`, then blank tape. Two steps from
blank tape the run is at S = D(1,0) = `1 0 C> 0` with an empty environment.

The rules (all in `lean/Macro.lean` and `lean/Halt.lean`, proved for every count and every tape around them):

- **Sweep** (`m_sweep`, iterated in `drain`): D(A+2,B) → D(A,B+2) for A ≥ 1, if the head has a 0 to its right. Each
  round trip bites two 1s off the block and turns them into a pair; the tape grows by two cells. This is the
  square-root growth of the right side.
- **Odd sweep** (`m_odd`, iterated in `odd_drain`): next to a block `0 (10)^c 1` (one 0 between), D(A+2,B) → D(A,B+3)
  and the block loses two pairs. This is the round of the **ternary step** proved earlier (`ternary`): T(n) next to
  `(10)^y 1` becomes D(2n−1,0) next to `0 (10)^(y−1) 1` (`m_tseg`), n−1 odd sweeps make D(1,3n−3), and D(1,B) → T(B+3)
  (`m_end1`) closes the round at T(3n). From blank tape: n = 3, 9, 27, 81, 243, … while the block lasts.
- **Ends of a drain**: D(1,B) → T(B+3) (`m_end1`); D(2,B) → S with a new block `0 (10)^(B+1) 1` in front of the
  environment (`m_end2`); T(n) next to at least five 0s → D(2n+2,0) (`m_tblank`).
- **Ends of a block**: a drain at a block two 0s away merges it (`m_absorb`); an odd sweep that uses up its block
  ends in D (`m_odd_end1`, last pair) or in the parity tail P (`m_odd_end0`, no pair left).
- **Parity tail**: P(A,2k) → D(A−1,2k+4) (`m_peven`). P(A,2k+1) → S followed by a **gap** `0^(A+1)` and the block
  `(10)^(2k+3) 1` (`m_podd`): the block of 1s is wiped out and a fresh run starts inside the gap.

A fresh run inside a gap does exactly what the run from blank tape does, until its right end reaches the block
after the gap; then the block is absorbed (or eaten by odd sweeps) and the larger drain goes on. So the whole run is
self-similar: the run from blank tape, with copies of its own beginning nested in the gaps it makes. In the first
10<sup>12</sup> steps the top level makes gaps of 392, 320, 124, 348 (all by step 2.1·10<sup>8</sup>), 22,456
(step 4.2·10<sup>9</sup>), 36,678 (5.5·10<sup>9</sup>) and 60,524 (10<sup>12</sup>) zeros; inside each of the
three large gaps the copy makes its own gaps of 392, 320, 124, 348, as the run from blank tape did. The macro
simulator runs the first 1.0008·10<sup>12</sup> steps without a halt (in minutes; it then reaches a small case
it hands to the slow plain run).

`py/drain.py` is a macro simulator built on these rules (with the exact step count, and a plain run for the few small
cases no rule covers); `py/drain.py check 5e6` compares it with a plain run cell for cell at all 310 macro
configurations up to step 5,265,516.

## The run as one map (Lean)

`lean/Chain.lean` chains the rules into one map. A node is `d A B e`, `p A B e` or `t n e` (D(A,B), P(A,B), T(n)),
with the environment e a list of blocks `(g, c)` = `0^g (10)^c 1`. `F : Node → Res` makes one macro move and
returns the next node, `halt`, or `stuck` (a case no rule covers). Its cases are the rules above one sweep at a
time, the two halting cases (`tail_halts` as `r_tail_halt`, `halt_001` as `r_thalt`), and four new rules for a block
that follows another with no gap, the small cases `py/drain.py` ran cell by cell (`lean/Fallback.lean`, written
by `py/chain_rules.py`):

- `f_oe1z`: an odd sweep that uses up its last pair `0 (10) 1` with a block `(10)^c 1` right after it:
  D(A+3,B) → D(A+1,B+c+4);
- `f_ab_z`: a drain at `0 0 (10)^c 1` followed directly by `(10)^(d+2) 1`: D(A+3,B) → D(A+1,B+c+4) next to
  `0 (10)^d 1`;
- `f_oe0z_odd`, `f_oe0z_even`: an odd sweep at `0 1` followed directly by `(10)^(c+1) 1`. With B = 2k+1 the block of
  1s is wiped: S next to `0^(A−1) (10)^(2k+3) 1 (10)^c 1`; with B = 2k, D(A+2,0) next to `0 0 (10)^(2k+1) 1 (10)^c 1`.

Outputs are normalized (a block after a single 0 is merged into the block before it, `canon`; T absorbs a first
block with a single 0, `mkT`). Proved (kernel, standard axioms):

- `F_sem`: a move to a node is a run of at least one step; a move to `halt` is a halting configuration;
- `halts_of_orbit`, `not_halts_of_orbit`, and the main theorem `halts_iff_of_no_stuck`: **if the orbit of the start
  `d 1 0 []` never gets stuck, the machine halts from blank tape iff the orbit reaches `halt`**;
- `orbit_kernel` (20,000 nodes, kernel) and `orbit_native` (3·10<sup>7</sup> nodes, compiled): no halt and no stuck
  node. Node 3·10<sup>7</sup> is D(7,667,001, 2,848,404) next to `0 (10)^7,629,577 1`. Adding up the step counts
  of the rules along the orbit (a Python copy of `F`, which agrees with Lean's evaluation) gives at least
  5.2·10<sup>14</sup> steps for these nodes, far past the 10<sup>12</sup> of `py/drain.py`.

`lean/Hybrid.lean` (12 November) removes the hypothesis from the statement: the hybrid map `hstep` is `F` where `F`
is defined and a single machine step (on the configuration written out as two lists) where it is `stuck`.
**`halts_iff_hybrid`: the machine halts from blank tape iff the hybrid orbit of `d 1 0 []` reaches `halt`, with no
hypothesis**; `hrun_of_orbit`: while the orbit of `F` is not stuck the hybrid orbit is the orbit of `F` (so for the
first 3·10<sup>7</sup> nodes, by `orbit_native`). The fallback explains nothing about the uncovered nodes.

Not proved: that the orbit never gets stuck. On 3,000 random small nodes the machine agrees with `F` wherever `F` has
a rule (2,124 nodes), and from the 876 nodes without a rule it always reaches another node of the three shapes (or
halts, 5 times): the map could be completed by more rules, but the uncovered nodes fall into several hundred classes. The stuck cases are small environments (a block right after a block
in a few configurations, a T next to three or four 0s, and so on) that the orbit has not met so far.

## How it could halt

The machine halts only when B reads a 1 (`step_none_iff`). B is entered from A0 or from F1, and F1 leaves B on
the 0 that D has just written, so the last three steps before a halt are always E, A, B reading 0, 0, 1 (by
inspection of the table): E running right over pairs `01` into `0 0 1`, which does halt (`halt_001`). In the drain picture there are two ways to get there, both proved for all
parameters:

- `drain_halts`: an odd drain D(2k+1,B) whose next 1 is exactly 2k+3 zeros past the head cell. After k sweeps it is
  D(1,B+2k), T(B+2k+3) starts, and E meets `0 0 1`.
- `tail_halts`: an odd sweep that uses up a block `0 (10)^(2k) 1` followed by exactly three 0s: the parity tail has
  no room.

Neither can happen at the top level, where the environment is blank. It can happen inside a gap. Started in a gap of
G zeros (S followed by `0^G (10)^c 1`), the fresh run halts before it reaches the block exactly for

    G = 3, 29, 75, 115, 289, 623, 716, 773, 1045, 1210, 3392     (all G ≤ 5000; c = 0…9 and 143 give the same set)

(`c/gapscan.c`, a plain run for each G; `py/drain.py gaps` gives the same list and says which of the two ways each
one takes). G = 3 is `start_halts_gap3` in Lean. Each G in the list is a moment where the run from blank tape has a
drain ending, or an odd sweep running out, at distance G from its start: the run halts if and only if one of the gaps
it makes has a sensitive size of a run started from scratch. The gaps made so far (392, 320, 124, 348, 22,456, 36,678, 60,524) miss the
list (the large ones are beyond the scan, but the run went past the first two without halting). The sensitive sizes thin out (eleven below 5000) while the gaps grow roughly geometrically, so a hit
looks unlikely but nothing rules it out: deciding it means knowing two sequences produced by the same counter, which
is a Collatz-like question.

## Status

Open (Collatz-like). Proved in Lean (kernel): the halting configurations, no halt in 10^4 steps (10^7 native), all
the rules above for every size and every tape around them (`lean/Macro.lean`, generated by `py/macro_rules.py`), the
ternary step (`lean/Ternary.lean`), the iterated sweeps and both ways of halting (`lean/Halt.lean`). The rules
chained into one map, `F` (`lean/Chain.lean`, with four more rules in `lean/Fallback.lean`): if its orbit never
reaches a case no rule covers, the machine halts iff the orbit reaches `halt`; its first 3·10<sup>7</sup> nodes are
evaluated (2·10<sup>4</sup> by the kernel) with no halt and no such case, at least 5.2·10<sup>14</sup> steps (that
sum by a script). Not in Lean: that the orbit never gets stuck, the list of halting gap sizes, and the claim that the
gaps made by the run avoid it. CTL with windows of 2-5 cells and NGramCPS (widths 2-8,
history and LRU variants) fail, as they must: a halting configuration of the shape above has only short-range
patterns that occur in the run.

## For later

1. `halts_iff_hybrid` has no hypothesis, but only through a fallback to machine steps. A real completion: add rules
   for the stuck cases (hundreds of small classes; generate them), or show the orbit never meets one (an invariant
   on the environments it builds; T next to a gap of 3 or 4 is as delicate as the halting case, a gap of 2). A weighted version of
   `F_sem` would also put the step count in Lean.
2. Compute the sensitive gap sizes further with the macro simulator (`py/drain.py gaps`), describe them as a
   function of the counter, and compare with the gaps the run makes.

## Reproduce

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RE_0RC---_1RD0RD_1LE0LF_1RA0LD_1LC1RB/lean/check.sh
python3 holdouts/1RB1RE_0RC---_1RD0RD_1LE0LF_1RA0LD_1LC1RB/py/macro_rules.py           # rewrites lean/Macro.lean
python3 holdouts/1RB1RE_0RC---_1RD0RD_1LE0LF_1RA0LD_1LC1RB/py/chain_rules.py           # rewrites lean/Fallback.lean
python3 holdouts/1RB1RE_0RC---_1RD0RD_1LE0LF_1RA0LD_1LC1RB/py/drain.py check 5e6
python3 holdouts/1RB1RE_0RC---_1RD0RD_1LE0LF_1RA0LD_1LC1RB/py/drain.py run 1e12         # the gaps the run makes (minutes)
gcc -O2 -o gapscan holdouts/1RB1RE_0RC---_1RD0RD_1LE0LF_1RA0LD_1LC1RB/c/gapscan.c && ./gapscan 0 2500 3 2000000000 | grep HALT
./tmrun 1RB1RE_0RC---_1RD0RD_1LE0LF_1RA0LD_1LC1RB 3000000000 at E L 10000000 | python3 holdouts/1RB1RE_0RC---_1RD0RD_1LE0LF_1RA0LD_1LC1RB/py/check_ternary.py
```

## Pages

- [`pages/holdouts/1RB1RE_0RC---_1RD0RD_1LE0LF_1RA0LD_1LC1RB/explainer.html`](../../pages/holdouts/1RB1RE_0RC---_1RD0RD_1LE0LF_1RA0LD_1LC1RB/explainer.html)
- [`pages/holdouts/1RB1RE_0RC---_1RD0RD_1LE0LF_1RA0LD_1LC1RB/proof-status.html`](../../pages/holdouts/1RB1RE_0RC---_1RD0RD_1LE0LF_1RA0LD_1LC1RB/proof-status.html)
