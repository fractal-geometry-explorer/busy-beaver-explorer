# 1RB0RA_0RC0LE_0LD1RA_1LB0RF_0LD1LC_1RD---

bbchallenge id 29537, a six-state holdout of group G05 (growth class fixed/sqrt: the tape grows to the right like
the square root of the step count, the left end stays put). **Open.** The machine is a binary counter written in
blocks of `10`s: the digits are single cells between the blocks, and each increment uses up two `10`s of a
reservoir at the right end and lengthens the blocks next to the carry. The two basic increments are proved in Lean
for all block lengths; the full rule is checked against the simulator, and the run is followed to 2·10^11 steps
without a halt.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RA |
| B | 0RC | 0LE |
| C | 0LD | 1RA |
| D | 1LB | 0RF |
| E | 0LD | 1LC |
| F | 1RD | --- |

## The same counter as 1RB0LF_0LC0RE_0RA1LD_1LB0LD_0RA1RC_1LA--- (21 Nov)

This machine is the table of [`1RB0LF_0LC0RE_0RA1LD_1LB0LD_0RA1RC_1LA---`](../1RB0LF_0LC0RE_0RA1LD_1LB0LD_0RA1RC_1LA---/README.md) in a mirror, its states A to F renamed D, B, C, A, E, F. So
its run is that table's run from blank tape started in state D, and the deeper analysis of that folder applies here
cell for cell:

- **Lean, kernel** (`../1RB0LF_0LC0RE_0RA1LD_1LB0LD_0RA1RC_1LA---/lean/Twin29537.lean`): `twin_halts_iff`: this machine halts from blank tape iff
  1RB0LF_0LC0RE_0RA1LD_1LB0LD_0RA1RC_1LA--- halts from blank tape started in D; `twin_reach157`: that run is at a left record after 157 steps;
  `twin_halts_iff_record`: so this machine halts iff the table halts from that record.
- **Exact macro machine**: that folder's block macro machine (`py/blockmm.py`) reproduces this machine's run record for
  record from step 157: steps, head cell and blocks agree at all 15,228 records up to step 299,972,981
  (`../1RB0LF_0LC0RE_0RA1LD_1LB0LD_0RA1RC_1LA---/py/twin.py`). Its macro run finds no halt in 300,000 records (1.20·10^11 steps). The 56 right and
  175 left crossing rules it needs beyond that folder's own 387 are proved for all t and all tapes
  (`../1RB0LF_0LC0RE_0RA1LD_1LB0LD_0RA1RC_1LA---/lean/RulesTwin1.lean`, `RulesTwin2.lean`, kernel).
- **The tape, in that folder's words**: at each left record (in the mirror) the tape is
  `0^inf B> 0 (10)^D0 0 (10)^D1 x1 (10)^D2 x2 ...`, a countdown block D0 followed by a binary counter on blocks of
  `10`s. The digits, blocks and reservoir described below are the same tape read from the other end.
- **The countdown map, exactly**: at each reset (countdown used up) the long block X after it becomes the next
  countdown, and the next reset has X' = floor(3X/2) + 1 (X even) or floor(3X/2) + 3 (X odd). Here X runs 7, 13, 22, 34, 52, 79,
  121, 184, 277, 418, 628, 943, 1417, 2128, 3193, 4792, 7189, 10786, 16180, 24271 (all 19 transitions of the first
  3·10^9 steps follow the rule, and so do all 33 of the macro run to 2·10^7 records, 2.5·10^14 steps, with no halt;
  `../1RB0LF_0LC0RE_0RA1LD_1LB0LD_0RA1RC_1LA---/py/reset_map.py`). 1RB0LF_0LC0RE_0RA1LD_1LB0LD_0RA1RC_1LA--- is another orbit of the same map (142, 214, 322, ...).
- **What decides halting** (heuristic, checked): the tail of the counter, right of the countdown and the long block,
  is acted on by four operators whose sequence is fixed by that orbit: E0, E1 alternating inside each phase
  (2,965 of 2,965 increments of the first 6,000 records), then E1 O0 O1 or E1 at a reset as X is even or odd (13 of 14
  resets). See "The twin, and what the tail sees" in that folder's README. The tail is a mass of short blocks of
  different lengths (190 blocks at 3·10^9 steps, in the mirror: `... 2 o o 1 i 1 i 9 i 1 o 2 o 4 o o o 3 i 1`), which
  is why run-length engines find no long runs to compress.

The sections below are the first pass on this machine, read from the right end; they remain correct.

**The reset map, phase by phase (22 Nov).** Every tail excursion of the first 36 phases of this run is now checked in
Lean, by a run-length simulator proved for every tape on the left (`ExcSim.lean`, `ResetExc.lean` in the twin's folder):
`reach_twin_phases36` (`ResetExcLong.lean`, by hand) says that this table started in D reaches the reset with
X = 121,081,390 with no hypothesis, and `reach_twin_phases` (`ResetExcRuns.lean`, in CI) does 26 phases, X = 2,099,734.

## What it does

**The tape.** Write `a = 10`. Apart from a short fixed start, the tape is made of runs of `a`s separated by
single cells, and read from the right end it is

    ...  d_3 a^n_3  d_2 a^n_2  d_1 a^n_1   0 0   a^m   C> 0^∞

A separator cell `d` between two runs is a **digit**: `... 1 0 [0] 1 0 ...` is a 0, `... 1 0 [1] 1 0 ...` is a 1.
`d_1` is the lowest digit. The `0 0` after the last digit block is the **marker**, and `a^m` at the far right is
the **reservoir**. For example, at step 29,987,318 the tape ends in

    ... 0 a^190 1 a^34 1 a^66 0 a^1154 1 a^788 0 0 a^1603 C>0

(digits ..., 0, 1, 1, 0, 1, 0 from the top down to `d_1 = 0`; blocks 190, 34, 66, 1154, 788; reservoir 1603).

**One increment.** The head bounces between the right end and the low digits. The first bounce (`half_sweep`)
turns the marker `0 0` into `1 10 1`; the second turns it back and does the arithmetic. Together they add one to
the binary number `... d_3 d_2 d_1`:

    the low 1-digits become 0, the next 0-digit d_j becomes 1,
    n_j += 2,  n_1 += 2  (so n_1 += 4 when j = 1),  m -= 2

and nothing further left changes. Exactly, in Lean, for all lengths:

| rule | start (head in C on the blank cell) | end | steps |
|---|---|---|---|
| `half_sweep` | `L 1 0 0 (1010)^(n+2) 0 0 (1010)^(m+2) 10` | marker becomes `1 10 1` | 12m + 36 |
| `inc_d0` | the same | `d_1: 0→1`; `n_1: 2n+4 → 2n+8`; `m: 2m+5 → 2m+3` (in `a`s) | 24m + 12n + 122 |
| `inc_d1` | `L 1 0 0 (1010)^(a+2) 1 (1010)^(n+2) 0 0 (1010)^(m+2) 10` | `d_1: 1→0`, `d_2: 0→1`; `n_2: 2a+4 → 2a+6`, `n_1: 2n+4 → 2n+6`, `m − 2` | 12a + 24m + 12n + 152 |

(`L` is any tape; the blocks are written in `1010` words, the `10` after the reservoir makes its length odd, which
is what the run shows.) `py/check_increments.py 30000000` compares the general rule with a direct simulation: in
the first 3·10^7 steps, **2,282 increments match and none disagree**; 141 carries run into a block of odd length
(a higher separator, outside the rule as stated) and 17 times the reservoir is refilled.

**The emergent behaviour.** A binary counter whose digit blocks grow: every increment lengthens the lowest block
and the block of the digit that the carry stops at, so block `n_j` grows by 2 every `2^j` increments, and the cost of
a sweep (proportional to the tape length) grows as the counter runs. The reservoir does not last: when it runs
out, the machine refills it, and further right it builds a second region made of `1100` words
(`c = 1100`; at step 2·10^9 the tape ends `... a^9640 0 a^868 00 c^4376 11 c^4882 110`, about half the tape in
`c`s), which is later converted back into reservoir `a`s. Higher up, the separators are not all single cells
(`1101`, `0101`, `000`, ... appear between long blocks), so the counter has a second layer of structure that
these rules do not describe. Samples of the low end:

| step | low end of the tape |
|---|---|
| 3·10^8 | `a^54 1 a^108 0 a^3760 1 a^1298 1101 a^856 00 c^2733 110` |
| 6·10^8 | `0 a^464 1 a^930 1 a^5404 0 a^376 00 a^3211 c^3661 110` |
| 10^9 | `1 a^820 0 a^1638 1 a^6822 0 a^5375 c^1754 11 c^2431 110` |
| 1.4·10^9 | `a^48 1 a^94 1 a^8224 1 a^1130 1101 a^983 00 c^7221 110` |

**Where it could halt.** The only halting transition is F reading 1. F is entered from D reading 1 (`0RF`), and
D from C or E reading 0 (`0LD`) or from F reading 0 (`1RD`). Following these: the machine halts exactly when C or
E reads a 0 whose left neighbour is a 1 and the cells to its right are `(1 0)^k 1 1` for some k ≥ 0; if instead
they are `(1 0)^k 0`, D reads a 0 and the machine goes on in B. On this tape that means: C or E stands on the `0`
of an `a` whose run is ended, to the right, by a 1-digit (or by a `11` in the marker or a `c`). The increments
never do this (they are proved for all values); whether a refill, a long carry or the `c` region can is open.

## Status and evidence

**Lean, kernel** (`lean/Rules.lean`, generated by `py/gen_rules.py` with `bbtools.symtm`): `half_sweep`,
`inc_d0`, `inc_d1`, each `steps n start = some end` for all `m`, `n` (and `a`) and every tape `L` to the left.
Also the generated `step_none_iff` and `blank_runs_kernel` (10,000 steps) in `lean/Blank.lean`.

**Lean, `native_decide`**: `blank_runs_native`, no halt in 10^7 steps (`lean/Blank.lean`).

**Computed (trusted)**: `tmrun` (C) runs 2·10^11 steps without a halt; the tape is then 391,889 cells wide. The shared
cycle accelerator (`bbtools.cycles` over 2- and 4-cell blocks) finds no cycle rules for this machine: every sweep
changes the tape near both ends, so it is no faster than plain simulation (10^8 steps in 150 s).

**Heuristic**: the increment rule for all 2,282 clean increments of the first 3·10^7 steps (`py/check_increments.py`).

**Lean, kernel, in the twin's folder** (`../1RB0LF_0LC0RE_0RA1LD_1LB0LD_0RA1RC_1LA---/lean/Twin29537.lean`,
`RulesTwin1.lean`, `RulesTwin2.lean`): this machine is that table mirrored and started in D; the crossing rules of
the exact macro machine for this machine's first 300,000 records.

**Open**: whether it halts. Through the twin's macro machine, what is missing is the same as there: the composition of
the crossing rules in Lean, and some invariant of the tail under the operator word that the 3/2 orbit fixes.

## Reproduce

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RA_0RC0LE_0LD1RA_1LB0RF_0LD1LC_1RD---/lean/check.sh
python3 holdouts/1RB0RA_0RC0LE_0LD1RA_1LB0RF_0LD1LC_1RD---/py/gen_rules.py           # rewrites lean/Rules.lean
python3 holdouts/1RB0RA_0RC0LE_0LD1RA_1LB0RF_0LD1LC_1RD---/py/check_increments.py 30000000   # 10 s
```

## Layout

| path | what it is |
|---|---|
| `lean/Machine.lean`, `lean/Blank.lean` | the machine and bounded runs (generated) |
| `lean/Rules.lean` | the increments `half_sweep`, `inc_d0`, `inc_d1` (generated by `py/gen_rules.py`) |
| `py/gen_rules.py` | writes `lean/Rules.lean` |
| `py/check_increments.py` | checks the increment rule against a direct simulation |

## Pages

- [`pages/holdouts/1RB0RA_0RC0LE_0LD1RA_1LB0RF_0LD1LC_1RD---/explainer.html`](../../pages/holdouts/1RB0RA_0RC0LE_0LD1RA_1LB0RF_0LD1LC_1RD---/explainer.html)
- [`pages/holdouts/1RB0RA_0RC0LE_0LD1RA_1LB0RF_0LD1LC_1RD---/proof-status.html`](../../pages/holdouts/1RB0RA_0RC0LE_0LD1RA_1LB0RF_0LD1LC_1RD---/proof-status.html)

## For later

Next: write the general increment (any number of low 1-digits) as one Lean rule by induction on the carry length,
then find the rule for a carry into a higher separator (`1101`, `0101`, `000` were seen) and for the reservoir
refill. The `c = 1100` region at the right end is the least understood part: how it is built and when it turns
back into `a`s. A macro simulator for the digit/block/reservoir level would then let the run go far past 10^11.

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0LF_0LC0RE_0RA1LD_1LB0LD_0RA1RC_1LA---`](../1RB0LF_0LC0RE_0RA1LD_1LB0LD_0RA1RC_1LA---/README.md): rename A→D, B→B, C→C, D→A, E→E, F→F and exchange left and right; it is this table started in state D, in a mirror

<!-- end of related machines -->
