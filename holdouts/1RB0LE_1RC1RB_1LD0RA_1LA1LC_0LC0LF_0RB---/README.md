# 1RB0LE_1RC1RB_1LD0RA_1LA1LC_0LC0LF_0RB---

bbchallenge id 67137. One of the six-state holdouts whose halting from blank tape is open. Siblings with the same
mechanism: `1RB0LE_1RC1RB_1LD0RA_1LA1LC_0LC1LF_0RA---` and `1RB0LE_1RC1RB_1LD0RE_1LA1LC_1RB0LF_0LC---` (those two
have identical tapes at every sample).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LE |
| B | 1RC | 1RB |
| C | 1LD | 0RA |
| D | 1LA | 1LC |
| E | 0LC | 0LF |
| F | 0RB | --- |

## What it does

**Sample point**: the head in A at the left end of the tape. At every sample the tape is a list of blocks
`1^k 00`, almost all with k = 6j+1 (level j), grouped in long runs of equal blocks, highest level on the left. For
example at step 448,826,251 (each block written as its k, `x` repeats, `1/1` is `1 0`):

    58 1/1 13 53 47 49x3 43x4 41 37x18 31x23 25x92 1 17 19x113 7 1 11 13x458 1 5 7x570 5 1x2265 1

**Round** (one sample to the next, about 1.25 times longer each time): an expanding bouncer. The head runs right to a
point inside the tape, then zig-zags in a window that widens on both sides by a few cells per trip until it reaches
the left end. Going right it rewrites `11` pairs as `01` (A or C, 6 steps a pair); going left it rewrites `01`
as `11` (C or D, 2 steps a pair).

**Rule (observed)**: a run of n blocks of level j becomes a run of between floor(n/2)-1 and ceil(n/2)+1 blocks of
level j+1, and a new run of level-0 blocks `100` appears on the right, alternately about 0.65 and 1.9 times the
previous one. Example: the sample above goes to `... 43x9 37x11 31x46 ... 19x228 ... 13x284 11 7x1133 1x1500 1`
(2265 -> 1133, 570 -> 284, 458 -> 228, 113 -> 56, 92 -> 46). A few odd blocks (k = 5, 11, 17, ...) sit between
runs: the leftovers of odd counts. In plain words: a binary-counter-like cascade on the lengths of the runs, so the
number of levels (the left side) grows like log t, while the bouncer makes the right side grow like sqrt t.

**Halting**: the only halt is F on a 1, reached only from `1 1 1 D> 0` (A must come from D on a 0, then A, E, F
each read a 1). In the first 10^9 steps D reads a 0 20,887 times next to `1 1 0` and 147 times at the blank end,
never next to three 1s. So: it halts iff some round brings D onto a 0 to the right of a run of at least three 1s.

## Status

Open.

- **Lean, kernel** (`lean/Rules.lean`, from `py/rules.py`): the shift rules `b_run`, `a_halve`, `c_halve`,
  `c_double`, `d_double`; `halt_shape` (`1 1 1 D> 0` reaches F on a 1 in 3 steps) and `halt_after_shape`.
  `lean/Blank.lean`: the halting configurations; no halt in 10^7 steps (native_decide), 10^4 (kernel).
- **Trusted**: no halt in 10^9 steps (triage); the near-miss count above (`c/halt_nbhd.c`).
- **Heuristic**: the rounds and the halving law, checked on every run of at least 10 blocks at every round from
  3·10^6 to 1.7·10^9 steps (`c/samples.c`, `py/rounds.py`).
- **Computed, negative**: `bbtools.ctl` with K = 3, 4, 5, 6 closes but allows halts; n-gram CPS widths 3..7 fail.

## Notes for later

- The exact round map, including what happens to odd counts (the leftovers) and how the size of the new level-0 run
  is set, is not found. With it the machine becomes a counter-like map on a list of run lengths, and the halting
  question becomes whether a leftover ever puts three 1s next to D reading a 0.
- `bbtools.cycles` (K = 2) finds no linear cycle: the windows change shape every bounce.

## Reproduce

```sh
gcc -O2 -o samples holdouts/1RB0LE_1RC1RB_1LD0RA_1LA1LC_0LC0LF_0RB---/c/samples.c
./samples 1RB0LE_1RC1RB_1LD0RA_1LA1LC_0LC0LF_0RB--- 2000000000 A L 0 100000 > left.txt
python3 holdouts/1RB0LE_1RC1RB_1LD0RA_1LA1LC_0LC0LF_0RB---/py/rounds.py left.txt
gcc -O2 -o halt_nbhd holdouts/1RB0LE_1RC1RB_1LD0RA_1LA1LC_0LC0LF_0RB---/c/halt_nbhd.c && ./halt_nbhd 1RB0LE_1RC1RB_1LD0RA_1LA1LC_0LC0LF_0RB--- 1000000000 D 0
python3 holdouts/1RB0LE_1RC1RB_1LD0RA_1LA1LC_0LC0LF_0RB---/py/rules.py > holdouts/1RB0LE_1RC1RB_1LD0RA_1LA1LC_0LC0LF_0RB---/lean/Rules.lean
```

## Accelerated run (13 November 2026)

Observed, not proved: the accelerated simulator `rsim.py` ran 1.90x10^14 steps from blank tape without reaching a halting transition. Its tape, state and head position were equal to those of a plain C simulator at 6 checkpoints, the last at 1.00x10^10 steps. Of these steps, the part after the last checkpoint rests on the simulator alone, including 6,642 trip-level jumps: a jump applies many identical round trips at once after seeing the same tape shape recur with constant count changes, which is validated against direct simulation but not proved.

```sh
python3 holdouts/1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA1RF_0LC---/py/rsim_screen.py 1RB0LE_1RC1RB_1LD0RA_1LA1LC_0LC0LF_0RB--- 400
```

## Pages

- [`pages/holdouts/1RB0LE_1RC1RB_1LD0RA_1LA1LC_0LC0LF_0RB---/explainer.html`](../../pages/holdouts/1RB0LE_1RC1RB_1LD0RA_1LA1LC_0LC0LF_0RB---/explainer.html)
- [`pages/holdouts/1RB0LE_1RC1RB_1LD0RA_1LA1LC_0LC0LF_0RB---/proof-status.html`](../../pages/holdouts/1RB0LE_1RC1RB_1LD0RA_1LA1LC_0LC0LF_0RB---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LE_1RC1RB_1LD0RA_1LA1LC_0LC0LF_0RB---/lean/check.sh
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0LC---`](../1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0LC---/README.md): rename A→B, B→C, C→D, D→A, E→E, F→F and exchange left and right; it is this table started in state D, in a mirror
- [`1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA0RF_0LD---`](../1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA0RF_0LD---/README.md): rename A→C, B→D, C→A, D→B, E→E, F→F and exchange left and right; it is this table started in state C, in a mirror

<!-- end of related machines -->
