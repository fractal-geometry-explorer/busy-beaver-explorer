# 1RB0LE_1RC1RB_1LD0RE_1LA1LC_1RB0LF_0LC---

bbchallenge id 95765. One of the six-state holdouts whose halting from blank tape is open. Same mechanism as
`1RB0LE_1RC1RB_1LD0RA_1LA1LC_0LC0LF_0RB---` (analysed first, see its folder). **Twin**: `1RB0LE_1RC1RB_1LD0RA_1LA1LC_0LC1LF_0RA---` has exactly the same tape at all 190
left-end samples in the first 2·10^9 steps (trusted, `c/samples.c`); the step counts differ by about 0.005 %.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LE |
| B | 1RC | 1RB |
| C | 1LD | 0RE |
| D | 1LA | 1LC |
| E | 1RB | 0LF |
| F | 0LC | --- |

## What it does

**Sample point**: the head in A at the left end of the tape. At every sample the tape is a list of blocks
`1^k 00`, almost all with k = 6j+1 (level j), grouped in long runs of equal blocks, highest level on the left. For
example at step 1,032,953,757 (each block written as its k, `x` repeats, `1/1` is `1 0`):

    8 1/1 25 7 1 7 57 55x2 53 1 7 49 47 1 43x16 39 37x5 35 1 19 31x82 29 11 1 25x33 23 19x415 17 1 7 13x176 11 1 7x2065 5 1x890 1

**Round** (one sample to the next, about 1.25 times longer each time): an expanding bouncer. The head runs right to a
point inside the tape, then zig-zags in a window that widens on both sides by a few cells per trip until it reaches
the left end. Going right it rewrites `11` pairs as `01` (E or C, 6 steps a pair); going left it rewrites `01`
as `11` (C or D, 2 steps a pair).

**Rule (observed)**: a run of n blocks of level j becomes a run of between floor(n/2)-1 and ceil(n/2)+1 blocks of
level j+1, and a new run of level-0 blocks `100` appears on the right, alternately large and small (the large ones
1590, 2086, 2664, 3330, 4130, 5171). Example: the sample above goes, at step 1,315,786,580, to `... 37x41 ... 31x16 29 25x207 23 13 19x87 17 1 7 13x1032 11
7x445 3 1x5171 1` (890 -> 445, 2065 -> 1032, 176 -> 87, 415 -> 207, 82 -> 41). A few odd blocks (k = 5, 11, 17, ...) sit between
runs: the leftovers of odd counts. In plain words: a binary-counter-like cascade on the lengths of the runs, so the
number of levels (the left side) grows like log t, while the bouncer makes the right side grow like sqrt t.

**Halting**: the only halt is F on a 1, reached only from `1 1 1 D> 0` (F needs E on a 1 entered from A, A comes
only from D on a 0). In the first 10^9 steps D reads a 0 20,887 times next to `1 1 0` and 147 times at the blank end,
never next to three 1s. So: it halts iff some round brings D onto a 0 to the right of a run of at least three 1s.

## Status

Open.

- **Lean, kernel** (`lean/Rules.lean`, from `py/rules.py`): the shift rules `b_run`, `e_halve`, `c_halve`,
  `c_double`, `d_double`; `halt_shape` (`1 1 1 D> 0` reaches F on a 1 in 3 steps) and `halt_after_shape`.
  `lean/Blank.lean`: the halting configurations; no halt in 10^7 steps (native_decide), 10^4 (kernel).
- **Trusted**: no halt in 10^9 steps (triage); the near-miss count above (`c/halt_nbhd.c`).
- **Heuristic**: the rounds and the halving law, checked on every run of at least 10 blocks at every round from
  1.2·10^7 to 1.6·10^9 steps (two exceptions earlier, at 5.7·10^6 and 1.1·10^7) (`c/samples.c`, `py/rounds.py`).
- **Computed, negative**: `bbtools.ctl` with K = 3 and 6 closes but allows halts (24 and 480 halting abstract configurations); n-gram CPS widths 3..7 fail.

## Notes for later

- The exact round map, including what happens to odd counts (the leftovers) and how the size of the new level-0 run
  is set, is not found. With it the machine becomes a counter-like map on a list of run lengths, and the halting
  question becomes whether a leftover ever puts three 1s next to D reading a 0.

## Reproduce

```sh
gcc -O2 -o samples holdouts/1RB0LE_1RC1RB_1LD0RE_1LA1LC_1RB0LF_0LC---/c/samples.c
./samples 1RB0LE_1RC1RB_1LD0RE_1LA1LC_1RB0LF_0LC--- 2000000000 A L 0 100000 > left.txt
python3 holdouts/1RB0LE_1RC1RB_1LD0RE_1LA1LC_1RB0LF_0LC---/py/rounds.py left.txt
gcc -O2 -o halt_nbhd holdouts/1RB0LE_1RC1RB_1LD0RE_1LA1LC_1RB0LF_0LC---/c/halt_nbhd.c && ./halt_nbhd 1RB0LE_1RC1RB_1LD0RE_1LA1LC_1RB0LF_0LC--- 1000000000 D 0
python3 holdouts/1RB0LE_1RC1RB_1LD0RE_1LA1LC_1RB0LF_0LC---/py/rules.py > holdouts/1RB0LE_1RC1RB_1LD0RE_1LA1LC_1RB0LF_0LC---/lean/Rules.lean
```

## Accelerated run (13 November 2026)

Observed, not proved: the accelerated simulator `rsim.py` ran 5.90x10^13 steps from blank tape without reaching a halting transition. Its tape, state and head position were equal to those of a plain C simulator at 6 checkpoints, the last at 1.00x10^10 steps. Of these steps, the part after the last checkpoint rests on the simulator alone, including 4,087 trip-level jumps: a jump applies many identical round trips at once after seeing the same tape shape recur with constant count changes, which is validated against direct simulation but not proved.

```sh
python3 holdouts/1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA1RF_0LC---/py/rsim_screen.py 1RB0LE_1RC1RB_1LD0RE_1LA1LC_1RB0LF_0LC--- 400
```

## Pages

- [`pages/holdouts/1RB0LE_1RC1RB_1LD0RE_1LA1LC_1RB0LF_0LC---/explainer.html`](../../pages/holdouts/1RB0LE_1RC1RB_1LD0RE_1LA1LC_1RB0LF_0LC---/explainer.html)
- [`pages/holdouts/1RB0LE_1RC1RB_1LD0RE_1LA1LC_1RB0LF_0LC---/proof-status.html`](../../pages/holdouts/1RB0LE_1RC1RB_1LD0RE_1LA1LC_1RB0LF_0LC---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LE_1RC1RB_1LD0RE_1LA1LC_1RB0LF_0LC---/lean/check.sh
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0LE_1RC1RA_1LD0RE_1LA1LD_1LD0RF_0RA---`](../1RB0LE_1RC1RA_1LD0RE_1LA1LD_1LD0RF_0RA---/README.md): rename A→C, B→D, C→A, D→B, E→E, F→F and exchange left and right; it is this table started in state C, in a mirror
- [`1RB1RD_1LC0RE_1LD1LC_1RA0LE_1LC0RF_0RD---`](../1RB1RD_1LC0RE_1LD1LC_1RA0LE_1LC0RF_0RD---/README.md): rename A→B, B→C, C→D, D→A, E→E, F→F and exchange left and right; it is this table started in state D, in a mirror

**Same tapes at another pace (observed, not proved).** Leave the states aside and compare only the tape and the place of the head. Then a large part of the first 10^7 configurations of this machine are configurations of the machines below, in the same order and up to the end of the run. The steps at which they occur differ, the tables are not renamings of each other, and equal tapes with different states may be continued differently, so this does not tie the halting questions together.

- [`1RB0LE_1RC1RB_1LD0RA_1LA1LC_0LC1LF_0RA---`](../1RB0LE_1RC1RB_1LD0RA_1LA1LC_0LC1LF_0RA---/README.md): 9,995,929 configurations, the last at step 9,995,928 here and step 10,000,000 there
- [`1RB0RF_0LC---_1LD1LC_1RE0LA_1RA1RD_0RD0RF`](../1RB0RF_0LC---_1LD1LC_1RE0LA_1RA1RD_0RD0RF/README.md) (in a mirror): 8,003,899 configurations, the last at step 8,003,898 here and step 9,999,998 there

<!-- end of related machines -->
