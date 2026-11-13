# 1RB0LE_1RC1RB_1LD0RA_1LA1LC_0LC1LF_0RA---

bbchallenge id 133909. One of the six-state holdouts whose halting from blank tape is open. Same mechanism as
`1RB0LE_1RC1RB_1LD0RA_1LA1LC_0LC0LF_0RB---` (analysed first, see its folder). **Twin**: `1RB0LE_1RC1RB_1LD0RE_1LA1LC_1RB0LF_0LC---` has exactly the same tape at all 190
left-end samples in the first 2·10^9 steps (trusted, `c/samples.c`); the step counts differ by about 0.005 %.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LE |
| B | 1RC | 1RB |
| C | 1LD | 0RA |
| D | 1LA | 1LC |
| E | 0LC | 1LF |
| F | 0RA | --- |

## What it does

**Sample point**: the head in A at the left end of the tape. At every sample the tape is a list of blocks
`1^k 00`, almost all with k = 6j+1 (level j), grouped in long runs of equal blocks, highest level on the left. For
example at step 1,032,996,043 (each block written as its k, `x` repeats, `1/1` is `1 0`):

    8 1/1 25 7 1 7 57 55x2 53 1 7 49 47 1 43x16 39 37x5 35 1 19 31x82 29 11 1 25x33 23 19x415 17 1 7 13x176 11 1 7x2065 5 1x890 1

**Round** (one sample to the next, about 1.25 times longer each time): an expanding bouncer. The head runs right to a
point inside the tape, then zig-zags in a window that widens on both sides by a few cells per trip until it reaches
the left end. Going right it rewrites `11` pairs as `01` (A or C, 6 steps a pair); going left it rewrites `01`
as `11` (C or D, 2 steps a pair).

**Rule (observed)**: a run of n blocks of level j becomes a run of between floor(n/2)-1 and ceil(n/2)+1 blocks of
level j+1, and a new run of level-0 blocks `100` appears on the right, alternately large and small (the large ones
1590, 2086, 2664, 3330, 4130, 5171). Example: the sample above goes, at step 1,315,832,564, to `... 37x41 ... 31x16 29 25x207 23 13 19x87 17 1 7 13x1032 11
7x445 3 1x5171 1` (890 -> 445, 2065 -> 1032, 176 -> 87, 415 -> 207, 82 -> 41). A few odd blocks (k = 5, 11, 17, ...) sit between
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
  1.2·10^7 to 1.6·10^9 steps (two exceptions earlier, at 5.7·10^6 and 1.1·10^7) (`c/samples.c`, `py/rounds.py`).
- **Computed, negative**: `bbtools.ctl` with K = 3 and 6 closes but allows halts (24 and 480 halting abstract configurations); n-gram CPS widths 3..7 fail.

## Notes for later

- The exact round map, including what happens to odd counts (the leftovers) and how the size of the new level-0 run
  is set, is not found. With it the machine becomes a counter-like map on a list of run lengths, and the halting
  question becomes whether a leftover ever puts three 1s next to D reading a 0.

## Reproduce

```sh
gcc -O2 -o samples holdouts/1RB0LE_1RC1RB_1LD0RA_1LA1LC_0LC1LF_0RA---/c/samples.c
./samples 1RB0LE_1RC1RB_1LD0RA_1LA1LC_0LC1LF_0RA--- 2000000000 A L 0 100000 > left.txt
python3 holdouts/1RB0LE_1RC1RB_1LD0RA_1LA1LC_0LC1LF_0RA---/py/rounds.py left.txt
gcc -O2 -o halt_nbhd holdouts/1RB0LE_1RC1RB_1LD0RA_1LA1LC_0LC1LF_0RA---/c/halt_nbhd.c && ./halt_nbhd 1RB0LE_1RC1RB_1LD0RA_1LA1LC_0LC1LF_0RA--- 1000000000 D 0
python3 holdouts/1RB0LE_1RC1RB_1LD0RA_1LA1LC_0LC1LF_0RA---/py/rules.py > holdouts/1RB0LE_1RC1RB_1LD0RA_1LA1LC_0LC1LF_0RA---/lean/Rules.lean
```

## Pages

- [`pages/holdouts/1RB0LE_1RC1RB_1LD0RA_1LA1LC_0LC1LF_0RA---/explainer.html`](../../pages/holdouts/1RB0LE_1RC1RB_1LD0RA_1LA1LC_0LC1LF_0RA---/explainer.html)
- [`pages/holdouts/1RB0LE_1RC1RB_1LD0RA_1LA1LC_0LC1LF_0RA---/proof-status.html`](../../pages/holdouts/1RB0LE_1RC1RB_1LD0RA_1LA1LC_0LC1LF_0RA---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LE_1RC1RB_1LD0RA_1LA1LC_0LC1LF_0RA---/lean/check.sh
```
