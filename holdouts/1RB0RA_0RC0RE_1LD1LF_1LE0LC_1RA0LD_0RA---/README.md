# 1RB0RA_0RC0RE_1LD1LF_1LE0LC_1RA0LD_0RA---

bbchallenge id 85142. One of the six-state holdouts whose halting from blank tape is open; analyzed by hand (group G02). The pages are built from [`status.json`](status.json).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RA |
| B | 0RC | 0RE |
| C | 1LD | 1LF |
| D | 1LE | 0LC |
| E | 1RA | 0LD |
| F | 0RA | --- |

## What it does

Sampled with the head in A at the right end, the tape has three zones (step 2,997,000; `c = 10`, `a = 110`,
`d = 110010`):

    c^40 0 c^61 a c^17 0 c^3 | d^148 0 c 0 c d 0 c 0 c d a^4 d 0 c 0 c 0 c a d 0 c 0 c d^2 0 c d^3 0 c | a^571 1 A>

- **Left counter**: a few runs of `10`; it changes only at rare moments (the left side grows like a logarithm).
- **Register**: cut into three-cell digits from the right it uses only `110` (1) and `010` (0). It has had exactly
  331 digits since step 764,833, when the tail of the time (329 blocks) was absorbed into it (it had 12 before).
  Its left part is still the fresh pattern `1010...`; every sweep changes digits only near its right (low) end:
  over the 4,244 sweeps to 10^8 steps the leftmost changed digit was within 20 of the end 93% of the time, never
  more than 60 away. The active zone eats into the fresh part very slowly (about 148 fresh digit pairs at 3·10^6
  steps, 136 at 3·10^9): a counter stepped once per sweep.
- **Tail** `(110)^t`, one block longer after every sweep (t = 21,472 at 3·10^9 steps): the bouncer, square-root
  growth. Going left the head rewrites each `110` as `001`, two blocks per 20 steps, and writes them back on the
  way right. Proved for all n (`pass`, `lean/Rules.lean`): `0 (110110)^n C> 001  ->  0 C> 001 (001001)^n` in 20n
  steps.

`py/register.py` prints the tail and the register's low end at each sample and the depth of each sweep's changes.

## Status

Open. The only halt is F reading a 1. F is entered after C reads a 1 (about 4% of steps); in the first 2·10^8
steps it always read a 0, almost always with `1011` to its left. The regular parts (tail, passes) cannot halt;
the register counter and the left counter are not understood, so the question is not reduced yet.

- Lean, kernel: halting configurations, 10^4 steps from blank (`lean/Blank.lean`); the leftward pass over the tail
  for every length, with a variant of `cross_l` that allows a fixed cell between head and repeats
  (`lean/Rules.lean`). `native_decide`: 10^7 steps.
- Computed: no halt in 10^10 steps (`tools/c/tmrun.c`); `bbtools.ctl` closes for K = 2..7 but allows F to read 1;
  n-gram CPS (widths 3..7, -H, -U) fails.

## Notes for later

- Decode the register: what the sweep does to its low end (it looks like a counter in an unusual numeration;
  compare consecutive samples from `py/register.py`), and when the left counter ticks.
- Then the halting question should become a question about that counter.

## Pages

- [`pages/holdouts/1RB0RA_0RC0RE_1LD1LF_1LE0LC_1RA0LD_0RA---/explainer.html`](../../pages/holdouts/1RB0RA_0RC0RE_1LD1LF_1LE0LC_1RA0LD_0RA---/explainer.html)
- [`pages/holdouts/1RB0RA_0RC0RE_1LD1LF_1LE0LC_1RA0LD_0RA---/proof-status.html`](../../pages/holdouts/1RB0RA_0RC0RE_1LD1LF_1LE0LC_1RA0LD_0RA---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RA_0RC0RE_1LD1LF_1LE0LC_1RA0LD_0RA---/lean/check.sh
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0RE_1LC0RA_1LD0LC_0LE0LB_1RA1RF_0LC---`](../1RB0RE_1LC0RA_1LD0LC_0LE0LB_1RA1RF_0LC---/README.md): rename A→C, B→D, C→E, D→A, E→B, F→F and exchange left and right; it is this table started in state D, in a mirror

<!-- end of related machines -->
