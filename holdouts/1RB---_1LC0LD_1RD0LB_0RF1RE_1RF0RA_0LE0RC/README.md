# 1RB---_1LC0LD_1RD0LB_0RF1RE_1RF0RA_0LE0RC

bbchallenge id 99408.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | --- |
| B | 1LC | 0LD |
| C | 1RD | 0LB |
| D | 0RF | 1RE |
| E | 1RF | 0RA |
| F | 0LE | 0RC |

## Status

**Open.** Long runs of 4-cell and 2-cell words, converted run by run; at the end one 1011 becomes three 10 every five visits, and the runs left behind have nearly doubling lengths (991, 1981, 3966, 7939): a binary-like hierarchy, not decoded.

## What it does

The tape grows to the right. It is made of long runs of the words `1011`, `0111` (4 cells) and `10`, `01`
(2 cells), and the work happens on the last runs (`py/view.py 2e10 4000`, block view at the right end):

- In the steady phase the end of the tape is `(1011)^X (10)^Y`, and every five visits of the right end one `1011`
  becomes three `10` (X = 11,920, 11,120, 10,320, ... and Y = 45,418, 47,818, 50,218, ... between 1.6·10^10 and
  1.7·10^10 steps).
- Between steady phases whole runs are converted from one word to another, one run after the other, walking left
  (`(10)^n` into `(01)^n`, `(01)^n` into `(0111)^(n/2)`, `(0111)^n` into `(1011)^n` and so on).
- The runs left behind have lengths close to a doubling sequence: 987 or 991, 1,981 or 1,983, 3,966 or 3,970,
  7,939, while the last run is several times longer (27,050 `1011` at 1.34·10^10 steps, then 54,118 `10`).

The doubling sizes suggest a binary counter whose digits are runs, or a map that doubles a value per level, but the
phases have not been decoded into an exact map.

## Results

- `py/view.py` (with `c/blocks.c`, `c/gaps.c`) prints the views of the run quoted above; `python3 py/view.py 2e10 4000` is the block view at the right end.
- Lean (`lean/Blank.lean`): no halt in 10^7 steps; C (`tools/c/triage.c`): none in 10^9.
- No macro rule is proved yet. Next step: prove the steady conversion with symtm, list the run conversions of a walk back, and extract the map on run lengths.

## First look

Growth class **fixed/sqrt** (left: fixed, exponent 0.0; right: sqrt,
exponent 0.498). After 1,000,000,000 steps: 52,266 cells visited (14 left of the
start, 37,397 right), 29,986 ones.

- right, step 970,117,228: `1^3 0 1^3 0 1^3 0 1^3 0 1^3 0 1^3 0 1^3 0 1^3 0 1^3 0 1^3 0 1 0 1 0 1 0 1 0 1 0 1 0 1^2 0 1^4 0 1^3 0 1 0 1 0 1 0 1 0 1 0 1 0 1^2 0 1 0^2 1^3 0 1 0 1 0 1 0 1 0 1 0 1 0 1^2 0 1 0^2 1^3 0 1^3 0 1^3 0 1^3 0 1^3 0 1^3 0 1^3 0 1^3 0 1^3 0 1^3 0 1^3 0 1^3 0 1^2 0 1^2 0 1^3 0 1^3 0 1^3 0 1^3 0 1^3 0 1^3 0 `
- right, step 985,860,648: `1^3 0 1^3 0 1^3 0 1^3 0 1^3 0 1^3 0 1^3 0 1^3 0 1^3 0 1^3 0 1 0 1 0 1 0 1 0 1 0 1 0 1^2 0 1^4 0 1^3 0 1 0 1 0 1 0 1 0 1 0 1 0 1^2 0 1 0^2 1^3 0 1 0 1 0 1 0 1 0 1 0 1 0 1^2 0 1 0^2 1^3 0 1^3 0 1^3 0 1^3 0 1^3 0 1^3 0 1^3 0 1^3 0 1^3 0 1^3 0 1^3 0 1^3 0 1^2 0 1^2 0 1^3 0 1^3 0 1^3 0 1^3 0 1^3 0 1^3 0 `

## Accelerated run (13 November 2026)

Observed, not proved: the accelerated simulator `rsim.py` ran 9.91x10^830 steps from blank tape without reaching a halting transition. Its tape, state and head position were equal to those of a plain C simulator at 6 checkpoints, the last at 1.02x10^10 steps. Of these steps, the part after the last checkpoint rests on the simulator alone, including 11,285 trip-level jumps: a jump applies many identical round trips at once after seeing the same tape shape recur with constant count changes, which is validated against direct simulation but not proved.

```sh
python3 holdouts/1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA1RF_0LC---/py/rsim_screen.py 1RB---_1LC0LD_1RD0LB_0RF1RE_1RF0RA_0LE0RC 400
```

## Pages

- [`pages/holdouts/1RB---_1LC0LD_1RD0LB_0RF1RE_1RF0RA_0LE0RC/explainer.html`](../../pages/holdouts/1RB---_1LC0LD_1RD0LB_0RF1RE_1RF0RA_0LE0RC/explainer.html)
- [`pages/holdouts/1RB---_1LC0LD_1RD0LB_0RF1RE_1RF0RA_0LE0RC/proof-status.html`](../../pages/holdouts/1RB---_1LC0LD_1RD0LB_0RF1RE_1RF0RA_0LE0RC/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB---_1LC0LD_1RD0LB_0RF1RE_1RF0RA_0LE0RC/lean/check.sh
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0LF_0RC1RD_0LD0RA_1RC0RE_1RF---_1LA0LB`](../1RB0LF_0RC1RD_0LD0RA_1RC0RE_1RF---_1LA0LB/README.md): rename A→E, B→F, C→A, D→B, E→D, F→C; it is this table started in state C

<!-- end of related machines -->
