# 1RB0RB_0LC0RA_1LE1LD_0LE---_1LF0LC_1RA1LB

bbchallenge id 164326. A marker 0 drifts left through a long alternating sea while a counter at the left end, written in pieces <code>1110</code>, counts the sweeps; when the marker reaches the far end the sea is reset, a little longer.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RB |
| B | 0LC | 0RA |
| C | 1LE | 1LD |
| D | 0LE | --- |
| E | 1LF | 0LC |
| F | 1RA | 1LB |

## What it does

Stop the run when the head reaches a new cell (`a = 10`):

    94,109,254  B>0 1^2 a 1^2 a 1^2 a 1^2 a^2 1^2 a^24 1^2 a^643 0 a^362
    94,966,670  B>0 1^2 a 1^2 a 1^2 a 1^2 a 1 a^1034
    94,968,812  a 0 a^2 0^2 a 0^2 a 0^2 a 0^2 a 0^2 a^1033 1 B>0        (right end)
    95,857,069  B>0 1^2 a^2 1^2 a 1^2 a 1^2 a 1^2 a 1^2 a^791 0 a^243
    97,110,957  B>0 1^2 a 1^2 a^2 1^2 a 1^2 a 1^2 a 1^2 a 1^2 a^62 0 a^972

A marker 0 in an alternating sea `a^x 0 a^y` moves left; a counter of pieces `1^2 a^k` at the left end grows only
when it gains a piece, and between left growths x fell by 243 (79 times), 81 (70), 27 (34), 9 (8), 729 (6) in the first
10^8 steps, with 143 resets. The sweep counter of `1RB0RE_1LC1RD_1LD0LD_0RE0LC_1RA1RF_0RA---`, mirrored.

## Halting

D1 halts; D is entered only from C1 (`1LD`), so a halt needs `1 C>1`. In the first 10^8 steps D was entered
74,578 times, always on a 0 (`c/sstat.c`). Open.

## Status

Open. Lean (`lean/Blank.lean`): the halting configurations (`step_none_iff`), no halt in 10,000 steps by the kernel, in 10,000,000 by `native_decide`. C: no halt in 10^9 steps (`tools/c/triage.c`) and in 10^15 steps (`c/mrun.c`, exact macro simulation). The structure described here is observed, not proved.

## First look

Growth class **power/power** (left: power, exponent 0.345; right: power,
exponent 0.298). After 1,000,000,000 steps: 4,657 cells visited (3,548 left of the
start, 252 right), 2,326 ones.

- left, step 967,979,530: `B>0 1^2 0 1 0 1^3 0 1 0 1^3 0 1^3 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1^3 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 `
- left, step 985,355,520: `B>0 1^3 0 1^3 0 1^3 0 1 0 1^3 0 1^3 0 1 0 1 0 1 0 1^3 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1^3 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 `
- right, step 977,920,311: `1 0^2 1 0 1 0^3 1 0^3 1 0 1 0 1 0 1 0^3 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0^3 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 `
- right, step 999,091,125: `1 0^2 1^2 0^3 1 0^2 1 0^3 1 0^3 1 0 1 0^6 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 `




## Accelerated run (13 November 2026)

Observed, not proved: the accelerated simulator `rsim.py` ran 2.89x10^9 steps from blank tape without reaching a halting transition. Its tape, state and head position were equal to those of a plain C simulator at 4 checkpoints, the last at 1.00x10^9 steps. No trip-level jump was used in this run, only the shift rules over repeated words (exact by induction, but the program is not verified).

```sh
python3 holdouts/1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA1RF_0LC---/py/rsim_screen.py 1RB0RB_0LC0RA_1LE1LD_0LE---_1LF0LC_1RA1LB 400
```

## Pages

- [`pages/holdouts/1RB0RB_0LC0RA_1LE1LD_0LE---_1LF0LC_1RA1LB/explainer.html`](../../pages/holdouts/1RB0RB_0LC0RA_1LE1LD_0LE---_1LF0LC_1RA1LB/explainer.html)
- [`pages/holdouts/1RB0RB_0LC0RA_1LE1LD_0LE---_1LF0LC_1RA1LB/proof-status.html`](../../pages/holdouts/1RB0RB_0LC0RA_1LE1LD_0LE---_1LF0LC_1RA1LB/proof-status.html)




## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RB_0LC0RA_1LE1LD_0LE---_1LF0LC_1RA1LB/lean/check.sh
gcc -O2 -o mrun holdouts/1RB0RB_0LC0RA_1LE1LD_0LE---_1LF0LC_1RA1LB/c/mrun.c && ./mrun 1RB0RB_0LC0RA_1LE1LD_0LE---_1LF0LC_1RA1LB 2 1000000000000000
gcc -O2 -I tools/c -o sstat holdouts/1RB0RB_0LC0RA_1LE1LD_0LE---_1LF0LC_1RA1LB/c/sstat.c && ./sstat 1RB0RB_0LC0RA_1LE1LD_0LE---_1LF0LC_1RA1LB 100000000
```

## Later

- Decode the left counter exactly and compare with `1RB0RE_1LC1RD_1LD0LD_0RE0LC_1RA1RF_0RA---`.
- Accelerate the sweeps of a round to run far beyond 10^15.

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB1RF_1RC0RA_1LD1RE_1LE0LE_0RA0LD_0RB---`](../1RB1RF_1RC0RA_1LD1RE_1LE0LE_0RA0LD_0RB---/README.md): rename A→D, B→E, C→A, D→F, E→B, F→C and exchange left and right; it is this table started in state C, in a mirror
- [`1RB0RE_1LC1RD_1LD0LD_0RE0LC_1RA1RF_0RA---`](../1RB0RE_1LC1RD_1LD0LD_0RE0LC_1RA1RF_0RA---/README.md): rename A→C, B→D, C→E, D→F, E→A, F→B and exchange left and right; it is this table started in state E, in a mirror

<!-- end of related machines -->
