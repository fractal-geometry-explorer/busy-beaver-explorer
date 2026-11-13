# 1RB0LD_0RC---_0RD0RF_1LE0LA_1LF1LE_1RA0RD

bbchallenge id 48815. One of the six-state holdouts whose halting from blank tape is open (group G05, growth class
fixed/sqrt).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LD |
| B | 0RC | --- |
| C | 0RD | 0RF |
| D | 1LE | 0LA |
| E | 1LF | 1LE |
| F | 1RA | 0RD |

## Status

**Open.** A bouncer with a moving wall, running on top of a stack of counters that it uses up irregularly.
Each layer is marked with what it rests on.

- Lean, kernel (`lean/Blank.lean`): the halting configurations (`step_none_iff`) and no halt in 10,000 steps.
- Lean, `native_decide` (`lean/Blank.lean`): no halt in 10,000,000 steps.
- Lean, kernel (`lean/Sweep.lean`, namespace `H48815`): the sweeps for every length, `sweep_left`, `sweep_right`,
  the turn at the right end `turn_right`, and the full right round trip `round_right` (68n + 5 steps); also a
  shift rule with carried words on both sides, `cross_l2`.
- Trusted (C, `tools/c/tm.h`, `c/snap.c`): no halt in the first 4·10⁹ steps.
- Trusted (Python segment simulator with cycle jumps, `py/segsim.py`, `py/accel.py`, checked cell for cell
  against the C simulator at 1.9·10⁹ and 9.9·10⁹ steps): no halt in the first 2.5·10⁷² steps (30 minutes).
- Heuristic: the epoch structure below and the 9/4 growth.
- Open: the rule by which the counters are used up, and so halting.

## What the tape looks like

Words: P = `10011010`, Q = `11110001` (8 cells), A18 = `101010011010100110`, C18 = `100110101001101001` (18 cells),
W36 = `101001100110010011101001101010100110` (36 cells).

    0^∞  [counters: W36^c₁ … W36^cⱼ]  [debris]  A18^x  |wall|  (P or Q)^y  1 0^∞

The head bounces between the wall and the right end. A right sweep turns Q^y into P^y (32 steps per word,
`sweep_right`), the turn adds 2 cells (`turn_right`), the left sweep turns P^y back into Q^y (36 per word,
`sweep_left`); a whole right trip is 68y + 5 steps (`round_right`).

- **Phase A.** The wall eats A18 two cells per trip: over a 36-trip cycle the wall moves 72 cells left,
  x drops by 4 and y grows by 18.
- **Phase B.** When A18 is used up the head runs further left into the counters and debris, works on them,
  and then the wall marches right 18 cells per trip, turning two 8-cell words into one C18 (x + 1, y − 2).
  When y is used up a new phase A starts (C18 now reads as A18 from the other side).

Each epoch (A then B) multiplies x and y by about 9/4. The number of B trips per epoch runs 86, 203, 463,
1051, 2359 (at 3.8·10⁶, 1.9·10⁷, 9.3·10⁷, 4.7·10⁸, 2.4·10⁹ steps).

## The counters

At the end of each phase A the wall works on the nearest counter W36^c and removes 0, 1 or 2 copies, with no
visible rule. The first counter (10 copies) runs 6, 4, 4, 4, 3, gone over the first epochs. When the last counter
is used up the whole A18 run turns into a new counter and the bouncer starts again from small sizes:

| steps | new counter (W36 copies) | counters afterwards |
|---|---|---|
| 1.7·10¹⁴ | 345,724 (and a small one of 5) | [345724, 5] |
| 4.96·10²¹ | 1,710,343,625 (and 38) | [345717, 1710343625, 38] |
| 2.57·10⁷² | 38,924,542,121,409,275,697,275,846,796,041,586 | [345717, 1710343616, 3.9·10³⁴, 7.3·10¹⁷] |

Between restarts the epoch sizes repeat exactly. This looks like a recursion: each counter is about as large as
the bouncer was when it was built, and the lower levels wear it down a little at a time. Whether a counter can
ever be used up in a way that sends the head into the halting entry (B reading 1) depends on residues of sizes
that grow by 9/4 per epoch, the usual Collatz-like obstacle.

## Reproduce

```sh
python3 holdouts/1RB0LD_0RC---_0RD0RF_1LE0LA_1LF1LE_1RA0RD/py/gen_sweep.py        # writes lean/Sweep.lean
python3 holdouts/1RB0LD_0RC---_0RD0RF_1LE0LA_1LF1LE_1RA0RD/py/run.py check 1e9    # segment simulator vs plain C at the first sample after 1e9
python3 holdouts/1RB0LD_0RC---_0RD0RF_1LE0LA_1LF1LE_1RA0RD/py/run.py epochs 600   # one line per epoch for 10 minutes
```

`c/dump.c`, `c/sweeps.c` and `c/snap.c` are the plain-simulator helpers used to find the structure.

## Pages

- [`pages/holdouts/1RB0LD_0RC---_0RD0RF_1LE0LA_1LF1LE_1RA0RD/explainer.html`](../../pages/holdouts/1RB0LD_0RC---_0RD0RF_1LE0LA_1LF1LE_1RA0RD/explainer.html)
- [`pages/holdouts/1RB0LD_0RC---_0RD0RF_1LE0LA_1LF1LE_1RA0RD/proof-status.html`](../../pages/holdouts/1RB0LD_0RC---_0RD0RF_1LE0LA_1LF1LE_1RA0RD/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LD_0RC---_0RD0RF_1LE0LA_1LF1LE_1RA0RD/lean/check.sh
```

## For later

- The exact rule for the wall's work at the end of phase A: how many W36 copies it removes, as a function of
  x, y, the counter and the debris. With it the run becomes an explicit recursion on the counter stack.
- Lean: the phase A cycle (36 trips) and the phase B trip as rules for all sizes, by the same method as
  `Sweep.lean` (symbolic proofs plus `cross_l2`).
- Run `py/run.py epochs` longer to see the next restarts and whether a counter is ever reached with a residue
  that leads to the halting entry.

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0RE_1RC0LE_0RD---_0RE0RA_1LF0LB_1LA1LF`](../1RB0RE_1RC0LE_0RD---_0RE0RA_1LF0LB_1LA1LF/README.md): rename A→B, B→C, C→D, D→E, E→F, F→A; it is this table started in state F
- [`1RB0RD_1RC1RB_1LD0LA_1LE0RA_0LF---_0LA0LC`](../1RB0RD_1RC1RB_1LD0LA_1LE0RA_0LF---_0LA0LC/README.md): rename A→D, B→E, C→F, D→A, E→B, F→C and exchange left and right; it is this table started in state D, in a mirror

<!-- end of related machines -->
