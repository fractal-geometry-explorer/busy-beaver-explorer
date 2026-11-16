# 1RB1LE_1RC0RD_1LD0RE_0LA0LC_1LC1RF_---0RA

bbchallenge id 158007. One of the six-state holdouts whose halting from blank tape is open. It is `1RB0RC_1LC0RE_0LD0LB_1RA1LE_1LB1RF_---0RD` with the states renamed, and runs the same binary counter in epochs.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LE |
| B | 1RC | 0RD |
| C | 1LD | 0RE |
| D | 0LA | 0LC |
| E | 1LC | 1RF |
| F | --- | 0RA |

## Status

Open. Proved in Lean (the same development as for the twin `1RB0RC_1LC0RE_0LD0LB_1RA1LE_1LB1RF_---0RD`, generated for this table):

- the halting configurations (`step_none_iff`, `lean/Blank.lean`); no halt in 10,000 steps by the kernel and in
  10^7 by `native_decide`;
- the token model: the eight rewriting rules (`lean/Rules.lean`, from `../1RB0RC_1LC0RE_0LD0LB_1RA1LE_1LB1RF_---0RD/py/rules.py twin`) and the map
  `next` with `next_sound` (`lean/Tokens.lean`), with the head in state A (the twin's D);
- the checked accelerated simulator `stepH` with `halts_iff` (`lean/Sim.lean`) and `no_halt_2e9`, no halt in 2·10^9
  steps (`lean/Run.lean`, `native_decide`).

Not proved: the resets, the epochs, and the relation to the twin (observed, below). A proof for the twin does not
transfer by itself: the two runs are different runs of one table, and they differ at the right end of the tape,
which is exactly where the resets happen.

## What it does

The table is that of `1RB0RC_1LC0RE_0LD0LB_1RA1LE_1LB1RF_---0RD` with states renamed (here A, B, C, D = there D, A, B, C), so the start state differs.
Everything in the twin's README ("What it does") holds here with A for D: the same token frames and rules, the same
binary counter in the left word, overflows whose gaps follow `D(n+1) = 2D(n) + 34` / `2D(n) - 14`, the marker walking
along the track of 0s, and epochs ended by resets.

**The relation to the twin.** From step 22.7·10^6 on, every token frame of this machine is phi of the twin's frame
at the same position in the run, where phi replaces the last two tokens `1 0` of the right word by `0` (the twin's
tape ends `...1 0 1^3`, this one's `...1 0 1`). So this machine's resets happen at `L | 1 0` where the twin's happen at
`L | 1 1 0`, and they produce phi of the twin's frame. This machine reaches each frame 67 steps before the twin reaches the corresponding
one in the epoch from 22.7·10^6, 77 in the next, 87 in the one after (each reset is 10 steps shorter here).
Checked frame by frame (`../1RB0RC_1LC0RE_0LD0LB_1RA1LE_1LB1RF_---0RD/py/twin.py`) over 3·10^6 frames across the reset at step 81.58·10^6, and at the
next two epoch starts by the epoch extrapolation (`../1RB0RC_1LC0RE_0LD0LB_1RA1LE_1LB1RF_---0RD/py/epochs.py run N twin`).

Epochs here: restarts at steps 8, 37, 206, 809, 3,782, 17,297, 22,706,588 and 81,579,887; the next predicted by the
extrapolation (heuristic) at step 3,219,517,448,110.

Halting: only F0; F is entered only from E1 (`1RF`), 9,523,774 times in 10^8 steps, always onto a 1.

## How far it was run

- Lean: 10^7 steps (`native_decide`), 2·10^9 (`no_halt_2e9`, checked token simulator).
- C, cell by cell: 10^9 steps; C token model (`../1RB0RC_1LC0RE_0LD0LB_1RA1LE_1LB1RF_---0RD/c/toksim.c twin`): 10^11 steps without a halt, every overflow gap of the epoch from 81,579,887 following the twin's law.
- Epoch extrapolation (heuristic): to step 3.2·10^12, the end of the second long epoch, in step with the twin.

## Open questions

- Everything open for the twin (the reset and the overflow law as theorems).
- The transfer: prove that phi commutes with the token rules (they read only the start of the right word, so this
  is local) and with the resets (`L | 1 1 0` against `L | 1 0` for every left word that occurs); then this machine
  halts iff the twin does.

## Earlier approaches

- Run-length frame map (`py/frames.py`, `lean/Pieces.lean`, `lean/Cases.lean`, `lean/Frames.lean`): 68 cases,
  each proved for all parameters and lists (`rlNext_sound`); the first 100,000 frames from blank tape exist
  (`native_decide`). Open: that the table is defined on every frame reached.
- Frame maps with scalar parameters do not close: `py/shapes.py` finds 455,393 distinct tape shapes at head turns in
  10^7 steps.

## First look

Growth class **fixed/power** (left: power, exponent 0.155; right: fixed,
exponent 0.081). After 1,000,000,000 steps: 181 cells visited (155 left of the
start, 23 right), 103 ones.

- left, step 553,148,028: `D>0 1^35 0 1^25 0 1^3 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1^3 0 1 0 1 0 1^5 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1^5 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1^3 0 1 0 1 0 1`

## Pages

- [`pages/holdouts/1RB1LE_1RC0RD_1LD0RE_0LA0LC_1LC1RF_---0RA/explainer.html`](../../pages/holdouts/1RB1LE_1RC0RD_1LD0RE_0LA0LC_1LC1RF_---0RA/explainer.html)
- [`pages/holdouts/1RB1LE_1RC0RD_1LD0RE_0LA0LC_1LC1RF_---0RA/proof-status.html`](../../pages/holdouts/1RB1LE_1RC0RD_1LD0RE_0LA0LC_1LC1RF_---0RA/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LE_1RC0RD_1LD0RE_0LA0LC_1LC1RF_---0RA/lean/check.sh
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0RC_1LC0RE_0LD0LB_1RA1LE_1LB1RF_---0RD`](../1RB0RC_1LC0RE_0LD0LB_1RA1LE_1LB1RF_---0RD/README.md): rename A→D, B→A, C→B, D→C, E→E, F→F; it is this table started in state B

<!-- end of related machines -->
