# 1RB0LD_0LC0RE_1LA0RD_0RB0LF_1RC1LA_0RB---

bbchallenge id 55410. One of the six-state holdouts whose halting from blank tape is open. Its run looks chaotic on a tape that grows roughly logarithmically.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LD |
| B | 0LC | 0RE |
| C | 1LA | 0RD |
| D | 0RB | 0LF |
| E | 1RC | 1LA |
| F | 0RB | --- |

## Status

Open. Proved in Lean (kernel): the halting configurations and the first 10,000 steps (`lean/Blank.lean`, 10^7 with
`native_decide`), and the laws of two of the three parts of the tape for every size (`lean/Counter.lean`,
`lean/Stream.lean`, below). Not decoded: the middle part of the tape. C: no halt in 30,000,000,000 steps.

## What it does

Mirror the tape and rename the states (C, A, B, E, D, F as A, B, C, D, E, F): the table becomes
1RB0LE_1LC0RE_0RA0LD_1LA1RB_0LC0RF_0LC---, which shares the prefix 1RB0LE_1LC0RE_0RA0LD_1LA with
1RB0LE_1LC0RE_0RA0LD_1LA0LF_0LC0RA_0RE--- and the F02 two-word sweepers. So it is the same cascade of counters, seen
in a mirror: the base-3 counter at the right end and the binary streams on the left. The crossing profile
(`c/cross.c`, 10^9 steps, cells -46 to 192):

| cells at 10^9 steps | crossings | part |
|---|---|---|
| about 149 to 191 | ×1/3 every 3 cells going right (6,052,568 at 149, 2,017,523 at 152 … 1 at 191) | **N**, a base-3 counter, 15 digits |
| 62 to 149 | up to 36 million, no simple pattern | the **middle**, not decoded |
| 22 to 62 | ×2 every 4 cells going right (1,883 at 22 … 1,563,086 at 62) | binary counters with 4-cell digits |
| -46 to 22 | a few hundred, falling to 1 at the left end | runs of `01` growing at rare left-end events |

**The right counter N (proved).** Read the cells right of N's low end three at a time from the head outward:
`010` = 0, `110` = 1, `100` = 2; blank beyond. A visit in state C adds one; it comes back out in state A (no carry)
or D (carry); a carry through every digit turns blank cells into a new digit 2. `lean/Counter.lean` proves it for
every number of digits (`n_inc0`, `n_inc1`, `n_inc0_carry`, `n_inc1_carry`, `n_overflow`), from five rows
(`lean/VisitR.lean`, predicate `Vis`). In the run, the cells right of 126 are entered only in state C and all
142,058 of those visits are these rows, from step 689,712 until step 43,905,102 (`c/vislaws.c`); then the middle
reaches 126 and N's low end moves outward. The wall of `110`s at the right end is made of N's top digits.

**The binary streams (proved).** `lean/Stream.lean` proves the stream laws of the F02 sibling
1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RA_0LB--- for the mirror image of this machine with the states renamed (predicate
`VisL`, streams left of the head, nearest cell first): a visit in state A (the sibling's B) to an a/z stream is a
binary increment (`vb_odd`, `vb_even`, `ve_odd`), a visit in state C (the sibling's A) to the counter M adds one and
wraps (`m_inc`, `m_wrap`). From 29 token rows mined left of cell 30 (`lean/VisitL.lean`).

**Where it could halt.** Only F1 halts, and F is entered only from D reading 1 (`0LF`), which is frequent here: 3,571,420
times in the first 10^8 steps, always with a 0 left of D, so F reads 0 and goes on with `0RB`. In the renamed table
this is the step E1 = `0RF` followed by F0 = `0LC`; the relatives have E1 = `0RA` or `0RE` there. The rare transition
is E1 (`1LA`, the renamed D1 = `1RB`): 66 times in 10^8 steps, the counterpart of the rare D1 events of
1RB0LE_1LC0RE_0RA0LD_1LA0LF_0LC0RA_0RE---. `holdouts/related.json` already notes that most of this machine's
configurations in its first 10^7 steps also occur, mirrored, in the run of that machine.

## How far it was run

- Direct C simulation (`c/longrun.c`): 30,000,000,000 steps, no halt; at the end cells -50 to 213 (264 cells), 118 ones.
- No macro-level accelerator: the time is spent in the undecoded middle.

## Open questions

- Decode the middle (cells 62 to 149 at 10^9 steps).
- Why D never reads 1 with a 1 to its left (millions of times per 10^8 steps): a local invariant that no CTL window
  up to 8 cells captures; it should follow from the decoded layout.

## Scripts

- `c/cross.c`, `c/longrun.c`, `c/d1ev.c`, `c/vislaws.c` (as in 1RB0LE_1LC0RE_0RA0LD_1LA0LF_0LC0RA_0RE---).
- `py/make_lean.py py/lean_config.json lean/` (from this folder; the config holds the renaming) writes
  `lean/VisitL.lean`, `lean/VisitR.lean`, `lean/Counter.lean`, `lean/Stream.lean`; `py/rows.json` holds the rows.

## Earlier notes

- `bbtools.macro` with blocks of 3 / 6 cells needs one macro step per about 3 / 6-7 steps over 10^7 steps;
  `bbtools.cycles` (k = 4) finds no linear cycle in 10^7 steps; CTL windows up to 8 cells do not close (group scan).

## First look

Growth class **fixed/fixed** (left: fixed, exponent 0.074; right: fixed,
exponent 0.082). After 1,000,000,000 steps: 239 cells visited (46 left of the
start, 192 right), 103 ones.

## Pages

- [`pages/holdouts/1RB0LD_0LC0RE_1LA0RD_0RB0LF_1RC1LA_0RB---/explainer.html`](../../pages/holdouts/1RB0LD_0LC0RE_1LA0RD_0RB0LF_1RC1LA_0RB---/explainer.html)
- [`pages/holdouts/1RB0LD_0LC0RE_1LA0RD_0RB0LF_1RC1LA_0RB---/proof-status.html`](../../pages/holdouts/1RB0LD_0LC0RE_1LA0RD_0RB0LF_1RC1LA_0RB---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LD_0LC0RE_1LA0RD_0RB0LF_1RC1LA_0RB---/lean/check.sh
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same tapes at another pace (observed, not proved).** Leave the states aside and compare only the tape and the place of the head. Then a large part of the first 10^7 configurations of this machine are configurations of the machines below, in the same order and up to the end of the run. The steps at which they occur differ, the tables are not renamings of each other, and equal tapes with different states may be continued differently, so this does not tie the halting questions together.

- [`1RB0LE_1LC0RE_0RA0LD_1LA0LF_0LC0RA_0RE---`](../1RB0LE_1LC0RE_0RA0LD_1LA0LF_0LC0RA_0RE---/README.md) (in a mirror): 9,285,736 configurations, the last at step 10,000,000 here and step 9,285,895 there

<!-- end of related machines -->
