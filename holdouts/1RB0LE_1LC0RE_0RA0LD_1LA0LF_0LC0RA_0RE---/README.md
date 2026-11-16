# 1RB0LE_1LC0RE_0RA0LD_1LA0LF_0LC0RA_0RE---

bbchallenge id 43701. One of the six-state holdouts whose halting from blank tape is open. Its run looks chaotic on a tape that grows roughly logarithmically.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LE |
| B | 1LC | 0RE |
| C | 0RA | 0LD |
| D | 1LA | 0LF |
| E | 0LC | 0RA |
| F | 0RE | --- |

## Status

Open. Proved in Lean (kernel): the halting configurations and the first 10,000 steps (`lean/Blank.lean`, 10^7 with
`native_decide`), and the laws of two of the three parts of the tape for every size (`lean/Counter.lean`,
`lean/Stream.lean`, below). Not decoded: the middle part of the tape, where the rare events that lead to F happen.
C: no halt in 10^11 steps.

## What it does

The run is a cascade of counters. At step 10^9 the tape (cells -191 to 47) splits into three parts, which show up
plainly in the *crossing profile*, the number of times the head moves from each cell to the next one
(`c/cross.c`):

| cells at 10^9 steps | crossings | part |
|---|---|---|
| -191 to -143 | ×3 every 3 cells (1, 11, 111, 1,003, 9,023, 81,209, … 19,736,834) | **N**, a base-3 counter, 16 digits |
| -143 to -60 | 0.5 to 33 million, no simple pattern | the **middle**, not decoded |
| -60 to -15 | ×1/2 every 4 cells (791,259 at -55, 396,417 at -51 … 3,617 at -23) | binary counters with 4-cell digits |
| -15 to 47 | a few hundred, falling to 1 | runs of `10` that grow by one word at rare right-end events |

**The left counter N (proved).** Read the cells left of N's low end three at a time, from the head outward:
`010` = 0, `110` = 1, `100` = 2. Everything left of N is blank. A visit of the head in state A adds one: trailing 2s become 0s, the first other digit goes up by one, and the head comes back out in
state B (no carry) or E (carry). A carry through every digit turns blank cells into a new digit 2.
`lean/Counter.lean` proves this for every number of digits (`n_inc0`, `n_inc1`, `n_inc0_carry`, `n_inc1_carry`,
`n_overflow`), from five token rows (`lean/VisitL.lean`, predicate `VisL`). The wall of `101`s at the left end
that the first description saw is made of N's top digits; its length wanders as N counts.

In the run, the cells left of -122 are entered only in state A, and every one of those 426,172 visits is one of
these five rows, from the first at step 588,436 until step 40,769,252 (`c/vislaws.c`). After that the middle reaches -122: N's low end moves outward
while digits are added at the top, so N stays at about 16 digits (cells -191 to -143 at 10^9, -206 to about -158 at
10^10). The visited region grows mostly because the middle grows (about 15 cells per tenfold time), not because N
does.

**The binary streams (proved).** The right part uses the stream laws found for the sibling
1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RA_0LB--- (family F02, two-word sweeper). In tokens of two cells (`z = 00`,
`a = 10`, `c = 01`): a visit in state B to a stream of a's and z's turns the first z into a and every second a
before it into z (a binary increment, `vb_odd`, `vb_even`, `ve_odd`), and a visit in state A to the counter M with
digits `z c` = 0, `c c` = 1 adds one, with a wrap that sends three visits into the stream after it (`m_inc`,
`m_wrap`). `lean/Stream.lean` proves them for this machine from 29 token rows mined at cell -40
(`lean/VisitR.lean`, proved with this machine's own table; it differs from the sibling's only in D1 and F0).

**The rare events.** The only way into F (whose 1 halts) is D reading 1 (`0LF`). That happened 72 times in the
first 10^8 steps, 74 by 10^9, 81 by 10^10 and 82 by 10^11 (`c/longrun.c`), always with a 0 to the left of D, so F
reads 0. The events come in three kinds (`c/d1ev.c`): at the right end, after `(10)^k` (k grows by one each time),
in a second series a few cells further left, and in cascades in which D appears every 3 cells going left
(`… [1] 0001011 …`), the head walking into N. Whether a cascade can ever put a 1 left of D is the open question.

**Machine family.** Machines 1RB0LE_1LC0RE_0RA0LD_1LA0LF_0LC0RA_0RE---, 1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_0LA---
and 1RB0LD_0LC0RE_1LA0RD_0RB0LF_1RC1LA_0RB--- (mirrored, states renamed) all contain the engine of the F02 two-word
sweepers (prefix 1RB0LE_1LC0RE_0RA0LD_1LA); all three satisfy the same counter law and the same stream laws. They
differ only in D1, E1 and F0, which are used in the middle and at the rare events. The 54 event rules of the F02
sibling (its `lean/Events.lean`) also hold for this table (`events.py` of that folder proves all 54 for it; not
added here), but the
F02 event shape `0^inf 1 0 [N] A> 0 [M] 1 …` never occurs in this run (none in 10^8 steps): here N and M are kept
apart by the middle.

## How far it was run

- Direct C simulation (`c/longrun.c`): 10^11 steps, no halt; at the end cells -215 to 53 (269 cells), 116 ones.
  Cells visited: 164 (10^6), 175 (10^7), 222 (10^8), 239 (10^9), 258 (10^10), 269 (10^11).
- No macro-level accelerator: the counter law and the stream laws describe the outer parts, but the time is spent in
  the middle, whose rules are not known, so no run beyond the direct one was possible.

## Open questions

- Decode the middle (cells -143 to -60 at 10^9): it grows by about 15 cells per tenfold time and eats N's low
  digits. Its crossing profile has steps of 4 cells (halving from -141 to -121) and bumps at -115, -95, -77 and -63,
  as if it held further binary counters fed by wraps.
- Write the rare D1 events (the right-end series and the cascades into N) as rules on the counters.
- Then: can D ever read 1 with a 1 to its left?

## Scripts

- `c/cross.c` (crossing profile), `c/longrun.c` (long run with the halting-state count), `c/d1ev.c` (the tape at
  each use of a transition), `c/vislaws.c` (token-level visit rows on either side of a cell).
- `py/make_lean.py py/lean_config.json lean/` (from this folder) mines the rows again and writes `lean/VisitL.lean`,
  `lean/VisitR.lean`, `lean/Counter.lean` and `lean/Stream.lean` (with `py/gen_visit2.py` and `py/Stream.lean.tpl`,
  the template of the sibling's `Stream.lean`); `py/rows.json` holds the rows.

## Earlier notes

- `bbtools.macro` with blocks of 3 / 6 cells needs one macro step per about 3 / 6-7 steps over 10^7 steps;
  `bbtools.cycles` (k = 4) finds no linear cycle in 10^7 steps; CTL windows up to 8 cells do not close (group scan).
  These remain true: the counters have no long uniform runs for a block machine to skip.

## First look

Growth class **fixed/fixed** (left: fixed, exponent 0.082; right: fixed,
exponent 0.056). After 1,000,000,000 steps: 239 cells visited (191 left of the
start, 47 right), 101 ones.

## Pages

- [`pages/holdouts/1RB0LE_1LC0RE_0RA0LD_1LA0LF_0LC0RA_0RE---/explainer.html`](../../pages/holdouts/1RB0LE_1LC0RE_0RA0LD_1LA0LF_0LC0RA_0RE---/explainer.html)
- [`pages/holdouts/1RB0LE_1LC0RE_0RA0LD_1LA0LF_0LC0RA_0RE---/proof-status.html`](../../pages/holdouts/1RB0LE_1LC0RE_0RA0LD_1LA0LF_0LC0RA_0RE---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LE_1LC0RE_0RA0LD_1LA0LF_0LC0RA_0RE---/lean/check.sh
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same tapes at another pace (observed, not proved).** Leave the states aside and compare only the tape and the place of the head. Then a large part of the first 10^7 configurations of this machine are configurations of the machines below, in the same order and up to the end of the run. The steps at which they occur differ, the tables are not renamings of each other, and equal tapes with different states may be continued differently, so this does not tie the halting questions together.

- [`1RB0LD_0LC0RE_1LA0RD_0RB0LF_1RC1LA_0RB---`](../1RB0LD_0LC0RE_1LA0RD_0RB0LF_1RC1LA_0RB---/README.md) (in a mirror): 9,285,736 configurations, the last at step 9,285,895 here and step 10,000,000 there

<!-- end of related machines -->
