# 1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_0LA---

bbchallenge id 2327. One of the six-state holdouts whose halting from blank tape is open. Its run looks chaotic on a tape that grows roughly logarithmically.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LE |
| B | 1LC | 0RE |
| C | 0RA | 0LD |
| D | 1LA | 1LF |
| E | 0LC | 0RE |
| F | 0LA | --- |

## Status

Open. Proved in Lean (kernel): the halting configurations and the first 10,000 steps (`lean/Blank.lean`, 10^7 with
`native_decide`), and the laws of two of the three parts of the tape for every size (`lean/Counter.lean`,
`lean/Stream.lean`, below). Not decoded: the middle part of the tape, where the rare events that lead to F happen.
C: no halt in 10^11 steps.

## What it does

The same cascade of counters as its close relative 1RB0LE_1LC0RE_0RA0LD_1LA0LF_0LC0RA_0RE--- (they differ in D1, E1
and F0). The crossing profile, the number of times the head moves from each cell to the next one (`c/cross.c`, 10^9
steps), splits the tape (cells -154 to 37) into three parts:

| cells at 10^9 steps | crossings | part |
|---|---|---|
| -154 to about -110 | ×3 every 3 cells (1, 12, 119, 1,068, 9,617, 86,553, 778,985, 7,010,861, …) | **N**, a base-3 counter, about 14 digits |
| -110 to -60 | up to 28 million, no simple pattern | the **middle**, not decoded |
| -60 to -26 | ×1/2 every 4 cells (495,734 at -58, 262,373 at -54 … 2,774 at -26) | binary counters with 4-cell digits |
| -26 to 37 | a few hundred, falling to 1 | runs of `10` growing at rare right-end events |

**The left counter N (proved).** Read the cells left of N's low end three at a time, from the head outward:
`010` = 0, `110` = 1, `100` = 2; blank beyond. A visit of the head in state A adds one: trailing 2s become 0s, the
first other digit goes up by one, and the head comes back out in state B (no carry) or E (carry); a carry through
every digit turns blank cells into a new digit 2. `lean/Counter.lean` proves it for every number of digits
(`n_inc0`, `n_inc1`, `n_inc0_carry`, `n_inc1_carry`, `n_overflow`) from five token rows (`lean/VisitL.lean`).
In the run, the cells left of -100 are entered only in state A, and all 898,777 of those visits are these rows, from
step 533,028 until step 62,483,156 (`c/vislaws.c`); after that the middle reaches -100 and N's low end moves outward
while digits are added at the top. The wall of `101`s at the left end is made of N's top digits.

**The binary streams (proved).** `lean/Stream.lean` proves for this machine the stream laws of the F02 sibling
1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RA_0LB---: in tokens `z = 00`, `a = 10`, `c = 01`, a visit in state B to an a/z
stream is a binary increment (`vb_odd`, `vb_even`, `ve_odd`), a visit in state A to the counter M (digits `z c` = 0,
`c c` = 1) adds one and wraps (`m_inc`, `m_wrap`). From 26 token rows mined at cell -30 (`lean/VisitR.lean`).
This table differs from the F02 sibling 1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_0LC--- only in F0; the 54 F02 event rules
hold for it too (`events.py` of the F02 folder proves them; not added here), but the F02 event shape never occurs in
this run (none in 10^8 steps): N and M are kept apart by the middle.

**The rare events.** F (whose 1 halts) is entered only from D reading 1 (`1LF`): 15 times in the first 10^8 steps,
22 by 10^11, always with a 0 to the left of D, so F reads 0 and goes on with `0LA`.

## How far it was run

- Direct C simulation (`c/longrun.c`): 10^11 steps, no halt; at the end cells -202 to 47 (250 cells), 106 ones; F entered 22 times in all.
- No macro-level accelerator: the time is spent in the undecoded middle.

## Open questions

- Decode the middle (cells -110 to -60 at 10^9 steps); it grows and eats N's low digits.
- Write the rare D1 events as rules on the counters; can D ever read 1 with a 1 to its left?

## Scripts

- `c/cross.c`, `c/longrun.c`, `c/d1ev.c`, `c/vislaws.c` (as in 1RB0LE_1LC0RE_0RA0LD_1LA0LF_0LC0RA_0RE---).
- `py/make_lean.py py/lean_config.json lean/` (from this folder) writes `lean/VisitL.lean`, `lean/VisitR.lean`,
  `lean/Counter.lean`, `lean/Stream.lean`; `py/rows.json` holds the rows.

## Earlier notes

- `bbtools.macro` with blocks of 3 / 6 cells needs one macro step per about 3 / 6-7 steps over 10^7 steps;
  `bbtools.cycles` (k = 4) finds no linear cycle in 10^7 steps; CTL windows up to 8 cells do not close (group scan).

## First look

Growth class **fixed/fixed** (left: fixed, exponent 0.057; right: fixed,
exponent 0.049). After 1,000,000,000 steps: 192 cells visited (154 left of the
start, 37 right), 83 ones.

## Pages

- [`pages/holdouts/1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_0LA---/explainer.html`](../../pages/holdouts/1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_0LA---/explainer.html)
- [`pages/holdouts/1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_0LA---/proof-status.html`](../../pages/holdouts/1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_0LA---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_0LA---/lean/check.sh
```
