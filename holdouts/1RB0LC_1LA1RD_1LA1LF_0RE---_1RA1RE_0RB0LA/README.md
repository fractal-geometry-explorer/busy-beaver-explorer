# 1RB0LC_1LA1RD_1LA1LF_0RE---_1RA1RE_0RB0LA

bbchallenge id 124153, group G08 (two-sided sqrt growth). Whether it halts from blank tape is **open**. Pages:
[`explainer.html`](../../pages/holdouts/1RB0LC_1LA1RD_1LA1LF_0RE---_1RA1RE_0RB0LA/explainer.html), [`proof-status.html`](../../pages/holdouts/1RB0LC_1LA1RD_1LA1LF_0RE---_1RA1RE_0RB0LA/proof-status.html), both built from
[`status.json`](status.json).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LC |
| B | 1LA | 1RD |
| C | 1LA | 1LF |
| D | 0RE | --- |
| E | 1RA | 1RE |
| F | 0RB | 0LA |

## What it does

A bouncer over runs of `01`. Both ends grow like the square root of the step count.

**Where it can halt.** Only in D reading a 1. D is entered only from `B>1` (1RD), so the machine halts exactly when
`B>1 1` occurs. In the first 10^8 steps D is entered 10,419,815 times, always onto a 0 (`c/haltwatch.c`).

**The tape** (`py/snapshots.py 3e7 L 60`, every 60th left-end record):

    1448288 A>0 10110110 (01010010101)^85 01010010110 (01)^5 0 (01)^8 0 (01)^8 0 (01)^5 0 (01)^8 001010 ...
    1705608 A>0 (10101010100)^78 (10)^11 (01)^5 0 (01)^8 (00101010101)^4 (01)^6 0 (01)^5 ...
    ...                (69, 61, 53, 44, 36, 27, 18, 9 at the next samples)
    4678768 A>0 01011001010 (01)^11 0 (01)^5 0 (01)^8 (00101010101)^4 ...

Runs of `01` separated by single 0s, lengths mostly 2, 3, 5, 8, 11; `01010010101` is a run of 2 then a run of 3. The
block at the left end grows and is eaten back, about nine words per sixty left-end visits, again and again (116 words at
step 26,755,844, 339 at step 38,516,556).

## What is proved (Lean)

Only the generated `lean/Blank.lean`: the halting configurations, no halt in 10^4 steps (kernel) and 10^7
(`native_decide`).

## Computed / observed

- No halt in 10^9 steps (`tools/c/triage.c`).
- The halt-entry counts (`c/haltwatch.c`) and the run picture (`py/snapshots.py`).

## Open, and next steps

- The eating of the end block looks regular: a symtm rule for one left-end visit with the block as
  `(01010010101)^m` should be provable, once the right part of the tape is understood well enough to be a context
  the head crosses and comes back from.
- What the cycle does to the run lengths of the rest of the tape is the real question.

## Write-only test at the left end (27 November 2026)

The end-signature screen of 27 November listed this machine's left end as a candidate for a finite end controller
beside a write-only bulk, the structure of DeepMind's proof of 1RB0LD_1LC0RE_---1LD_1LE1LA_1RA0LF_1LC1RE. The direct
test (10^9 steps; a trip leaves a 24-cell window at the end and goes more than 1,000 cells further): **passes, but only because the trips are plain sweeps**.
Computed, not proved: the return state (A, C or F) of all 7,112 deep trips from the left end is fixed by the end word and at most 2 more cells, and at every boundary of the tape the return state of a rightward trip is fixed by 8 cells (64 million deep trips, 236 classes by 16 cells). But a trip takes 5.1 steps per cell of depth. Around step 2.6 million three full sweeps and four short trips repeat at the left end with the same seven end words, and the tape grows by 22 cells per repeat. The left end is periodic, and the halt (`B> 1 1`) can only happen inside the bulk during a sweep, where a finite controller at the end says nothing. Details and the other 11 candidates: [`recent-proofs/followup/write-only-test.md`](../recent-proofs/followup/write-only-test.md).

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB1LC_1LA0RE_0LD---_1LB1LD_1RB1RF_0LA0RB`](../1RB1LC_1LA0RE_0LD---_1LB1LD_1RB1RF_0LA0RB/README.md): rename A→B, B→A, C→E, D→C, E→D, F→F and exchange left and right; it is this table started in state B, in a mirror

<!-- end of related machines -->
