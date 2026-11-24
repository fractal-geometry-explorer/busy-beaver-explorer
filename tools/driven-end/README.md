# Driven ends: finding the split that busycoq PR #110 uses

busycoq PR #110 (ccz181078/busycoq, November 2026) proves that `1RB0LA_1LC1RF_---1LD_1RE0LA_1RA0RB_1RE0RF` and
`1RB0RA_1RC0RD_1RD0LC_1LE1RA_---1LF_1RB0LC` never halt. The proof splits the tape into a counter, which never reads
the rest of the tape, and a messy end. The counter only sends *calls* into the end, and every call comes back in a
fixed state. The end is then a separate system driven by a known stream of calls, and the proof analyses it column
by column with small transducers and a rational potential. (Our notes on the PR are in the project files,
`notes/busycoq-prs-110-112.md`.)

The tools here look for that split in any machine, and run the end on its own once it is found.

| file | what it does |
|---|---|
| `pcross.c` | `pcross MACHINE STEPS ERASIDE ENDSIDE [MINLEN]`. A *round* starts each time the head extends the tape on `ERASIDE`. At the start of a round it finds the maximal periodic runs (period at most 12, at least `MINLEN` cells and 4 periods) and cuts the tape after the last one (`ENDSIDE` R) or before the first one (L; `FIRST=1` cuts after the first run instead). It then logs every crossing of that cut during the round: `X` (upper case) is the head entering the end in state X, `y` (lower case) is the head coming back in state Y. One line per round: round, step, end size, tape width, period of the run, crossings. With `DUMP=1` the end's cells at the start and at the end of the round follow (read outward from the cut). |
| `pscan.py` | runs `pcross` on every undecided holdout (`holdouts/families.json`), both round sides and both end sides, and keeps the rounds whose crossings are *pure*: only pairs `Xy` (a call and its return). Writes `pscan.json`. |
| `reflect.c` | `reflect MACHINE SCHED Y INIT CALLS [EVERY]`, the end on its own. Cell 0 is the first cell of the end and a wall stands left of it. Call i enters cell 0 in state `SCHED[i mod len]`. When the head steps onto the wall in state Y, the call is over and the next one starts. Stepping onto the wall in another state is reported as a violation. |
| `check_reflect.py` | checks `reflect` against the whole machine: the end at the start of a round, fed that round's calls, must be the end at the end of the round. |
| `rctl.py` | a closed tape language (windows of K cells, as in `tools/py/bbtools/ctl.py`) for the end on its own, with the wall on the left. It reports `closed` when it finds a closed set, or the abstract configurations that halt or hit the wall in the wrong state. |
| `survey-table.md` | the pure splits that `pscan.py` found (10^8 steps per machine and side). |

## What was checked

* On the PR #110 machine `1RB0LA_1LC1RF_---1LD_1RE0LA_1RA0RB_1RE0RF`, `pcross 1RB0LA_1LC1RF_---1LD_1RE0LA_1RA0RB_1RE0RF
  300000000 L R` finds the split without being told: every round is a block of calls entering in E, then a block
  entering in F, all returning in A (`E405 F148` near step 3·10^8). This is the two-letter event stream of the
  PR's proof, seen at a cut one run further out.
* `python3 check_reflect.py 1RB0LA_1LC1RF_---1LD_1RE0LA_1RA0RB_1RE0RF 300000000 L R 100`: the end-only run reproduces
  the end exactly in each of the last 100 rounds (`100 of 100`). (`reflect` prints at most 300 cells, so the
  check applies only to ends shorter than that.)
* `rctl.py` on that end, fed E calls only, from a blank end, K = 3 to 8: no closed set (abstract halts with C on a 0).
  This agrees with the earlier failed flat searches on this machine. A closed language of windows does not
  capture the counter-like end.

## What the survey found (24 November 2026)

41 (machine, side) pairs among the undecided holdouts have pure rounds with a fixed return state for each entry state
and an end of at least 12 cells (`survey-table.md`). Almost all of them are families already studied here:

* the zone and cascade machines (`1RB0RB_1RC1RA_0LD1LC_0RA1LE_1LF0LC_---1LA` and its relatives): one call per round, and
  the end is the XOR cascade already in Lean there;
* the reservoir counters (`1RB1RD_1LC0LC_1RD1LB_1RF0RE_0RA1RE_---1RB`, `1RB1RD_1LC1RA_---1LD_1LE0RA_1LF0LE_0RB0LB`):
  constant calls into a chaotic counter, where the events at the far end are expected to come eventually;
* the clock and word-map machines (`1RB0LC_1LC0RB_0LE1LD_1LB1LA_0RA1LF_0LA---`, `1RB0LA_1RC---_1RD1RA_1LE1RF_1LC1LE_0RC0RD`,
  `1RB1RE_1LC1RD_1LA1LC_0RA0RB_1RF0LE_1RA---`): 2^k identical word-map steps per tick;
* the PR59 visit-law machines (`1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD---`, `1RB0LB_0RC0LD_1LD1RE_0LA0RF_1RB0RD_0RB---`), whose
  end is already a proved token-level call system (`lean/Visit.lean`), the closest analogue of PR #110's event rules;
* up/down and two-level block counters whose end is a fixed-width binary counter (`1RB0RF_1RC1LB_1LD1RE_1LB0LD_1RF0RC_1RA---`,
  `1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LB`, `1RB1LD_1RC0RB_1LA1RC_1LE0LA_1LF---_1LC---`): run alone, the end stays at 77, 69 and 61 cells for
  2·10^7 calls without repeating;
* the four machines of the list-of-counters family R13 (`1RB1RF_1LC0LB_1RE0LD_1LB0RF_0RA0RC_1RE---` and relatives).

No new family turned up. In the PR #110 machine the end is driven by a *two-letter* stream whose blocks grow every
round, and the proof's potential bound uses those growing blocks. In most of the families above the end gets one
identical call per round, so it runs on its own, and in the reservoir and clock families something is expected to
happen at the far end eventually (an event or a phase end). The visit-law machines are the exception and the best fit
for the PR's column-by-column method: a token-level event system already proved in Lean, whose open question is
whether a visit ever meets `111`.

The split is found by a heuristic (the cut after a periodic run) and is not proved. A proof also has to show that the
counter side really never reads the end, as `era_step` does in PR #110.
