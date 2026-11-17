# 1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---

bbchallenge id 104106. One of the six-state holdouts whose halting from blank tape is open.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LB |
| B | 1RC | 0LA |
| C | 1LB | 0RD |
| D | 1RE | 1RD |
| E | 1RB | 1RF |
| F | 1LA | --- |

**Family:** Nested ternary counter with an exact regime law (segments drained by 3^j per event).

A nested ternary counter: the tape is a list of segments of 111-blocks; an exact three-step law drains the oldest segment by 9 per generation until it runs out at P_14 (step 2.5x10^18). An exact model of the whole tape (16 November 2026) follows the run through that collapse and through the middle collapse at 2.06x10^35 steps, and a lean accelerator (17 November) on through a middle collapse at 2.58x10^54 and the collapse of the third regime's oldest segment at 2.8x10^54 to 3.0x10^54, without a halt, to 3.09x10^54 steps.

## Equivalence

`1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---` (b1, id 104106) and `1RB0LC_1LA0RD_1RA0LA_1RE1RD_1RA1RF_1LC---` (b2, id 44149) have the same table, started in different states: relabelling A->C, B->A, C->B turns b1's table
into b2's, so b2 from blank is b1 started in state B. That is another run of the same table, not the same run: the two share no configuration in 10^7 steps (see Related
machines). At the right records the right ends of their tapes agree (the rest of the tape differs), and the law below holds for both with one constant changed: c0 = 161 for b1, 38 for b2.
This analysis (and its scripts, in `holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/`) covers both.

## What it does

At each step where the head writes a new cell on the right in state D or F, the tape, written as lengths of runs of
1s (the single 0s between runs left out), is

    2 3^16 5 3 5  3^a1 5 3^a2 5 ... 5 3^am  TAIL

blocks `111` separated by single 0s, cut into segments by markers `11111`. The list L = [a1, ..., am] is the state.
Between two such events the head sweeps the whole tape (16 shift rules in `lean/Rules.lean`), so the far (left)
side grows like the square root of the time and the right side very slowly.

## The map

The events come in a cycle of three, P_n, Q_n, R_n (n = -1, 0, 1, ...). With k = n + 1:

    P_n = [g_n, y_n(n), ..., y_n(0), c_n]    g_n = 2*3^(n+5) - 28
                                             y_n(j) = 3^(j+2) * (17 - n + j) - 27
                                             c_n = c0 - 2n     (c0 = 161 for this machine)
    Q_n = [g, g - 3^(k+1) + 1, y_1 - 3^k, ..., y_k - 3, c]           from P_n = [g, y_1..y_k, c]
    R_n = [a + 2*3^(k+4), b - 3^(k+1), z_1 - 3^k, ..., z_k - 3, c - 1]  from Q_n = [a, b, z_1..z_k, c]
    P_(n+1) = the same step again, from R_n

So the segment with i segments on its right loses 3^(k+1-i) blocks per event, the first segment keeps growing, and
each generation adds a segment. A generation costs about 9 times the previous one: P_n is reached at step

| n | b1 step | n | b1 step |
|---|---|---|---|
| -1 | 223,281 | 7 | 526,388,511,969 |
| 0 | 505,965 | 8 | 4,734,432,301,285 |
| 1 | 1,881,665 | 9 | 42,600,703,431,937 |
| 2 | 11,227,329 | 10 | 383,378,775,170,313 |
| 3 | 86,702,753 | 11 | 3,450,326,315,986,929 |
| 4 | 740,547,553 | 12 | 31,052,688,869,335,161 |
| 5 | 6,549,323,129 | 13 | 279,473,455,907,952,089 |
| 6 | 58,601,296,349 | | (b2: P_13 at 279,473,455,907,774,113) |

The law holds while every count stays >= 0. The oldest segment y_n(0) = 9(17 - n) - 27 loses 9 per generation:
y_13(0) = 9, y_14(0) = 0, and Q_14 would need 0 - 3. **The regime ends at P_14.**

**The exact run through the collapse (13 November).** `c/msim.c` ran 55 minutes from blank tape, to step
229,416,990,524,183,704,810, without a halt (`data/b1_far.txt`). The events after P_13:

| event | step | end of the list |
|---|---|---|
| Q_13 | 627,262,429,067,109,861 | on the law |
| R_13 | 1,372,524,234,994,915,593 | on the law |
| P_14 | 2,515,258,871,431,441,221 | on the law: ..., 1431, 378, 81, 0, 133 |
| first new cell on the right after the collapse | 16,989,897,072,297,977,885 | ..., 1341, 348, 204 (second regime) |

(`py/bmap.py b1 saved data/b1_far.txt` checks every event before P_14 and then stops at P_14, because its parser
does not read a segment of length 0; P_14 was compared with the law separately. For b2 only the events that write a
new cell on the right are in the file, two per generation.)

So the law held to its last event, the collapse did not halt, and the second regime starts with the end counter
at 204, which is what the shortened runs below had forecast.

## Halting condition

Not known. Halting needs the head in state D on a 0 with `1 1` to its right (D0 → 1RE, E1 → 1RF, F1 halts), which the law never produces. The first collapse did not produce it either (exact run). Whether a later collapse can needs a rule for the collapses, which is not known yet.

## Beyond P_14 (forecast from shortened tapes; its first part is now confirmed)

The law is right-anchored (a segment's loss depends only on how many segments lie to its right), so the right end of
the real P_13 is also the right end of a short configuration: the m oldest segments y_13(m-1..0), the end counter
c_13, and the generator g = 2*3^(m+4) - 28 that belongs with m segments. `py/bcollapse.py` builds it and runs the
macro simulator. For m = 3, 4, 5 the run passes P_14 and the collapse without a halt; the right end (independent of
m) settles into a second regime of the same kind, e.g. for b1 and m = 4 `[78704 | 37881, 20628, 38529, 12096, 1341,
348 | 204]`, the end counter jumping 133 -> 204 (b2: 12 -> about 81). In that regime the oldest element (321) drops
about 9 per cycle, so the next collapse is about 36 generations later, near 1e46 steps; for b2 the end counter (-2
per cycle) runs out at about the same time, so which happens first is not clear.

## Reproduce

All scripts are in `holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/`:

```sh
python3 py/bmap.py b1 direct 1e9       # the law against every D/F right record of the direct run (c/evrun.c)
python3 py/bmap.py b1 saved data/b1_msim.txt   # against every snapshot of the saved macro run (to 2.8e17)
python3 py/bmap.py b1 macro 1e15       # a fresh macro run (c/msim.c), reaches P_10
python3 py/check_msim.py 2e9              # the macro simulator against tools/c/tmrun.c
python3 py/bcollapse.py b1 4 1e14      # the collapse at P_14 on a reduced configuration
```

`data/b1_msim.txt` and `data/b2_msim.txt` are `c/msim.c MACHINE 4 1e18 - 1`, stopped by hand at 2.8e17 steps;
`data/b1_far.txt` and `data/b2_far.txt` are `c/msim.c MACHINE 4 1e36 - 1 r 3300` (55 minutes, to 2.3e20 steps).

## Deep runs of the whole family (13 November)

`c/msim.c` is not specific to this machine. `py/deep.py run 240` ran it on the 45 machines of the family of block-list
countdown counters (the list is `data/deep.json`): for each one it tries blocks of 2 to 10 cells for 6 seconds, keeps
the size that gets furthest and runs it for 240 seconds from blank tape (this machine and its twin: 55 minutes).
**No machine halted.** `py/deep.py verify` compares the macro run with the direct simulator `tools/c/tmrun.c` after
2x10^9 steps for every machine at the block size used: state, head position and tape agree for all 45. These are
bounded runs and say nothing about later steps.

| machine | block | steps without a halt | seconds | ended |
|---|---|---|---|---|
| `1RB---_1LC0LC_1RD1LB_1LE1RD_0LA1LF_1LD0RF` | 6 | 2.48e+15 | 240 | ran out of room for runs |
| `1RB1LA_1RC1RE_1RD0RD_1LA1RC_1RF0LE_1RA---` | 6 | 7.72e+15 | 240 | ran out of room for runs |
| `1RB1LF_1LC1RB_1LE1LD_1LB0RD_1LF---_1LA0LA` | 6 | 6.60e+17 | 240 | still running |
| `1RB0RE_1LC0RD_1LD0LD_1RA0LC_1RA1RF_1RA---` | 6 | 8.95e+17 | 240 | still running |
| `1RB0RF_1LC0RA_0LD0LB_1RD1LE_0RC0RA_1RA---` | 4 | 9.31e+17 | 240 | still running |
| `1RB---_1RC0RA_1LD0RB_0LE0LC_1RE1LF_0RD0RB` | 4 | 1.24e+18 | 240 | still running |
| `1RB1LF_1LC1RB_1LF1LD_1LE0RD_1LB---_1LA0LA` | 6 | 2.17e+18 | 240 | still running |
| `1RB0LE_0RC0RA_1LC1RD_0LB0LE_1LA0LF_1LE---` | 6 | 2.46e+18 | 240 | still running |
| `1RB0LC_1RC0RC_1LD0RB_1LA0LE_1LD1LF_1LD---` | 4 | 2.49e+18 | 240 | still running |
| `1RB0RE_0RC1RE_1RD1LE_0LE---_1RA1LF_1RF0LC` | 4 | 5.11e+18 | 240 | still running |
| `1RB1LC_0LC---_1RE1LD_1RD0LA_1RF0RC_0RA1RC` | 6 | 5.93e+18 | 240 | still running |
| `1RB1RD_1RC1RB_1LD0RA_1RA0LE_1LF0LC_---1LE` | 6 | 6.65e+18 | 240 | still running |
| `1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD` | 4 | 7.06e+18 | 240 | still running |
| `1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RB---` | 4 | 7.11e+18 | 240 | still running |
| `1RB1LE_1LC1RE_1LE1LD_1LC0LA_1RF0LA_---0RA` | 6 | 7.19e+18 | 240 | still running |
| `1RB1LF_1RC0RA_0RD1RA_1RE1LA_0LA---_1RF0LD` | 6 | 7.45e+18 | 240 | still running |
| `1RB0LC_1LC0RE_1LD1LB_1LA1LD_1RF0RA_---1RE` | 6 | 7.59e+18 | 240 | still running |
| `1RB1RE_1LC0LD_1RA0LD_1LA1LB_0RC1RF_1RC---` | 8 | 1.11e+19 | 240 | still running |
| `1RB1RD_0LC0LB_0RE0LD_1LB0RB_1RF---_0RA0RC` | 6 | 1.24e+19 | 240 | still running |
| `1RB---_1RC1RF_1LD1RA_1LB0LE_1LF1LF_0RB0LD` | 6 | 1.29e+19 | 240 | still running |
| `1RB0LF_0RC0LC_1LA1LD_1RE1LC_---1RA_0LC0RD` | 7 | 1.54e+19 | 240 | still running |
| `1RB0RE_1LC1LF_1RA1LD_0LB---_1RF1LE_0LB0RA` | 6 | 1.68e+19 | 240 | still running |
| `1RB1RE_1LC0RF_1LA0LD_1LE1LC_0RA0LC_1RA---` | 6 | 1.73e+19 | 240 | still running |
| `1RB1LA_0LC0RE_1LD1LB_1RE1LF_1RC0RA_0RC---` | 6 | 1.77e+19 | 240 | still running |
| `1RB1RD_1LC0RF_0LA0RA_1LE1RA_---1LB_0RA0LD` | 7 | 1.97e+19 | 240 | still running |
| `1RB1LF_0RC1RC_1LD0RD_0LE0LA_1RA0LB_---1LD` | 6 | 2.00e+19 | 240 | still running |
| `1RB1LE_1RC1LF_0RD1RD_1LE0RE_0LA0LB_---1LE` | 6 | 2.00e+19 | 240 | still running |
| `1RB0LB_1LC1RE_1LA1LD_0RB1LF_1LA0RC_---1LC` | 6 | 2.04e+19 | 240 | still running |
| `1RB---_0RC0LA_1LD0RB_1LE0LF_1RC1LF_0LC0LB` | 8 | 2.11e+19 | 240 | still running |
| `1RB0RE_1LC0RE_1LA1LD_0LB1LF_1RC1RA_1LB---` | 8 | 2.12e+19 | 240 | still running |
| `1RB0LD_1RC1RE_1LA0LD_1LB1LC_0RA1RF_1RA---` | 8 | 2.12e+19 | 240 | still running |
| `1RB1RC_1LC1LE_1RD0RA_1LB0RA_0LD1LF_1LD---` | 4 | 2.59e+19 | 240 | still running |
| `1RB0RD_0LC0LF_1RD1LB_0RE---_1RA0LC_0LA1LF` | 6 | 2.72e+19 | 240 | still running |
| `1RB1LD_1LC0RE_1LA0LD_0LB0LE_0RB0LF_1RE---` | 8 | 2.78e+19 | 240 | still running |
| `1RB0RF_1LC1RF_1RA0LD_0LC0RE_1LD---_0RC0RD` | 8 | 3.06e+19 | 240 | still running |
| `1RB0LD_1RC0RF_0LD0LE_1RF1LC_0LB1LE_0RA---` | 6 | 3.84e+19 | 240 | still running |
| `1RB0LF_1LC0RC_1RA1LD_0RB0LE_1LC0LB_---1LA` | 6 | 4.49e+19 | 240 | still running |
| `1RB1LD_1RC1RE_1LA0RA_1RC0LB_0LA1RF_---1RB` | 6 | 4.97e+19 | 240 | still running |
| `1RB1LE_0RC---_1RD0LA_1RE0RB_0LA0LF_0LD1LF` | 6 | 5.10e+19 | 240 | still running |
| `1RB0LD_1LC1RE_1LA1RC_1RA0LC_0RF---_0LD1RB` | 9 | 5.31e+19 | 240 | still running |
| `1RB0LB_1RC1LD_1LD0RD_1LE0RC_1LF---_0LA1RF` | 10 | 5.32e+19 | 240 | still running |
| `1RB1LE_0LC1RE_---1LD_0RD1LA_0RF1RF_1RA0LB` | 10 | 6.00e+19 | 240 | still running |
| `1RB0LB_1RC0LA_1RD---_0RE1LD_1LF0RF_1LA1RB` | 10 | 8.13e+19 | 240 | still running |
| `1RB0LC_1LA0RD_1RA0LA_1RE1RD_1RA1RF_1LC---` | 4 | 2.28e+20 | 3300 | still running |
| `1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---` | 4 | 2.29e+20 | 3300 | still running |

## Further work

A rule for the collapses: what the right end looks like after a segment runs out, as a function of the counts. With
that, the run could be followed from regime to regime by computation (the second collapse near 1e46 steps); a
proof of the regime law for all n (one generation as a Lean theorem from the shift rules) would lift the trusted
part to the kernel level.

## Long accelerated run (16 November 2026)

Goal: jump whole generations and collapses, past the forecast collapse near 10^46 steps. No halt was found, and the
run did not get past the next collapse. That collapse comes earlier than forecast, and it is of a different kind.

New tools (in `holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/`, shared by both machines):

* `holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/c/msimev.c` is `holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/c/msim.c` with exact right records. It prints the step count and the tape (as runs of blocks)
  each time the head enters a new rightmost cell in a given set of states. It accepts a run-length start tape
  (`rle:FILE`), so tapes with very long segments can be started directly. Check: all 49 D/F right records up to
  2x10^8 steps agree exactly with the direct simulator, lists and step counts both.
* `holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/lawev.py` implements the general event law and parses the msimev records. `holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/track.py` alternates between
  the law and reduced exact runs at collapses. `holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/midwin.py` is the middle-collapse experiment.
  `holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/rsim.py` is a generic recursive-rule prover; it found no rules here (the junction digits keep whole-tape
  signatures from recurring), and nothing below uses it.

Findings:

1. **General law (trusted).** At D/F right records the list is [g, y_1..y_s, c] (generator, segments, end counter),
   and the events cycle birth, drain, drain:
   * birth: [g, y.., c] -> [2*3^(s+4)-28, g-3^(s+1)+1, y_i-3^(j+1), c]
   * drain: [g+2*3^(s+3), y_i-3^(j+1), c-1]

   Here j is the number of segments to the right of y_i. The generator reset at a birth is new; in regime 1 it
   cannot be seen, because g is already 2*3^(s+4)-28 there. At every P event each segment is exactly
   a*3^(j+1)-27, and every event lowers every coefficient a by 1.
2. **The first collapse, reproduced from the law alone (trusted).** `holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/track.py` simulates the collapse at P_14
   exactly on reduced tapes with m = 4, 5 and 6 kept segments. It splices the three outcomes into the full list,
   fitting the newborn left entries as A*3^s+B (e.g. 324*3^s-28 and g-2*3^(s+1)+1) and draining the hidden segments
   by E = 10 events. The resulting 18-entry list equals the real list at step 16,989,897,072,297,977,885. Every
   later record in `holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/data/b1_far.txt` and `holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/data/b2_far.txt` matches the spliced list continued by the law (the end
   counter to within 2).
3. **The next collapse is in the middle (event 107).** The law, run on from there, reaches P event 105 with
   coefficients (from the left) 51, 48, ..., 12, 9, 24, **2**, 35, 426, 399, ..., 75. The same holds for both
   machines; only c differs (170 for b1, 47 for b2). At event 107 the segment with a = 2 (j = 15, born at the
   first collapse) goes negative. Its position is 18th of 35, not the right end. The step at that point is about
   0.4654*g^2 with g = 300,189,270,593,998,214, which is about 4x10^34 (heuristic fit). The 10^46 forecast assumed
   that the oldest segment runs out first, and is superseded. For b2 the end counter would run out near event 176,
   so the middle collapse also comes first there.
4. **Middle collapse: unresolved here; resolved by the whole-tape run below.** `holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/midwin.py` runs a window around the dying segment exactly, keeping 3 or 7
   neighbours on its left and 3 on its right, with a canonical generator in front. The 7-neighbour run went 3000 s,
   to 1.15x10^19 steps (`holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/data/b1_midwin_l7q3.txt`). Neither run halted, and neither returned to the law. The
   generator becomes small and irregular, and the left neighbours carry over with coefficients one lower and a
   remainder. New births come with coefficients near 497 that fall by 3 per generation. The right part keeps
   draining as before. A model with the left part cut off is therefore not faithful: the collapse merges the
   generator region, and a real resolution needs the whole tape left of the dying segment, which is about 10^17
   blocks wide. So halting is still undecided, and the run so far is exact only up to the first collapse plus
   its law continuation.

Reproduce: `python3 holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/track.py b1 200 /tmp/b1track.log` (it stops at the middle collapse with a note);
`python3 holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/midwin.py 7 3 170 3000`.

## The whole tape as one counter, and the middle collapse (16 November 2026)

Goal: follow the exact run through the middle collapse forecast above, which needs the whole tape, not a window.
Result: **the middle collapse comes at about 2.06x10^35 steps, and neither machine halts there.** Both runs were
followed far past it: b1 to 8.2x10^51 steps, b2 to 2.6x10^54. No halt was found. Halting is still open.

The model. Between two right-end records the head bounces at the left end, and each bounce sends a carry to the
right through a ternary counter that spans the whole tape. A *sample* is the head on a new leftmost cell, in state
A (b1) or C (b2). Read mirrored (the machine `1LB0RB_1LC0RA_1RB0LD_1LE1LD_1LB1LF_1RA---`, or its twin), a sample is
a list of digits, each a run of r blocks `1000` followed by a wall: Z = `100000` (digit 0), O = `1010` (digit 1),
T = `111000` (digit 2), plus a few walls of other shapes that turn up near collapses and births (`b1_1` = `10`,
`b1_2`, `b1_6`, `b2_2`, `b2_3`, named automatically). The tools, in `holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/`:

* `cdigits.py` is the digit model. One sweep (one bounce) is a symbolic run of the machine
  (`tools/py/bbtools/symtm.py`) on a window that holds the carry chain and the digit where it stops, with long
  runs as variables; each rule is cached by its window shape. Check: `python3 cdigits.py check 1e7` compares every
  sample of the direct run with the model: 12,348 sweeps for b1 and (to 2x10^6 steps) 4,655 for b2, no mismatch.
* `tacc.py` stacks sweeps into counter macros, Inc(L) for a place L counted from the far end (the macro algorithm
  of `holdouts/1RB0LF_1LC0RC_1RA1LD_0RB0LE_1LC0LB_---1LA/py/macro4.py`; `caccel.py` is the same counted from the
  head's end, which is not stable here). A macro is derived once per window shape and stands for exactly the
  sweeps it replaces, step counts included; repeated rounds are skipped in bulk while every run stays in the class
  it was derived for. Check: `python3 tacc.py test 1e6 5e6` (and `... b2`): every landing point of 5.07 million
  sweeps equals the plain sweeps, states and step counts.
* `farcheck.py` is an independent check of the long run: it converts the accelerated state just before
  1.7x10^19 steps back to a tape and runs `c/msimev.c` (a block macro simulator that shares no code with the
  model) from it; every later record of `data/b1_far.txt` (the earlier exact msim run, to 7.4x10^19) must come out
  at the same step with the same tape. All three records agree: same tape (as runs of 1s, up to the end run the head is writing) and the step
  count to within 10 (msim reports at the end of its macro step, 8 to 10 steps after the head reaches the new cell).
* `digits_lean.py` proves the 8 most used sweep rules (of the direct run to 2x10^6 steps) in Lean for all lengths of
  the long runs, `lean/Digits.lean` (and the same for b2 in its own folder); 1,210 of the 5,014 sweeps of b1 to
  2x10^6 steps are instances of them.

What the run shows (b1; b2 goes through the same events with different constants, at nearly the same step counts):

1. The accelerated run reproduces every law event checked: the segment lists of the P_n events (for example
   90, 351, 1188, 3861, 12366 with generator 39338 at P_4), P_14 and the first collapse, the end counter 204 after
   it, and the three later msim records of `data/b1_far.txt`.
2. The middle collapse. At 2.060x10^35 steps the segment of coefficient 2 (j = 15, born at the first collapse)
   runs out, as the law said, but later than the 4x10^34 fit. A wall `10` appears in its place, and the two
   neighbouring segments merge: 473,513,913 and 2,841,083,638 become one segment of 3,314,597,534. The counter
   passes through a stretch of mixed O and T digits, then settles into a new all-Z regime. Nothing near a halt
   happens (the halting transition needs state D on a 0 with `1 1` to its right).
3. The new regime (third). From the far end: the end counter c, the segments, each about 3 times the last, the
   newest and largest ones, then a small pair [a, b] with 54a + b = 7262 (a a multiple of 3 between 0 and 132),
   then the fixed part. Each generation takes about 9 times as long as the one before, and c drops by 2 per
   generation, as in the first regime: c = 155, 153, 151, ..., 133 at 8.2x10^51 steps for b1, and 32, 30, 28, ...
   for b2.
4. What comes next. The oldest segment (second from the far end) loses 9 per generation, as y(0) did in the
   first regime: 123, 114, 105, ..., 26 at 8.2x10^51 steps for b1, so it runs out in about 3 more generations,
   near 10^54 to 10^55 steps; that is a collapse of the first kind (the fuse at P_14), now in the third regime.
   For b2 the constants are smaller: at 2.58x10^54 steps the end counter is 3, the oldest segment 3, and a
   segment of 162 blocks has appeared in the middle of the list (another middle collapse under way). All three
   come due within the next generation. The run stopped there because deriving the next macros took more than
   the 14 GB of memory available; nothing in it was near a halt. Getting past this point needs a leaner macro
   cache, not a new idea.

Reproduce (each run checkpoints and can be resumed):

    cd holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py
    python3 cdigits.py check 1e7
    BLAST=1000 python3 tacc.py test 1e6 5e6
    BLAST=1000 MEMO_MAX=300000 SPEC_MEMO_MAX=300000 FULLLOG=/tmp/b1full.log python3 tacc.py run 1e6 28000 /tmp/b1.pkl
    BLAST=1000 MEMO_MAX=300000 SPEC_MEMO_MAX=300000 FULLLOG=/tmp/b2full.log python3 tacc.py run 1e6 28000 /tmp/b2.pkl b2
    python3 farcheck.py b1
    python3 digits_lean.py b1 --check; python3 digits_lean.py b2 --check

`FULLLOG` gets one line with the whole digit list each time the number of digits or the first digit changes;
the main log prints the state every few minutes. BLAST=1000 keeps the last run exact (it is always small), and
the memo bounds keep memory below about 5 GB.

## A lean accelerator, and the collapses at 2.58x10^54 and 3.0x10^54 (17 November 2026)

Goal: get past the point where the counter-macro run stopped (8.2x10^51 steps for b1, 5.3x10^53 for b2; deriving
its macros there needed more than the 14 GB of memory available) and reach the collapses that were due next. Result:
**both machines pass the middle collapse at 2.58x10^54 steps and the oldest-segment collapse at 2.8x10^54 to
3.0x10^54 steps without halting, and both runs are now at 3.09x10^54 steps.** Halting is still open.

`py/lean.py` uses the digit model of `py/cdigits.py` and needs no macro cache. Two exact facts make it work:

1. **The counter rule.** A sweep whose carry chain passes the T digits q..s+1 and stops at digit s turns the T digits
   into Z, raises digit s by one, and takes 1 block (stop on Z) or 2 blocks (stop on O) from the run of digit s+1.
   A run of r blocks in the chain costs 12r + 16 steps, and a stop on O costs 2 steps less than a stop on Z. This was
   checked by symbolic sweeps for stop runs 0 to 9, top runs 1 to 9 and chains of every shape tried; it is what the
   regime law of the right end looks like at the left end.
2. **The low end is periodic.** Take N, a digit with a big run, and S, everything below it (in the third regime: the
   pair a, b and the small gadget at the end of the tape). S sees nothing of the rest of the tape except N's wall,
   so it repeats exactly. In the third regime one period is 14,976 sweeps: N sends 44 carries into the counter above
   it and grows by 7,348 blocks.

So `lean.py` finds the period of S by exact sweeps (Brent's cycle search). Each sweep whose window reaches N is run a
second time with N's run larger by one, which checks that S does not depend on N's run and gives that sweep's step
count as a function of it. Then it does T periods at once in closed form: ternary addition of T*E carries at the
bottom of the counter, the block losses (each a sum over a period-3 pattern), and the step count (arithmetic
series). T is the largest number of periods for which no carry leaves the counter and every run stays >= 1. The
event that blocks the next period (a carry into the far end or into an odd wall) is run exactly. Then S is run on
exactly to the start of its period, and the next jump follows.

Checks (all exact equalities, states and step counts):

* `python3 py/lean.py test CKPT` compares jumps of 1, 2, 3, 5 and 13 periods with plain sweeps: equal at 8.2x10^51
  (b1), next to a small digit after the middle collapse (b2, up to the largest allowed jump of 26 periods), and for
  the 4.26-million-sweep period of the fourth regime (1 and 2 periods, 8.5 million sweeps).
* `python3 py/lean.py verify line0 FULLLOG` runs from the first state of the counter-macro run's full log to every
  later line and compares. All 206 lines of b1 (2.25x10^35 to 8.16x10^51, through the middle collapse at
  2.06x10^35) are equal, in 11 minutes. For b2, all 482 lines checked from line 100 on (3.8x10^14 to 1.3x10^53 steps) are equal. These
  logs are in the project folder, not in the repository (295 MB in all).

What the runs show (b1 and b2 go through the same events at nearly the same step counts; the right ends of their
tapes agree, only the end counter differs):

1. **To 2.58x10^54 steps, the third regime as forecast.** The oldest segment loses 9 per generation, 26 at 8.2x10^51
   down to 3 at 2.58x10^54 (b1). The end counter drops by 2 per generation, 133 down to 126 for b1. For b2 it is at
   3. From the earlier run's checkpoints this took about 10 minutes for each machine.
2. **The middle collapse at 2.5824x10^54 steps.** A middle segment runs out (15 blocks, then 0). The digit it leaves
   (wall `b1_6`) and its neighbours are resolved in a few carries, and the counter goes on. No halt.
3. **A fourth regime.** After that, the low system is nested one level deeper. The pair a, b now sits inside a
   second pair x, y: x counts down, y grows by about 7,300 blocks per 14,976 sweeps, and when x runs out y merges
   into the big digit above. The start values of the x, y pairs repeat with period 4,257,468 sweeps, during which N
   sends 1,383 carries up and grows by 2,072,117 blocks.
4. **The oldest segment runs out.** It reaches 0 blocks at about 2.76x10^54 steps. Its wall then counts Z, O, T as
   an empty digit. At 2.8214x10^54 the carry it passes reaches the far end: the end counter goes 126 -> 127 (b1) and
   3 -> 4 (b2). At about 3.02x10^54 the empty digit is absorbed into the end counter. The tape loses that segment,
   and the next one (293 blocks) becomes the oldest. No halt anywhere: the halting transition (state D on a 0 with
   `1 1` to its right, at the right end of the tape) never comes up.
5. **Where the runs stand.** At 3.093x10^54 steps (b1: 3,093,119,948,897,520,980,264,650,467,058,210,255,920,661,012,668,767,926;
   b2: 3,093,119,948,897,520,980,264,579,279,963,217,281,792,578,051,434,039,981) the far end is `[125]b1_6 [293]Z ...`
   for b1 and `[3]b1_2 [0]b2_3 [293]T ...` for b2. The odd walls at the far end change only when a carry reaches
   them. The next events that could matter are b2's end counter, at 3 blocks and 2 fewer per generation, and the
   next oldest segment, 293 blocks.

Reproduce (each run checkpoints after every jump and can be resumed from its checkpoint or from a state line):

    cd holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py
    python3 lean.py test CKPT.pkl                    # a tacc.py checkpoint, e.g. the one at 8.2e51 steps
    python3 lean.py verify line0 b1full.log          # FULLLOG of tacc.py run (b2: add b2)
    python3 lean.py run ../data/b1_lean_last.txt 86000 /tmp/b1lean.pkl
    python3 lean.py run ../data/b2_lean_last.txt 86000 /tmp/b2lean.pkl b2

`data/b1_lean.log` and `data/b2_lean.log` are the logs of the runs (one line per jump: periods done, step count, the
far end and the bottom of the tape). `data/b1_lean_last.txt` and `data/b2_lean_last.txt` hold the last state (sweeps,
steps, digit list) of each run.

## What is proved, and how firmly

| level | claim | where |
|---|---|---|
| kernel | **The halting configurations.** The machine stops exactly when it reads the symbol of a halting transition (F1); the generated statement covers every configuration. | `step_none_iff`, `lean/Blank.lean` |
| kernel | **No halt in the first 10,000 steps.** The list simulator of the shared library, proved to agree with the machine's semantics, runs 10,000 steps from blank tape without a halt, evaluated by Lean's kernel. | `blank_runs_kernel`, `lean/Blank.lean` |
| native | **No halt in the first 10^7 steps.** The same run, evaluated by compiled code. | `blank_runs_native`, `lean/Blank.lean` |
| trusted | **No halt in the first 10^9 steps.** The C simulator `tools/c/triage.c` runs 10^9 steps without a halt; at the end 294,091 cells have been visited and 168,784 of them hold a 1. | `holdouts/triage.json` |
| heuristic | **Growth shape: exp/sqrt.** Left of the start, the visited part of the tape grows like the square root of the step count, the signature of a head sweeping back and forth across the whole tape and adding a cell or a few at the end of each sweep (a bouncer-like shape) (fitted exponent 0.512). Right of the start it grows like the logarithm of the step count: each new cell costs a roughly constant factor more time, the signature of a counter or of a Collatz-like map whose values are written on the tape (fitted exponent 0.028). | `tools/py/bbtools/triage.py` |
| kernel | **16 shift rules.** For every n, the head crosses n copies of a short word in a fixed number of steps per copy and leaves another word behind (for example A going left over `0111` leaves `0100`, 8 steps a copy; these are the moves that cross the 111-blocks of the counter). Generated and proved by `bbtools.symtm`, checked by Lean's kernel. | `lean/Rules.lean`, generated by `holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/rules.py` |
| trusted | **The regime law, every event to 10^9 steps.** From step 223,270 on, every new cell written on the right in state D or F (16 events up to 10^9 steps) has exactly the list of segment lengths that the law P_n, Q_n, R_n predicts, with g_n = 2*3^n+5-28, y_n(j) = 3^j+2(17-n+j)-27, c_n = 161-2n. | `python3 holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/bmap.py b1 direct 1e9` |
| trusted | **No halt in the first 2.29x10^20 steps, through the first collapse.** The macro simulator (blocks of 4 cells, crossing long runs of equal blocks in one go; exact, and it agrees with the direct simulator at 2x10^9 steps) ran 55 minutes from blank tape to step 229,416,990,524,183,704,810 without a halt. Every right-end event up to P_14 lies on the law, and P_14, at step 2,515,258,871,431,441,221, is exactly the predicted list: the oldest segment is down to 0 and the end counter is 133. The run then leaves the law, as predicted, passes the collapse without halting, and the next new cell on the right comes at step 16,989,897,072,297,977,885 with the end counter at 204; 3 such events are recorded after the collapse. | `holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/c/msim.c MACHINE 4 1e36 - 1 r 3300`; output in `holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/data/b1_far.txt`; `py/check_msim.py` |
| heuristic | **After the collapse: the next one (forecast).** The law only looks at a segment's distance from the right end, so the right end of P_13 was simulated beforehand from a shortened tape with 3, 4 or 5 kept segments. That forecast said the run would pass the collapse at P_14 without halting and that the end counter would jump from 133 to 204; the full exact run has now done exactly that (previous claim). The same shortened runs say that in the second regime the oldest segment (321 blocks) loses about 9 per cycle, so the next collapse would be some 36 generations later, near 10^46 steps. The second regime has no law yet, and nothing is known about that second collapse. | `python3 holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/bcollapse.py b1 4` |
| trusted | **The general event law and the first collapse, reproduced (16 November 2026).** Events cycle birth, drain, drain (formulas in the section above); the collapse at P_14, run exactly on reduced tapes with 4, 5, 6 kept segments and spliced in, gives exactly the real list at step 16,989,897,072,297,977,885, and all later records of the exact run match the law continued from it. | `python3 holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/track.py b1 200 LOG`, `holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/c/msimev.c` |
| heuristic | **The next collapse is in the middle, forecast near 4x10^34 steps** (it comes at 2.06x10^35, see above). At event 107 the segment with coefficient 2 (18th of 35) goes negative, before the oldest segment or the end counter (170 at event 105) runs out; the step count is a fit. Replaces the 10^46 forecast. | `python3 holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/track.py b1 200 LOG` |
| heuristic | **The middle collapse in a cut-down window: no halt, not resolved.** Window runs (to 1.15x10^19 steps) do not halt but never return to the law; the left part of the tape cannot be cut off. | `python3 holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/midwin.py 7 3 170 3000`, `holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/data/b1_midwin_l7q3.txt` |
| trusted | **The whole tape as one exact counter.** Read at the left end, the tape is one ternary counter (runs of `1000`, mirrored, between walls Z, O, T); every sample of the direct run to 10^7 steps equals the model, and the counter macros equal plain sweeps on 5.07 million sweeps. | `py/cdigits.py check 1e7`, `py/tacc.py test 1e6 5e6` |
| trusted | **No halt in the first 8.2x10^51 steps, through the middle collapse.** The whole-tape run reproduces the law events, the first collapse and the msim records (`py/farcheck.py`); the middle collapse comes at 2.060x10^35 steps (two segments merge, then a third regime of the same kind). | `py/tacc.py run`, `py/farcheck.py b1` |
| kernel | **8 sweeps of the digit model, for all run lengths.** The 8 most used sweeps of the direct run to 2x10^6 steps, proved for all lengths of the long runs. | `lean/Digits.lean`, generated by `py/digits_lean.py b1` |
| trusted | **No halt in the first 3.09x10^54 steps, through the middle collapse at 2.58x10^54 and the oldest-segment collapse at 2.8x10^54 to 3.0x10^54.** The lean accelerator (closed-form jumps over periods of the low system, every other sweep exact) reproduces all 206 logged states of the counter-macro run to 8.2x10^51 steps, step counts included, and its jumps equal plain sweeps wherever compared. | `py/lean.py run`, `py/lean.py verify`, `py/lean.py test`; `data/b1_lean.log` |
| open | **Does it halt from blank tape?.** Not known. Halting needs the head in state D on a 0 with `1 1` to its right (D0 → 1RE, E1 → 1RF, F1 halts). The law never produces it, and neither did the first collapse, the middle collapses at 2.06x10^35 and 2.58x10^54, or the oldest-segment collapse at 2.8x10^54 to 3.0x10^54 (exact runs). The next oldest segment holds 293 blocks; the run goes on from 3.09x10^54 steps. |  |

## Lean

`lean/Rules.lean` is generated by `holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/rules.py` (one script for all eight machines of this worker;
`--check` compares the files instead of writing them) and is listed in `lean/check.sh` after `Blank.lean`:

`lean/Digits.lean` (8 sweeps of the digit model) is generated by `holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/digits_lean.py b1` (`b2` writes the twin's file) and
listed after `Rules.lean`:

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/lean/check.sh
python3 holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/rules.py --check
python3 holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/digits_lean.py b1 --check
```

## Pages

- [`pages/holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/explainer.html`](../../pages/holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/explainer.html)
- [`pages/holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/proof-status.html`](../../pages/holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/proof-status.html)

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0LC_1LA0RD_1RA0LA_1RE1RD_1RA1RF_1LC---`](../1RB0LC_1LA0RD_1RA0LA_1RE1RD_1RA1RF_1LC---/README.md): rename A→C, B→A, C→B, D→D, E→E, F→F; it is this table started in state B

<!-- end of related machines -->
