# 1RB0LC_1LA0RD_1RA0LA_1RE1RD_1RA1RF_1LC---

bbchallenge id 44149. One of the six-state holdouts whose halting from blank tape is open.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LC |
| B | 1LA | 0RD |
| C | 1RA | 0LA |
| D | 1RE | 1RD |
| E | 1RA | 1RF |
| F | 1LC | --- |

**Family:** Nested ternary counter with an exact regime law (segments drained by 3^j per event).

A nested ternary counter: the tape is a list of segments of 111-blocks; an exact three-step law drains the oldest segment by 9 per generation until it runs out at P_14 (step 2.5x10^18). An exact model of the whole tape (16 November 2026) follows the run through that collapse and through the middle collapse at 2.06x10^35 steps, without a halt, to 2.58x10^54 steps, where three more collapses come due at once.

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
                                             c_n = c0 - 2n     (c0 = 38 for this machine)
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
227,980,806,246,614,777,399, without a halt (`data/b2_far.txt`). The events after P_13:

| event | step | end of the list |
|---|---|---|
| Q_13 | 627,262,429,066,930,655 | on the law |
| P_14 | 2,515,258,871,431,259,069 | on the law: ..., 1431, 378, 81, 0, 10 |
| first new cell on the right after the collapse | 16,989,897,072,297,794,501 | ..., 1341, 348, 81 (second regime) |

(`py/bmap.py b1 saved data/b1_far.txt` checks every event before P_14 and then stops at P_14, because its parser
does not read a segment of length 0; P_14 was compared with the law separately. For b2 only the events that write a
new cell on the right are in the file, two per generation.)

So the law held to its last event, the collapse did not halt, and the second regime starts with the end counter
at 81, which is what the shortened runs below had forecast.

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
python3 py/bmap.py b2 direct 1e9       # the law against every D/F right record of the direct run (c/evrun.c)
python3 py/bmap.py b2 saved data/b2_msim.txt   # against every snapshot of the saved macro run (to 2.8e17)
python3 py/bmap.py b2 macro 1e15       # a fresh macro run (c/msim.c), reaches P_10
python3 py/check_msim.py 2e9              # the macro simulator against tools/c/tmrun.c
python3 py/bcollapse.py b2 4 1e14      # the collapse at P_14 on a reduced configuration
```

`data/b1_msim.txt` and `data/b2_msim.txt` are `c/msim.c MACHINE 4 1e18 - 1`, stopped by hand at 2.8e17 steps;
`data/b1_far.txt` and `data/b2_far.txt` are `c/msim.c MACHINE 4 1e36 - 1 r 3300` (55 minutes, to 2.3e20 steps).

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
4. **Middle collapse: unresolved.** `holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/midwin.py` runs a window around the dying segment exactly, keeping 3 or 7
   neighbours on its left and 3 on its right, with a canonical generator in front. The 7-neighbour run went 3000 s,
   to 1.15x10^19 steps (`holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/data/b1_midwin_l7q3.txt`). Neither run halted, and neither returned to the law. The
   generator becomes small and irregular, and the left neighbours carry over with coefficients one lower and a
   remainder. New births come with coefficients near 497 that fall by 3 per generation. The right part keeps
   draining as before. A model with the left part cut off is therefore not faithful: the collapse merges the
   generator region, and a real resolution needs the whole tape left of the dying segment, which is about 10^17
   blocks wide. So halting is still undecided, and the run so far is exact only up to the first collapse plus
   its law continuation.

This machine is b2; the window runs were made with the b1 table and c = 170, and are taken to stand for both (the right part and the dying segment are the same; not run separately). Reproduce: `python3 holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/track.py b2 200 /tmp/b2track.log` (it stops at the middle collapse with a note);
`python3 holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/midwin.py 7 3 170 3000`.

## The whole tape as one counter, and the middle collapse (16 November 2026)

The whole-tape model and its runs are described in [`1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---`](../1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/README.md) (section of the same name);
the scripts there take `b2` for this machine. For this machine:

* `python3 holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/cdigits.py check 2e6` with `BMACH=b2`: 4,655 sweeps, every sample of the direct run
  equals the model; `BLAST=1000 python3 holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/tacc.py test 1e6 5e6 b2`: the macros equal plain sweeps.
* The run goes through the same events as the other machine, at nearly the same step counts and with different
  constants: the first collapse, then the middle collapse at about 2.06x10^35 steps (no halt), then a third regime
  where the end counter drops by 2 and the oldest segment by 9 per generation (end counter 32, 30, 28, ...).
* **No halt to 2.58x10^54 steps.** There the end counter is 3, the oldest segment 3, and a segment of 162 blocks has
  appeared in the middle of the list (another middle collapse under way); all three come due within the next
  generation. The run stopped there because deriving the next macros needed more than the 14 GB of memory
  available. Nothing in it was near a halt.
* **Past it with the lean accelerator, to 3.09x10^54 steps (17 November 2026).** `py/lean.py` (in the other
  machine's folder; it jumps whole periods of the low part of the counter in closed form and runs every other sweep
  exactly) takes this machine through the middle collapse at 2.58x10^54 steps and the collapse of the oldest segment
  (its carry reaches the far end at 2.82x10^54 and raises the end counter from 3 to 4; the emptied digit is absorbed
  by about 3.0x10^54). No halt. At 3,093,119,948,897,520,980,264,579,279,963,217,281,792,578,051,434,039,981 steps the
  far end is `[3]b1_2 [0]b2_3 [293]T ...`, so the end counter (3) and the new oldest segment (293) are the next things
  to come due. Run: `python3 holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/lean.py run STATE b2`, with the
  state line in `data/b2_lean_last.txt` of that folder; the log is `data/b2_lean.log`.
* **On to 6.1x10^135 steps (18 November 2026)**, with no halt. The same tool now reuses learned cycles, so a
  generation takes seconds. The end counter drops 3 -> 2 -> 1 and at 4.80x10^54 merges with the oldest segment
  (1 + 290 -> 291). A middle collapse follows at 3.70x10^54. From 1.1x10^55 on, a regular run of middle collapses
  follows: each takes 2 blocks from the oldest segment and multiplies the step count by about 9. At 6.1x10^135 the far end
  is `[0]b2_3 [118]T ...`; at this rate that segment runs out near 10^192 steps (a fit). Log: `data/b2_lean2.log` in
  the other machine's folder.
* **The next collapse tried ahead of time (20 November 2026).** Each cycle the oldest segment loses exactly 2
  blocks and the j-th exactly 3^j, on all 71 logged cycles. The oldest segment (148 blocks at 3.0x10^121) runs
  out first, near 10^192. Setting it to 0 on today's tape and running on exactly, the empty digit is absorbed, the
  next segment (1008 blocks) becomes the oldest and the usual far-end cycle resumes. No halt (a forecast for the real
  tape, which will have more bottom digits by then). The details are in the other machine's README.
* `lean/Digits.lean`: the 8 most used sweeps of the direct run to 2x10^6 steps (1,225 of 5,128 sweeps), proved for
  all run lengths (`python3 holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/digits_lean.py b2`).
* **A short rule table, and the generic sweep for every carry length (21 November 2026).** Every exact sweep rule
  of a run over one cycle (296 from 7x10^175, `data/rule_table_b2.txt` in the other machine's folder) is a stop rule
  plus a carry chain that does not depend on its length, the same table as for the other machine. `lean/Chain.lean`
  proves the generic sweep (carry over any list of T digits, stop on Z or O) for every list and all run lengths
  (`sweepZ`, `sweepO`; `python3 holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/chain_lean.py b2`). The
  details are in the other machine's README.

## What is proved, and how firmly

| level | claim | where |
|---|---|---|
| kernel | **The halting configurations.** The machine stops exactly when it reads the symbol of a halting transition (F1); the generated statement covers every configuration. | `step_none_iff`, `lean/Blank.lean` |
| kernel | **No halt in the first 10,000 steps.** The list simulator of the shared library, proved to agree with the machine's semantics, runs 10,000 steps from blank tape without a halt, evaluated by Lean's kernel. | `blank_runs_kernel`, `lean/Blank.lean` |
| native | **No halt in the first 10^7 steps.** The same run, evaluated by compiled code. | `blank_runs_native`, `lean/Blank.lean` |
| trusted | **No halt in the first 10^9 steps.** The C simulator `tools/c/triage.c` runs 10^9 steps without a halt; at the end 293,599 cells have been visited and 133,391 of them hold a 1. | `holdouts/triage.json` |
| heuristic | **Growth shape: exp/sqrt.** Left of the start, the visited part of the tape grows like the square root of the step count, the signature of a head sweeping back and forth across the whole tape and adding a cell or a few at the end of each sweep (a bouncer-like shape) (fitted exponent 0.514). Right of the start it grows like the logarithm of the step count: each new cell costs a roughly constant factor more time, the signature of a counter or of a Collatz-like map whose values are written on the tape (fitted exponent 0.042). | `tools/py/bbtools/triage.py` |
| kernel | **16 shift rules.** For every n, the head crosses n copies of a short word in a fixed number of steps per copy and leaves another word behind (for example A going left over `0111` leaves `0100`, 8 steps a copy; these are the moves that cross the 111-blocks of the counter). Generated and proved by `bbtools.symtm`, checked by Lean's kernel. | `lean/Rules.lean`, generated by `holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/rules.py` |
| trusted | **The regime law, every event to 10^9 steps.** From step 103,844 on, every new cell written on the right in state D or F (16 events up to 10^9 steps) has exactly the list of segment lengths that the law P_n, Q_n, R_n predicts, with g_n = 2*3^n+5-28, y_n(j) = 3^j+2(17-n+j)-27, c_n = 38-2n. | `python3 holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/bmap.py b2 direct 1e9` |
| trusted | **No halt in the first 2.28x10^20 steps, through the first collapse.** The macro simulator (blocks of 4 cells, crossing long runs of equal blocks in one go; exact, and it agrees with the direct simulator at 2x10^9 steps) ran 55 minutes from blank tape to step 227,980,806,246,614,777,399 without a halt. Every right-end event up to P_14 lies on the law, and P_14, at step 2,515,258,871,431,259,069, is exactly the predicted list: the oldest segment is down to 0 and the end counter is 10. The run then leaves the law, as predicted, passes the collapse without halting, and the next new cell on the right comes at step 16,989,897,072,297,794,501 with the end counter at 81; 4 such events are recorded after the collapse. | `holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/c/msim.c MACHINE 4 1e36 - 1 r 3300`; output in `holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/data/b2_far.txt`; `py/check_msim.py` |
| heuristic | **After the collapse: the next one (forecast).** The law only looks at a segment's distance from the right end, so the right end of P_13 was simulated beforehand from a shortened tape with 3, 4 or 5 kept segments. That forecast said the run would pass the collapse at P_14 without halting and that the end counter would jump from 10 to 81; the full exact run has now done exactly that (previous claim). The same shortened runs say that in the second regime the oldest segment (321 blocks) loses about 9 per cycle, so the next collapse would be some 36 generations later, near 10^46 steps; for this machine the end counter (−2 per cycle) runs out at about the same time, so the outcome of that second collapse is unclear. The second regime has no law yet, and nothing is known about that second collapse. | `python3 holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/bcollapse.py b2 4` |
| trusted | **The general event law and the first collapse, reproduced (16 November 2026).** Events cycle birth, drain, drain (formulas in the section above); the collapse at P_14, run exactly on reduced tapes with 4, 5, 6 kept segments and spliced in, gives exactly the real list at step 16,989,897,072,297,977,885, and all later records of the exact run match the law continued from it. | `python3 holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/track.py b2 200 LOG`, `holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/c/msimev.c` |
| heuristic | **The next collapse is in the middle, near 4x10^34 steps.** At event 107 the segment with coefficient 2 (18th of 35) goes negative, before the oldest segment or the end counter (47 at event 105) runs out; the step count is a fit. Replaces the 10^46 forecast. | `python3 holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/track.py b2 200 LOG` |
| heuristic | **The middle collapse in a cut-down window: no halt, not resolved.** Window runs (to 1.15x10^19 steps) do not halt but never return to the law; the left part of the tape cannot be cut off. | `python3 holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/midwin.py 7 3 170 3000`, `holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/data/b1_midwin_l7q3.txt` |
| trusted | **The whole tape as one exact counter.** Every sample of the direct run to 2x10^6 steps equals the whole-tape model, and the counter macros equal plain sweeps on 5.07 million sweeps. | `py/cdigits.py check 2e6`, `py/tacc.py test 1e6 5e6 b2` (scripts in the other machine's folder) |
| trusted | **No halt in the first 2.58x10^54 steps, through the middle collapse.** The middle collapse comes at about 2.06x10^35 steps; the run stops at 2.58x10^54 steps, out of memory, where the next collapses come due. | `py/tacc.py run ... b2` |
| trusted | **No halt in the first 3.09x10^54 steps, through the middle collapse at 2.58x10^54 and the oldest-segment collapse at 2.8x10^54 to 3.0x10^54.** The lean accelerator reproduces 482 logged states of the counter-macro run (3.8x10^14 to 1.3x10^53 steps), steps included, and its jumps equal plain sweeps where tested; every sweep outside the jumped periods is exact. | `py/lean.py run ... b2`, `py/lean.py verify ...` (other machine's folder) |
| trusted | **No halt in the first 6.1x10^135 steps, through the end counter running out at 4.8x10^54 and about 87 more middle collapses.** The lean accelerator with cycle reuse reproduces the logged states of the counter-macro run and of the slower lean runs (all 47 states from 5.1x10^55 to 2.8x10^59 with the cycle cache), step counts included. | `py/lean.py run ... b2` (other machine's folder) |
| heuristic | **The collapse near 10^192 does not halt (tried ahead of time).** On today's tape with the oldest segment set to 0, the exact run absorbs it, the next segment takes over and the usual cycle resumes. | `py/probe.py` and `data/probes/` (other machine's folder) |
| kernel | **8 sweeps of the digit model, for all run lengths.** | `lean/Digits.lean`, generated by `py/digits_lean.py b2` |
| kernel | **The generic counter sweep, for every number of carry digits.** Carry over any list of T digits, stop on Z or O, all run lengths. | `sweepZ`, `sweepO`, `lean/Chain.lean`, generated by `py/chain_lean.py b2` |
| trusted | **The sweep rules form a short table.** Every exact rule over one cycle is a stop rule plus a length-independent carry chain. | `py/ruletable.py table b2`, `data/rule_table_b2.txt` in the other machine's folder |
| open | **Does it halt from blank tape?.** Not known. Halting needs the head in state D on a 0 with `1 1` to its right (D0 → 1RE, E1 → 1RF, F1 halts), which the law never produces. The first collapse did not produce it either (exact run). Whether a later collapse can needs a rule for the collapses, which is not known yet. |  |

## Lean

`lean/Rules.lean` is generated by `holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/rules.py` (one script for all eight machines of this worker;
`--check` compares the files instead of writing them) and is listed in `lean/check.sh` after `Blank.lean`:

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LC_1LA0RD_1RA0LA_1RE1RD_1RA1RF_1LC---/lean/check.sh
python3 holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/rules.py --check
```

## Pages

- [`pages/holdouts/1RB0LC_1LA0RD_1RA0LA_1RE1RD_1RA1RF_1LC---/explainer.html`](../../pages/holdouts/1RB0LC_1LA0RD_1RA0LA_1RE1RD_1RA1RF_1LC---/explainer.html)
- [`pages/holdouts/1RB0LC_1LA0RD_1RA0LA_1RE1RD_1RA1RF_1LC---/proof-status.html`](../../pages/holdouts/1RB0LC_1LA0RD_1RA0LA_1RE1RD_1RA1RF_1LC---/proof-status.html)

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---`](../1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/README.md): rename A→B, B→C, C→A, D→D, E→E, F→F; it is this table started in state C

<!-- end of related machines -->
