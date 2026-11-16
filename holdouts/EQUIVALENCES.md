# Machines whose halting questions are the same

Can the 552 open holdouts be grouped so that one proof settles several of them? This page reports a search for
pairs that provably halt together, beyond the relations already found by `related.py` (`related.json`: the same table
with another start, the same run, slowed copies, the same tapes up to a shift or mirror). **The result is negative.
No new pair could be proved cheaply, so 552 distinct open questions remain.** The tools stay in `tools/` for later
use.

## Method

**Re-sync bisimulation (`tools/lean/TM/Sync.lean`, `tools/py/syncpair.py`).** X and Y run on one tape. A *pair* (p, q)
means both runs have the same tape and head, X is in state p and Y in state q. A closed tape language (the windows
of `bbtools.ctl`, or two DFAs found by SAT) covers every configuration of X's run from blank tape. For each pair and
each abstract configuration of X in state p, the checker expands cells next to the head as needed. It must find
either n ≥ 1 steps of X and m ≥ 1 steps of Y after which the tape and head agree again (a new pair), or a halt of
both. When every pair reachable from (A, A) closes, `TM.Sync.halts_iff` proves `Halts X ↔ Halts Y` with one
`decide` per certificate. `tools/lean/Test/Sync.lean` is a small worked example: BB(2) against a copy that takes a
three-step detour.

With `--sat`, the SAT search is a loop. Each context where the bisimulation fails is added as a forbidden
(state, left word, right word) to satctl's encoding, without its no-halt clauses, and the search runs again for
DFAs that exclude every forbidden context.

**Configuration hashes (`tools/c/cfghash.c`).** For candidates beyond `related.json`, this tool hashes each
configuration's tape relative to the head, forward and mirrored. It samples a configuration when its hash is
divisible by a modulus, so the sample depends only on the tape and not on the history. Every holdout was run for
3·10⁸ steps. Whenever two machines shared a sampled hash, the pair was aligned and run together.

## Results

**The known relations.** The 51 pairs already in `related.json` were all run through the re-sync checker,
unrestricted, over window languages of 2 to 14 cells, and over SAT DFAs of up to 8 + 8 states. None of them closes.
Siblings that differ in one transition part exactly at the rare events that decide halting. Typical cases:

- **F05 F-row variants.** Examples are `1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0LE---` and
  `1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LA---`. They part only at F events, about 2 per 2·10⁶ steps. Re-syncing then
  takes 21 steps of one against 1 of the other, and needs about 17 cells of left context that no small regular
  language pins down.
- **F03.** `1RB0RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_0RB---` and `1RB0RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_1RC---` re-sync only
  when a counter at F entry is in one residue class. There were 4 F events in 10⁹ steps.
- **F02.** `1RB1RF_1RC0RF_0RD0LC_1LE1RA_1LC---_0LD0RE` and `1RB1RF_1RC0RF_0RD0LC_1LE1RA_1LC---_1RB0RE` need "F reads 0
  only with a 1 to its left". That holds for 10⁸ steps, but no DFA invariant up to 8 × 8 states rules out the
  opposite.
- **Same table, different start (F05).** `1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---` and
  `1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_0LD---` have the same F-event counts out to 10²⁰⁰ steps (block level), but
  their configurations never coincide within 3·10⁹ steps. At 7.29·10⁸ steps the interior blocks agree
  ([465, 135, 1171, 1776, 8606]), while the first block (2 against 10) and the tail differ. An equivalence would
  need a proof at the level of blocks, not a local re-sync.

**New candidates from the hash screen.** The screen found 23 pairs that share sampled tapes and are not in
`related.json`. The table shows a combined run of 3·10⁵ steps from blank tape with `syncpair.py resync`:

- **ok:** every time the runs parted, they re-synced within 40 + 40 steps. The table gives the number of breaks.
- **fail:** at the step shown, in the state pair shown, they never re-sync locally.
- **fail at step 0 or 1:** the shared tapes are in different frames or at other times, so the runs do not start out
  together.

| kind | X | Y | 3·10⁵ steps together | breaks |
|---|---|---|---|---|
| F | `1RB0LC_0RC0RE_1RD1LF_1LE0RA_0LA0LE_0RB---` | `1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_1RE---` | ok | 1131 |
| F | `1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_0RC---` | `1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_0LA---` | ok | 2 |
| F | `1RB---_0LC0LB_1RF0LD_1RE0RB_1LB0RC_0RD1RA` | `1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA1RF_0RE---` | fail at 1 (BB) | 0 |
| F | `1RB---_0LC0LB_1RF0LD_1RE0RB_1LB0RC_0RD1RA` | `1RB1LF_1LC0RD_0LD0LC_1RE0LA_0RA0RC_0RE---` | fail at 1 (BB) | 0 |
| F | `1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA1RF_0RE---` | `1RB1LF_1LC0RD_0LD0LC_1RE0LA_0RA0RC_0RE---` | fail at 49250 (EA) | 326 |
| F | `1RB0LC_0RC0RB_1LD0RE_0LE0LB_1LA1RF_0LD---` | `1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_0RE---` | ok | 1110 |
| F | `1RB0LC_0RC0RB_1LD0RE_0LE0LB_1LA1RF_0LD---` | `1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_1LB---` | ok | 1111 |
| F | `1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0RA---` | `1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA1RF_0LD---` | ok | 2 |
| F | `1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD0LC_0RC---` | `1RB0LB_0RC0LF_1LD1RE_0LA0RB_0RD0RF_0LA---` | ok | 136 |
| F | `1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD0LC_0RC---` | `1RB0LB_0RC0LD_1LD1RE_0LA0RF_1RB0RD_0RB---` | ok | 25030 |
| F | `1RB0LC_0RC0RE_1RD1LF_1LE0RA_0LA0LE_0RB---` | `1RB0LD_0LB1RC_0RD---_1RE0RF_1LF0RA_0LA0LF` | ok | 31213 |
| F | `1RB0RC_1LC0RD_0LD0LC_1RE0LA_0LE1RF_0RA---` | `1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA1RF_0RE---` | fail at 59376 (AE) | 5063 |
| F | `1RB0RC_1LC0RD_0LD0LC_1RE0LA_0LE1RF_0RA---` | `1RB1LF_1LC0RD_0LD0LC_1RE0LA_0RA0RC_0RE---` | ok | 25565 |
| F | `1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF` | `1RB0RE_1RC0RC_1LD---_0LB1LE_1RF0LD_1RA1RF` | fail at 680 (CD) | 34 |
| F | `1RB1LC_0RC0RB_1LD0LA_1LE---_1LF1RA_1LA1LC` | `1RB1LE_1RC0RB_1LD1RC_1LA1LE_1LF0LA_1LC---` | fail at 2412 (BB) | 182 |
| F | `1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE` | `1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_---0RE` | fail at 13 (CE) | 1 |
| F | `1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_---0RE` | `1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_---0RE` | fail at 17 (DE) | 1 |
| F | `1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_---0RE` | `1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE` | fail at 35 (CD) | 3 |
| F | `1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_---1LB` | `1RB0RF_1RC1RF_1LD0LE_---1LC_1RA1LE_1LC1RB` | fail at 7 (BB) | 1 |
| F | `1RB0LA_0RC---_0RD0RF_1LD0LE_0LA1LE_1RA0RE` | `1RB0LA_0RC0RF_0RD0RA_1LD0LE_0LA1LE_---1LB` | fail at 44 (AB) | 1 |
| F | `1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RA_0LB---` | `1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RA_0LE---` | fail at 92914 (CB) | 10 |
| M | `1RB1LF_1RC1RF_0LD1RE_---1LC_0RB1RE_1LA0LE` | `1RB1RF_1LC1LF_0RE1LD_0LB1LD_---1RC_1RA0RD` | fail at 0 (AA) | 0 |
| M | `1RB1RA_0LC0RF_1LD1LC_1RE1LB_---0RA_1RF0RD` | `1RB1RA_1LC1RE_---0LD_1LE1LD_0RA0LF_1LF0LB` | fail at 3 (CB) | 1 |

(F: same tapes; M: mirror image, Y run with its directions reversed.)

The ten "ok" pairs travel together for 3·10⁵ steps. All of them still part at rare events where a local
re-sync needs context that no window or SAT-DFA language of the tried sizes can supply, so the symbolic closure stays
open. In every case where it was measured, the rare events are the F-row or end-of-tape events, the same events
the holdouts' own halting questions depend on.

One near miss is worth recording. The tables of `1RB1LF_1RC1RF_0LD1RE_---1LC_0RB1RE_1LA0LE` and the mirror image of
`1RB1RF_1LC1LF_0RE1LD_0LB1LD_---1RC_1RA0RD` agree except in the direction of A0, and their halting transitions
correspond. A0 occurs only at left-end events, 6 times in 3·10⁹ steps. The two runs' pass counts diverge and later
re-merge (both reach (46, 16)), so an equivalence may hold, but proving it would take a proof about the macro
dynamics, not a re-sync certificate.

## Count

Of the 552 open holdouts, none are newly proved equivalent here. The one-way implication
`1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RB_0RC---` ⇒ `1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RC---` was already known, and
both machines are claimed halting upstream. **552 distinct open questions remain.** The relations in `related.json`
still say which questions are likely to have the same answer and should be attacked together, but none of them is a
proved equivalence.

## Reproducing

```sh
python3 tools/py/syncpair.py find X Y out.json --window 4     # or --sat; prints CLOSED or OPEN with the failing context
python3 tools/py/syncpair.py lean out.json Namespace > P.lean # a closed certificate as a Lean proof
python3 tools/py/syncpair.py resync X Y 3e5                   # the combined run and its breaks
gcc -O2 -o cfghash tools/c/cfghash.c && ./cfghash X 300000000 4096
```
