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

One near miss is worth recording; the next section settles it as far as it can be settled.

## The mirror pair: no proof from the tables

The tables of `1RB1LF_1RC1RF_0LD1RE_---1LC_0RB1RE_1LA0LE` (X) and the mirror image of
`1RB1RF_1LC1LF_0RE1LD_0LB1LD_---1RC_1RA0RD` (Y), with D and E swapped, agree except in the direction of A0, and
both halt only on the same transition. **Result: no argument about the two tables can prove that they halt together,
and none can prove that they do not.** Whether they do is a question about their particular runs from blank tape.

**How the runs differ.** Both machines have exact pass maps: Y's `next` (proved in Lean, `lean/Phases.lean` in Y's
folder) and X's `step` (`py/model.py` in X's folder). X's right-end visit `T(none, c, a)` is the mirror image of Y's
pass start `PS a c = B> 0 0 (10)^a 1^c`, so the two maps act on the same states. They agree at every pass start with
c even (checked at all 39,800 with a < 200, c < 400). The tables differ only where a pass ends at the tape end with a
single 1 left. That happens only in an *odd event*, when c is odd, and odd events are the only places where either
machine can halt. There the maps part: Y rebounds
off the end, while X leaves a *bracket* `(01)^k 1` behind and its right part restarts from a small seed.
`py/partner.py lag` in Y's folder follows both runs. In the first 2·10⁵ passes the pattern is always the same. The
runs part at an odd event. Later, after X's bracket has been absorbed, X's run is Y's run again, delayed by a few
passes (0, then 2, then 4). The odd events out to 3·10⁸ passes show the same thing, with delays of 4 and 6. The
pass map is two-to-one, so different runs keep falling together.

| pass | event |
|---|---|
| 0–2 | the same run |
| 3 | they part (Y `PS 0 12`, X `T(none, 13, 0)`) |
| 49–82 | the same run again |
| 83 | they part |
| 153 | X is Y delayed by 2 passes |
| 495 | they part |
| 581 | X is Y delayed by 4 passes |
| … | the same pattern: seven partings and seven rejoinings in 2·10⁵ passes |

The halting tests are not the same, though. An odd stretch that starts at `PS 0 A`, or at X's odd pool A, halts iff
A = 2^(k+2) − 2k − 3 for some k. That is the same test for both machines, but it is applied to different lists
(`py/partner.py events`, 3·10⁸ passes):

- Y's odd stretches start at A = 5, 61, 165, 253, 989, 1021, 1853, 13309, 26333, 44669, 67581, 19855861, 169438117,
  213734333, 283866789;
- X's odd pools without a bracket are A = 5, 13, 165, 989, 1853, 13309, 26333, 44669, 49909, 19855861, 169438117,
  283866789. Its pools behind a bracket cannot halt.

Most values are shared, but 61, 253, 1021, 67581 and 213734333 occur only in Y, and 13 and 49909 only in X. No value
on either list is a halting value. A future halting value could fall on the list of one machine only.

**Lean: halting together is not a property of the tables** (`lean/Partner.lean` in Y's folder). The file takes two
pass-start tapes c of Y and X's mirror images `mirror c` of them:

- from `PS 0 39`, Y reaches its own run from blank tape (phase 83, `ps_0_39_iff`), but X halts from
  `mirror (PS 0 39)` after 44,274 steps (`partner_halts_39`);
- from `PS 22 3`, Y halts (`ps_22_3_halts`), but X, from `mirror (PS 22 3)`, reaches the configuration of its own
  blank-tape run at step 730,147 after 1,499,945 steps (`partner_iff_22_3`, by `native_decide`).

`together_forces_halts` then says that if the two machines halted together on these two pairs of tapes, both would
halt from blank tape. Both are open holdouts that run 10⁸ phases or more without halting. So an equivalence proof
cannot be uniform over tapes: it has to use the runs from blank tape themselves. A non-equivalence proof would have
to show that one of the machines halts. `py/partner.py local` lists many more such tapes (for example `PS 0 37`,
`PS 0 42` and `PS 1 24`).

## Pairs whose runs differ by one inserted word (17 November 2026)

The F09 pair 1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE / 1RB0RA_0LC0RF_0LB1RD_1LE---_1RA0LF_1LE0RC was settled by a
relation the re-sync search above cannot see: the two runs are not step-aligned, but one tape is the other with one
word more. A new search looked for that kind of relation everywhere.

**Screen.** `tools/c/extev.c` recorded the new-extreme events of all 608 holdouts to 10^9 steps; `tools/py/evfp.py`
ranked pairs by shared k-grams of (side, change in the number of 1s), plain and mirrored; `tools/c/evdiff.c` compared
the tapes of candidate pairs at matching tape-end events and kept those whose difference stays one short word. Then
`tools/c/inslock.c` was run on all 287 pairs of open holdouts with one table (`related.json`): it finds a moment where
one configuration is the other with a word inserted, then follows the shorter run step by step. When the head crosses
the place of the word, the longer run must cross the word in the state it entered (a *transparent crossing*), or the
word may move one cell along a matching cell (a *shift*). Every 10^8 steps the longer run is simulated to the matching
step and compared cell by cell.

**Result.** 10 pairs stay related in this way for 3·10^9 steps (with `NOEXC=1`, exactly the rules of the Lean file
below). Four are the known T63 group of F09 (1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB--- and its three partners). The
other four pairs are new, and each was checked from the exact starting relation of its Lean file to 10^10 steps
(`tools/c/inscheck.c`):

| pair | word, where | crossings in 10^10 steps | what it means |
|---|---|---|---|
| 1RB0LF_1LC0LA_---1RD_1RF1RE_1LF1RD_1LB0RE / 1RB1RF_1LC0RF_1LE0LD_1RC0LB_---1RA_1LB1RA (F01) | one copy of the period-10 block `1011011011`, 5 cells from the left end | 94,671, all in state A going left or D going right | the regular left part has one copy more; the irregular region that decides halting is the same in both |
| 1RB---_0RC0RF_0RD0RA_1RE0LB_1LF0LE_1RC0LE / 1RB0RA_1LC0RA_0LF0LD_1LE---_0LC0LB_1LA0RE (F11) | `01010101` in the background, about 440 cells from the right end | 210,678 | one block of the second machine's sweep counter is 4 longer (same parity) |
| 1RB0RA_0RC0RE_1LD1LF_1LE0LC_1RA0LD_0RA--- / 1RB0RE_1LC0RA_1LD0LC_0LE0LB_1RA1RF_0LC--- (F08) | `0101`, about 250 cells from the left end | 377 | |
| 1RB0LD_1RC1RE_1LA0LD_1LB1LC_0RA1RF_1RA--- / 1RB0RE_1LC0RE_1LA1LD_0LB1LF_1RC1RA_1LB--- (F06) | `0101` near the right end | 64 | the second item list is the first with one item 2 longer (all 2·10^7 sweeps checked on the item model of the first machine); that item drifts into the far-end items where a halt would be decided, so this coupling probably breaks before it matters |

**Lean.** `tools/lean/TM/Insert.lean` proves the general statement `halts_iff_of_good`: if `c'` is `c` with a word
inserted and the followed run of `c` never reaches a bad moment (`Good`), then `c` halts if and only if `c'` does.
`holdouts/insert_pair.py` writes a file `lean/Insert_<partner>.lean` for each pair (state renaming or mirror, the two
starting configurations by `decide`, the starting relation), with **`halt_together`: if `GoodPair` holds, the two
machines halt from blank tape together.** `GoodPair` is not proved for any of the four. A local window argument like
the one that settled the F09 pair (`RightEnd.lean`) does not close here: with the rest of the tape left free, the head
can come back to the word in states that the real runs never use (a search over windows of 15 to 45 cells at the left
end of the F01 pair, not kept in the repository, always reached bad configurations). Proving `GoodPair` needs a fact about the whole run, for example for
the F01 pair that the head reaches the left part only in state A after a full pass.

```sh
gcc -O2 -o inslock tools/c/inslock.c && NOEXC=1 ./inslock 1RB0LF_1LC0LA_---1RD_1RF1RE_1LF1RD_1LB0RE D 3000000000 100000000 q 44 4 3000
gcc -O2 -o inscheck tools/c/inscheck.c && NOEXC=1 ./inscheck 1RB0LF_1LC0LA_---1RD_1RF1RE_1LF1RD_1LB0RE D 1 A 85 r 1 1011011011 10000000000
python3 holdouts/insert_pair.py 1RB0LF_1LC0LA_---1RD_1RF1RE_1LF1RD_1LB0RE 1RB1RF_1LC0RF_1LE0LD_1RC0LB_---1RA_1LB1RA Y 1 85
. /etc/profile.d/lean.sh && holdouts/1RB0LF_1LC0LA_---1RD_1RF1RE_1LF1RD_1LB0RE/lean/check.sh
```

The other starting relations: `inscheck 1RB---_0RC0RF_0RD0RA_1RE0LB_1LF0LE_1RC0LE E 3 A 26 r 1 01010101`,
`inscheck 1RB0RA_0RC0RE_1LD1LF_1LE0LC_1RA0LD_0RA--- D 0 A 15 r 1 0101`,
`inscheck 1RB0LD_1RC1RE_1LA0LD_1LB1LC_0RA1RF_1RA--- A 11 C 18 r 1 0101`.

No pair here is a proved equivalence, so the count of distinct open questions does not change, but four pairs of
questions are now reduced to one condition each.

## Trying to prove GoodPair (17 November 2026)

**Result: `GoodPair` is not proved for any of the four pairs, and for the first three it cannot be proved without
understanding the irregular part of the machine.** For the fourth pair the coupling itself fails: `GoodPair` is
false there (by the item model, not in Lean), at sweep 72,734,792,369, about 1.0·10^22 steps.

**F01** (1RB0LF_1LC0LA_---1RD_1RF1RE_1LF1RD_1LB0RE / 1RB1RF_1LC0RF_1LE0LD_1RC0LB_---1RA_1LB1RA). At each pass the
tape is `0 (011)^4 (1011011011)^k I`. To 10^10 steps (47,331 passes, `c/engine.c` in the first machine's folder):
k grows by one block about every 7 passes and shrank only once (pass 255); the rest I, the *engine*, stays between
126 and 520 cells and never repeats; its first 33 to 70 cells are a 7-periodic *emitter* that hands one block to the
left part per period; 20 cells inside the blocks every pass crosses right once in D and left once in A. The engine
never sees k, so the partner (one block more) runs the same engine, and `GoodPair` says exactly that the engine
never eats back through all the blocks. A proof from the left part alone is impossible: with the boundary at the end
of the blocks or 30 cells into the emitter, an adversary that may send the head across in any state reaches more
than 3,000 contents, about 200 irregular visits to the left end and over 1,000 halts (`py/shield.py`). So
`GoodPair` needs a description of the engine, the same thing the halting question needs.

**F11 and F08.** The same test (`tools/py/shield.py`, any machine, any end) on the region holding the extra word
(460 cells from the right end of 1RB---_0RC0RF_0RD0RA_1RE0LB_1LF0LE_1RC0LE, 260 from the left end of
1RB0RA_0RC0RE_1LD1LF_1LE0LC_1RA0LD_0RA---) also grows past 3,000 contents with over 900 halting visits. The word sits
next to the defect region in the first and in the left counter in the second, both of which are not understood.

**F06** (1RB0LD_1RC1RE_1LA0LD_1LB1LC_0RA1RF_1RA--- / 1RB0RE_1LC0RE_1LA1LD_0LB1LF_1RC1RA_1LB---). The partner is the
first table run from state C. In the item model of the first machine (its README) the partner's first item list is
[(2,0),(5,1)] against [(2,0),(3,1)]: one item 2 longer. `c/items_pair.c` runs both item lists in step and checks
after every sweep that the partner's tape is the first one with four cells more. The extra length always sits in
one of the last three items, the far-end leftovers; at the rare sweeps that reach them it moves between them, and
the item holding it shrinks (value 64 at sweep 395, 12 at 10^8, 9 at 2.2·10^9, 3 at 2.2·10^10, 1 at 4.5·10^10). Twice early on (sweeps 11 and 12)
the item lists differ in shape but the tapes still differ by four cells only. At sweep 64,144,857,777 the lists part
in shape again (a merge in the first run, a plain sweep in the partner) with the tapes still four cells apart. Then
at sweep 72,734,792,369 (step 1.016·10^22 of the first run) the first run's sweep reaches the end of its list and
does an end reset, which turns every separator into a 1 and puts a new item (2,0) in front, while in the partner the
same sweep stops at an earlier item. Afterwards the lists are

    first:    (2,0) (53885261825,1) (19134581049,1) ... (145,1) (55,1) (1,1)
    partner:  (53885261828,0) (19134581049,0) ... (145,0) (53,0) (1,0) (0,1)

The tapes already differ in the sixth cell and again near the right end, so the partner's tape is no longer the
first one with a word inserted, and `GoodPair` fails (`Good` would keep `Rel` true at every sweep start). This
rests on the item model, which is exact against the machine wherever it was compared (its README) but is not
proved in Lean; checking the break cell by cell is out of reach at 10^22 steps. It does **not** show that the two
machines differ on halting: after the break their halting questions are simply not tied by this coupling.

**The map pair** 1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_---0RE / 1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE, which the
map sweep flagged as running in step. Both phase maps are proved in Lean (`lean/Phases.lean` in each folder). With
phi: e(x, z) -> e(x, z), r(x, y) -> a(x, y - 1), q(m, k, t) -> q(m, k/2, t), the maps commute (up to a skipped
phase) on every phase with parameters below 14 except the all-ones phases r(0, y) and the phases q(0, k, 0)
(`py/partner.py check` and `orbits` in the second folder). The runs therefore travel together and part only at
all-ones tapes: in the first 2·10^5 phases of the first machine they part 4 times, each time just after a shared
all-ones tape (lengths 5, 279, 5882, 12114 in the first, 4, 278, 5881, 12113 in the second), and rejoin each time
after a few hundred to a few thousand phases. The first machine's other all-ones tapes (10, 71, 466, 763, ...) fall
in stretches where the runs are apart. But the all-ones tapes are exactly where both machines
decide halting, and there the tests disagree. By the fatal lists proved in each folder's `lean/Phases.lean`
(`fatal_list`, all n < 10^5), the first halts from the all-ones tape r(0, n) exactly for n = 0, 6 and
32·2^k − 2k − 12, the second from a(0, n − 1) exactly for n − 1 = 3 and 28·2^j − 2j − 13. These never meet:
32·2^k − 2k − 13 = 28·2^j − 2j − 13 would need 2^(j+2)·(2^(k−j+3) − 7) = 2(k − j), which has no solution. So at a shared all-ones moment (below 10^5, and at every length if the formulas hold beyond) at most one of them halts: the maps cannot show that the two
machines halt together, and they are two questions, like the mirror pair above.

## F05 twins: ten pairs with one question each (18 November 2026)

Twenty F05 machines come in pairs whose exact block-list runs (`f05_run.py`) have the same block list at every
recorded left-end event and the same number of F-events to 10^200 steps. The two machines of a pair are the core in
the same frame with the same start state, and their frame-A tables differ only in D1 and F0. Since F is entered only by
D1, the two runs are identical until D reads a 1. The re-sync search at the top of this page failed on these F-row
variants because it needed a re-sync in every context a tape language allows. Here the contexts where the re-sync fails
are allowed: they become the shared question. A symbolic simulation of both machines from D reading 1, with every
other cell unknown, finds the window that makes them meet again (`holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---/py/gen_twins.py`):

- if the cell left of D is 1, F reads it and both machines halt;
- if the window holds (`0 0 D>1` for seven pairs, `1 0 0 0 D>1 1` for the three pairs where one machine has F0 = 0LE),
  the machines meet again in the same configuration after the step counts shown, for every tape around;
- otherwise the configuration is *bad*, and the two machines may part there.

**Lean.** `tools/lean/TM/Resync.lean` proves the general statement `TM.halt_together`. If two machines agree at every
synchronised configuration that is not a segment start, never halt there, and every segment start that is not bad
either re-synchronises or makes both halt, then their runs from a common start meet a bad configuration together, and
if they never do, the machines halt together. Each pair has a generated file `lean/Twin.lean` in the folder of its
first machine. It checks the three hypotheses for every configuration (`resync`; the window cases by computation)
and states **`halt_together`: the two frame-A runs from blank tape reach a bad configuration together, and if they
never do, the two machines halt from blank tape together** (through each machine's `halts_iff`). All ten compile in
the kernel with no `sorry`; the axioms are `propext`, `Classical.choice` and `Quot.sound`.

| machine | twin | frame, start | frame A: D1 / F0 | window | steps to meet |
|---|---|---|---|---|---|
| 1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RE--- | 1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LB--- | A, A | 0LF / 0RE vs 0LF / 1LB | `0 0 D>1` | 2 / 4 |
| 1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0LE--- | 1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LA--- | A, A | 0LF / 0LE vs 0LF / 1LA | `1 0 0 0 D>1 1` | 22 / 2 |
| 1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_0RE--- | 1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_1LB--- | A, A | 1LF / 0RE vs 1LF / 1LB | `0 0 D>1` | 2 / 4 |
| 1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_0LB--- | 1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_1LD--- | A, A | 1LF / 0LB vs 1LF / 1LD | `0 0 D>1` | 4 / 2 |
| 1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1RE--- | 1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_1LD--- | B, C | 0LF / 1LB vs 1LF / 1RA | `0 0 D>1` | 3 / 3 |
| 1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_0RC--- | 1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_0LA--- | B, C | 0LF / 0LE vs 1LF / 0RC | `1 0 0 0 D>1 1` | 16 / 2 |
| 1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_0RE--- | 1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_1RB--- | B, C | 1LF / 0LB vs 1LF / 1LD | `0 0 D>1` | 4 / 2 |
| 1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0RA--- | 1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA1RF_0LD--- | G, E | 0LF / 0LE vs 1LF / 0RC | `1 0 0 0 D>1 1` | 16 / 2 |
| 1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0LA--- | 1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_1RC--- | G, E | 0LF / 0RE vs 0LF / 1LB | `0 0 D>1` | 2 / 4 |
| 1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA1RF_0RC--- | 1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA1RF_1RE--- | G, E | 1LF / 0LB vs 1LF / 1LD | `0 0 D>1` | 4 / 2 |

**What it means.** Every F-event in the family's runs (all 39 run machines, to 10^200 steps) has the tape
`1 0 0 0 D>1 1` around the head, which is inside both windows. That is the context `fevent` in `Family.lean` proves
harmless. So no observed run reaches a bad configuration, and any non-halting proof along the F05 plan (show that every
F-entry is of the proved kind) covers both machines of a pair at once. These are not unconditional equivalences:
`Halts X ↔ Halts Y` is proved only under the shared condition, which is itself open. In the strict count below the
number of distinct open questions does not change, but for planning, these twenty machines are **ten questions**.

The other near-identical F05 runs are pairs with the same frame-A table and a different start; they are the next
section.

```sh
python3 holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---/py/gen_twins.py --check   # pairs, windows, step counts
python3 holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---/py/gen_twins.py --records # writes lean/Twin.lean and records
. /etc/profile.d/lean.sh && holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---/lean/check.sh   # (or any pair's folder)
```

## F05 start twins: one table, two starts (18 November 2026)

Fourteen F05 machines come in seven pairs that are one frame-A table started in state A and in state C. From the
fourth left-end event on, the two block lists agree except that the first block of the start-C run is 16 longer:

| left-end event | step from A | block list | step from C | block list |
|---|---|---|---|---|
| 4 | 284 | [16] | 1,241 | [32] |
| 5 | 537 | [16, 8] | 1,574 | [32, 8] |
| 6 | 4,658 | [12, 16, 44] | 5,775 | [28, 16, 44] |
| 7 | 221,839 | [8, 114, 368, 104] | 223,036 | [24, 114, 368, 104] |

(the pair 1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA--- / 1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_0LD---; the first rounds are
the same for all seven). At a left-end event nothing is written left of the head, so the start-C tape is the start-A
tape with 32 more alternating cells, the word `(10)^16`, inside the first block. That is the inserted-word relation of
`TM/Insert.lean`, and here it can be followed: each round crosses the word twice in the state it entered, once when
the first block is spread into `(1000)^q` and once when it is folded back, and in between the head stays further right
(it only touches the last cells of the spread block). The start-C run is exactly 80 steps slower per round.

**Lean.** `tools/lean/TM/Rounds.lean` proves `TM.good_of_rounds`: the condition `Good` of `TM.halts_iff_of_good`
(the followed run never reaches a bad moment) splits into one statement per round, if each round ends with the word in
one of a set of allowed places. Each pair has a generated file `lean/StartTwin.lean` in the folder of its start-A
machine (`holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---/py/gen_starttwins.py`). A left-end event `E m X` is the
head in state A at the left end, nothing on its left, `m` alternating cells `0 1 0 1 ...` and then any tape `X` (for
the block list [b1, ..., bk], m = 2 b1 + 2). The file proves:

- **`event_rel`, the lemma about block lists:** for every m, every place n inside the run and every tape X,
  `E (m + 32) X` is `E m X` with the word inserted after n cells;
- the two runs reach `E 34 blank` (the list [16], step 284 from A) and `E 66 blank` (the list [32], step 1,241 from
  C), by `decide`;
- **`halt_together`:** if `RoundGood m X` holds at every left-end event `E m X` of the start-A run, the two machines
  halt from blank tape together. `RoundGood m X` says that one round from `E m X`, with the word anywhere inside the
  alternating run, never reaches a bad moment, or reaches the next left-end event with the word inside its alternating
  run again.

All seven compile in the kernel with no `sorry` (Lean 4.34.0); the axioms are `propext`, `Classical.choice` and
`Quot.sound`.

**The condition.** `RoundGood` fails when a round uses up the first block of the start-A run: then the head of that
run reaches the place of the word in a state that does not cross it, and the start-C run, with 16 more, goes on
differently. On 3,000 random block lists (first block 0 to 30, up to five more blocks of 1 to 120;
`period.c`-style runs of 1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA--- from `E l` and from `E l` with the first block 16
longer, to the next left-end event) the two rounds ended differently in 496 cases. In 307 of them the start-A first
block had run down to 3 or less, in 187 it had merged with the next block, and in the other two (first blocks 1 and 2)
the start-C round was still running at 10^8 steps. With a first block of 6 or more, only 18 of 2,379 rounds ended
differently. In the real runs:

| start A | start C | left-end events to 10^200 steps | F-events | lists agree |
|---|---|---|---|---|
| 1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA--- | 1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_0LD--- | 505 | 278 | all |
| 1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RB--- | 1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_0LE--- | 524 | 200 | all |
| 1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LB--- | 1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1RE--- | 520 | 292 | all |
| 1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LC--- | 1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1RA--- | 577 | 192 | all |
| 1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1RA--- | 1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1LD--- | 566 | 240 | all |
| 1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_1LB--- | 1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_1RE--- | 546 | 193 | all |
| 1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_0LD--- | 1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_0RB--- | 58 (to 10^22 steps, `hybrid2.py`) | 21 | all |

(`py/start_twins_check.py`; both runs have the same numbers, and the first block of the start-A run stays at 6 or
more.)

The coupling itself (`tools/c/inscheck.c`, the rules of `TM.tnext` exactly) holds cell by cell for 10^10 steps for all
seven pairs, and `gen_starttwins.py --check` checks `RoundGood` for every place of the word on the first three rounds.
Four more A/C pairs of the family have the same first rounds but part later, each time when the start-A run's first
block runs out:
1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0LC--- / 1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_0RA--- at the seventh left-end
event (step 90,636; the start-A list goes [12, 16, 44] → [3, 116, 50, 176]),
1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0LE--- / 1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_0RC--- at event 23 (step
1.1·10^11; [4, 8, 4078, ...] → [4042, 121952, ...], the first block merges), and
1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_0LB--- / 1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_0RE--- and
1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_1LD--- / 1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_1RB--- at event 168 (step
2.1·10^69; [4, 18, 10822, ...] → [3, 10728, ...]). For these the condition is false and `StartTwin.lean` is not
generated.

**What it means.** Like the ten twins above, these are conditional: `Halts X ↔ Halts Y` is proved under a condition on
one run that is itself open. But the condition says only that the start-A run's first block never runs out during a
round, a fact any non-halting proof along the F05 plan has to establish anyway. Two of the pairs join twin classes
of the previous section: 1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LB--- links the twins 1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RE---
and 1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1RE--- into one class of four (with 1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_1LD---),
and 1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_1RE--- joins the twins 1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_0RE--- /
1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_1LB---. Together the twins and start twins put **31 machines into 14 questions**.

```sh
python3 holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---/py/gen_starttwins.py --check    # start relation, first rounds
python3 holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---/py/gen_starttwins.py --records  # writes lean/StartTwin.lean and records
python3 holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---/py/start_twins_check.py 1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA--- 1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_0LD---
gcc -O2 -o inscheck tools/c/inscheck.c && NOEXC=1 ./inscheck 1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA--- A 284 C 1241 r 1 10101010101010101010101010101010 10000000000
. /etc/profile.d/lean.sh && holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---/lean/check.sh
```

## Count

Of the 552 open holdouts, none are newly proved equivalent here. The one-way implication
`1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RB_0RC---` ⇒ `1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RC---` was already known, and
both machines are claimed halting upstream. **552 distinct open questions remain.** Ten F05 twin pairs and seven F05
start-twin pairs (above) now share questions under proved conditions: 31 machines in 14 classes, so for planning
purposes they count as 14 questions, not 31. The relations in `related.json`
still say which questions are likely to have the same answer and should be attacked together, but none of them is a
proved equivalence.

## Reproducing

```sh
python3 tools/py/syncpair.py find X Y out.json --window 4     # or --sat; prints CLOSED or OPEN with the failing context
python3 tools/py/syncpair.py lean out.json Namespace > P.lean # a closed certificate as a Lean proof
python3 tools/py/syncpair.py resync X Y 3e5                   # the combined run and its breaks
python3 holdouts/1RB1RF_1LC1LF_0RE1LD_0LB1LD_---1RC_1RA0RD/py/partner.py lag 40000   # the mirror pair, pass by pass
gcc -O2 -o cfghash tools/c/cfghash.c && ./cfghash X 300000000 4096
gcc -O2 -o engine holdouts/1RB0LF_1LC0LA_---1RD_1RF1RE_1LF1RD_1LB0RE/c/engine.c && ./engine 1e10 20
python3 holdouts/1RB0LF_1LC0LA_---1RD_1RF1RE_1LF1RD_1LB0RE/py/shield.py 30 3e7 3000
python3 tools/py/shield.py 1RB0RA_0RC0RE_1LD1LF_1LE0LC_1RA0LD_0RA--- L 260 2e7 3000
gcc -O2 -o items_pair holdouts/1RB0LD_1RC1RE_1LA0LD_1LB1LC_0RA1RF_1RA---/c/items_pair.c && ./items_pair 1e11
python3 holdouts/1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE/py/partner.py check 14
```
