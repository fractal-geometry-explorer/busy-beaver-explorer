# The run from blank tape, followed to width 2⁴³ (untrusted)

The machine's own run from blank tape in the mark model, cycle by cycle (one clean tape to the next), with every round
start of three walls analysed as it comes: which pass starts the run passes, how it reaches them (an entry into the
loop, or a landing of the loop's chain after a full pass, a half pass or a round-7 break), which entry of its cycle
each chain comes from, and how close each pass start comes to the eight halting families
(`../lean/thm/PassOpenHalt.lean`), to the halting lanes Q = 2^(j+2), to failing the wide condition W ≤ 64R + 6 or
15W ≤ 64(W − b), and to the clean-tape classes the exhaustive check leaves open. None of it is proved; the engine
follows the proved rules and stops on anything they do not cover.

## What the run does to width 2⁴³

From the first round start the model reaches the first clean tape of width at least 2⁴³ (n = 4,398,046,511,105, width
2⁴³ + 8) after 484,888,773,759 cycles and 2,466,400,605,902 rounds, with no halt and no uncovered round; the
trailing-wall canonical form is never written. The clean tape of width exactly 2⁴² (n = 2,199,023,255,549) comes after
242,444,389,027 cycles and 1,233,200,303,024 rounds. Tables: `results/tables.md`; data: below.

*Against the earlier follower.* Where the notes give numbers for `../csearch/fastfollow.c` (a different program,
table lookups of settled classes), they agree: the first clean tape past 10¹² is n = 10¹² + 1 after 110,250,943,953
cycles (the notes: 110,250,943,952; the count here includes the cycle from blank tape to n = 2), the 11-meeting cascade
at n = 37,558,132,238 comes back at 140,637,347,342, and there is a 14-meeting cascade at n = 391,305,139,022. Past
10¹² the closest end meeting of the run improves once more, to 14.39 halvings at n = 3,185,173,435,214 (width
6.4 × 10¹², another 14-meeting cascade); 285 cycles have cascades of 11 meetings or more, 8 of 13 or more.

*Pass starts.* 1,806,203,417 of them (every three-wall round start but 52), 3.7 per 1,000 cycles at every width. How
the run reaches them: 1,798,389,396 entries, 7,530,068 half-pass landings, 81,139 round-7 breaks, 52,379 full-pass
landings, and 150,435 pass starts inside a stretch (code i); no landing with a gap below 448. After an entry the chain
lands 0 times in 99.57% of stretches, once 7,653,429 times, twice 5,041 times and three times 25 times, never more.
80% of the entries come in round 10 of their cycle, all with the same shape (R/W = 0.3496, (W − b)/W = 0.8369).
Every landing lies on the plane 2(b − a) = W − 2R − 6 (`landing_plane`); so do 96.05% of the entries (3.42% are
one step off, at +2, 0.22% at −2, 0.32% elsewhere), at every width; every i start is at +2.

*The halting families and lanes.* No pass start is in any of the eight families, and none comes near: the families
fix R and W − b, while along the run R/W ≥ 0.0011 and (W − b)/W ≥ 0.095, so the scale distance grows with the width
(27.6 halvings at 2⁴²). Q = (W − b) + 2R + 22 is never a power of two or three times one (the lanes need Q = 2^(j+2), or
3·2^j on the other route). v2(Q) is distributed exactly like the 2-adic valuation of a random even number (the share
with v2(Q) ≥ v is 2^-(v−1) to within sampling error up to v = 32); the largest is v2(Q) = 32, Q = 809 · 2³², at the
round-10 entry of n = 1,130,966,187,986 (width 2.26 × 10¹²), and the largest v2(Q)/log2 Q is 0.768, there. The
smallest odd part of Q is u = 463 (Q = 463 · 2²¹, width 6.3 × 10⁸).

*The chain a halt would need.* A halt from blank tape needs the last pass start of the loop's chain from the first
loop entry after an open clean tape (`blank_halt_open_small`, `../lean/thm/OpenSmallHalt.lean`), and
`../lean/thm/WideHalt.lean` and `FarHalt.lean` give that pass start W ≤ 64R + 6 or 15W ≤ 64(W − b), and
15W ≤ 64(W − b), from the entry checks `EntryWide` (W ≤ 32R) and `EntryFar` (15W ≤ 64(W − b) and
15W + 26 ≤ 32(W − b + R)) that the clean-tape trees pass at their entries. An entry later in the same cycle, after that
chain has ended, is part of the run from that pass start, which the theorems leave to the pass-start tree. The run
marks every pass start with the entry of its cycle whose chain it belongs to:

- *First entries* (1,770,345,647, one in every cycle with a pass start). Every one has W ≤ 32R, and every one but one
  passes `EntryFar`; the last pass start of every first-entry chain has the wide shape (least slack
  max(64R + 6 − W, 64(W − b) − 15W)/W = 0.434), and every one but that one 15W ≤ 64(W − b). The chains land 0, 1, 2 or
  3 times (1,766,522,570, 3,821,163, 1,889 and 25 chains), and no last pass start has Q = 2^v or 3·2^v (largest
  v2(Q)/log2 Q 0.768). The exception is n = 1,480,645,918,802 (width 2.96 × 10¹²), whose only pass start is its first
  entry, at round 46: a = 6,437,135,253, b = 2,568,965,956,546, W = 2,961,291,837,770, R = 139,690,975,514, so
  (W − b)/W = 0.1325 and W/R = 21.2. It fails `EntryFar` and ends its chain with 15W > 64(W − b) (but W ≤ 64R + 6).
  A tree with the far check does not stop at such an entry but follows the run on past it (`RTree.exploreWE` stops
  only at a round start that passes the check), so `FarHalt.lean` claims no shape for this chain; its clean tape needs
  47 digits to settle, so the 36- and 40-digit trees leave it open. Of the bounds `../lean/EntryForms.lean` finds on
  the 36-digit entry classes, R > W/29.02 holds at every first entry (W/R at most 28.4), and W − b > 0.4558W at every
  one below width 2³⁴ and in the 1/1,024 sample above; the first entries that set a record of their stretch below
  (W − b)/W = 0.4558 all come late in the cycles of clean tapes open at 36 and at 40 digits (rounds 46 to 62, settle
  depths 41 to 61): 0.1325 above, then 0.3788 at n = 4,352,455,290,926 (W/R = 7.6), 0.4031, 0.4547, 0.4548 and
  eight from 0.4553 to 0.4558.
- *Later entries* (28,043,749, 1.56% of the entries). Their chains hold the other 1,378 of the 1,379 pass starts with
  15W > 64(W − b) (all from width 2³² on: 902 later entries and 476 half-pass landings from them) and all 20 that fail
  both conditions (1 entry and 19 half-pass landings; one in [2³⁹, 2⁴⁰), one in [2⁴⁰, 2⁴¹), seven in [2⁴¹, 2⁴²) and
  eleven in [2⁴², 2⁴³)). The lowest slack is −0.505, at n = 2,422,756,279,634 round 59 (a = 1,997,150,438,435,
  b = 4,382,458,318,106, W = 4,845,512,559,476, R = 37,448,400,064), a half-pass landing in the chain of the cycle's
  third entry; the record before 2⁴², −0.0756 at n = 2,041,590,924,626 round 52, is a half-pass landing two rounds
  after a second entry with W/R = 34.6. 1,066 later entries have W > 32R and 9,690 fail `EntryFar`.

W > 64R + 6 holds at 62,352 pass starts in all (from width 2¹⁷ on, 3,076 of them chain ends of first entries). By the
step maps only entries and half-pass landings can fail 15W ≤ 64(W − b): a full pass lands inside
15W ≤ 64(W − b) − 144R − 375 (all 52,379 of the run's do), and a round-7 break with
64(W − b) − 15W = 17E − 6b + 12R + 284 > 0.

*The open clean-tape classes* (`settle.c`, `passes.py`). Of the run's clean tapes, 4.4 to 5.3 in 100,000 have a class
still open at 36 digits (nine windows of 3.7 million consecutive clean tapes from 2³⁴ to 2⁴²), twice the cut classes'
measure 2.4 × 10⁻⁵: every open class has n ≡ 2 (mod 4), and the run lands there 51% of the time, not 25%. The cycles
of entries and half-pass landings are open at 36 digits about 0.45% of the time at every width (0.42 to 0.52% in
each binary length from 2²⁶ on, but for the sample's noise), about 90 times the rate of a clean tape of the run;
those of full-pass landings 74%, of round-7 breaks 27%, of i starts 53%. The deepest cycle with a pass start needs
81 digits.

## Data

In `results/` (tab-separated, one row per three-wall round start: n of the cycle's clean tape, round, a, b, c, W, R,
W − b, code, chain position, sigma, family distance at the start and at the next step, v2(Q), log2 of Q's odd part,
settle depth of n, flags: `e<k>` for a pass start in the chain of the k-th entry of its cycle, k ≥ 2, and `last` for
the last pass start of a chain):

| file | contents |
|---|---|
| `tables.md` | the tables of `report.py` and `passes.py` |
| `stitched.txt` | `stitch.py`'s output: the joins, checkpoints (K: widths 2^k; P: multiples of 10¹¹), the cascades of 11 or more meetings (C), the statistics per binary length of the width (B), the closest-end-meeting records (H) |
| `landings_F7.tsv.gz` | every full-pass and round-7 landing of the run (52,379 and 81,139) |
| `notable_EH.tsv.gz` | the entries and half-pass landings above width 2³⁴ written as notable (20,470): every one with 15W > 64(W − b), first entries failing an entry check, and the records of their stretch (slack, R/W, (W − b)/W, v2(Q)/log2 Q, ..., and for first entries and their chains' ends separately; most, 18,189, are first entries in round 26 whose (W − b)/W comes down towards 0.455824 along the run, a new record of their stretch each time) |
| `sample16k.tsv.gz` | every three-wall round start in a 1/16,384 sample of the cycles (by a hash of n), at every width (110,313) |

In the project's shared folder `blank-run/`: every three-wall round start below width 2³⁴ (3,527,686), the 1/1,024
sample at every width (1,763,800), every i, x, full-pass and round-7 start with the notable entries and half-pass
landings (304,475), and each stretch's output without its pass-start lines.

## Programs

| file | what it does |
|---|---|
| `engine.h` | the mark model on integer positions: the rules of the fixed engines (`../csearch/lined.c`, `nrefdfs2.c`) with the trailing-wall canonical form, and every contact condition of `roundZ` (`../lean/BB6/Round.lean`: `gapEvent`, `pktBack`, `pktLand`); a round those conditions do not cover stops the run (`bad` ≠ 0) instead of applying a rule outside them |
| `fast.h` | the same rules and checks, rearranged for speed (one array of marks with room at both ends; positions relative to an offset that grows at each round end) |
| `blankrun.c` | the plain follower on `engine.h`: checkpoints, every three-wall round start, end-meeting records |
| `follow.c` | the follower used for the run (`fast.h`): skips the five quick classes (81% of the cycles: odd n, n ≡ 0 mod 4, 6 and 10 mod 16, 2 mod 32, each with a fixed jump, round count and halving chain and no three-wall round start), simulating every 65,536th one as a check; analyses each cycle's three-wall round starts with the loop's chain stretches as `EndEvent` defines them (`../lean/BB6/Ends.lean`), the landings as `StepMap` and `StepWall` give them, and marks the entry of the cycle each chain comes from and its last pass start; keeps statistics per binary length of the width, for the first entries and their chains' ends separately; runs the stretch from any clean tape |
| `stitch.py` | joins the stretches of a parallel run and checks the joins (below) |
| `report.py` | the tables of a stitched run (Markdown) |
| `settle.c` | the settle depth of clean tapes n: how many low binary digits of n the exhaustive check needs to settle n's class |
| `passes.py` | tables over the written pass starts: offsets from the landing plane, the rounds the entries come in, settle depths of their cycles and of every clean tape in windows of the run (Markdown) |
| `pack.py` | the written three-wall round starts as the TSV files above, with the settle depth of each cycle |

## How it is checked

- **The Lean prefixes.** From the first round start, `follow` and `blankrun` reach the clean tape of width exactly 2²⁰
  after 294,033 rounds and of width exactly 2³² after 1,204,297,272 rounds: the values of `blank_prefix_kernel`
  (`../lean/thm/PrefixKernel.lean`) and `blank_prefix` (`../lean/thm/Prefix.lean`).
- **Round by round** (`../simtest/`, `br` and `brf`, up to 12 rounds from each random well-formed round start):
  `engine.h` against the bare transition table on 25,000 starts (199,401 rounds compared, no disagreement) and
  against `lined` on 20,000 (161,390 rounds, none); `fast.h` against `engine.h` (159,687 rounds) and against the bare
  machine (158,944 rounds), none (`ORACLE="node stepper.js 12 machine" python3 run.py 20000 7 12 br="build/br 12"`
  and the like).
- **The fast engine and the skipping.** `follow` on `fast.h` writes the same three-wall round starts as `blankrun` on
  `engine.h` over the whole run to width 2³² (881,912 lines, identical), and the same output with the quick classes
  simulated (`NOSKIP=1`) as with them skipped. During the run every 65,536th quick cycle is simulated and compared.
- **The chain analysis** on the full pass onto the 13,400 landing of PR #48: `follow pass 449 1182 10399 13376 40` finds
  the landing at round 8 (code F, in family 8, Q = 2¹²) and then the uncovered close.
- **The entry marking.** The run to width 2⁴² was made twice, before and after `follow.c` marked the entries: every
  line of the first run is among the second's (which adds the pass starts with 15W > 64(W − b) and the first-entry
  records as notable lines), and every statistic of the first is the same in the second, stretch by stretch.
- **The joins.** Two paths of clean tapes started up to 90 apart meet within 18 cycles, having moved at most 129
  (4,000 trials near 10¹² and 10¹⁴; 7 to 8 cycles on average), and paths 300,000 apart within about 33,000 cycles;
  from a shared clean tape on they are the same. So the run is split into stretches started at chosen clean tapes;
  each stretch writes every clean tape it visits in a window at its head and at its tail, and `stitch.py` checks that
  the earlier stretch's tail (the true run, by induction from blank tape) meets the later stretch's head inside the
  window, and that the two agree from there on. Each stretch counts only the cycles from clean tapes after its head
  window, so the counts add up exactly; the stitched statistics of stretches started at 4 different clean tapes near
  2²⁶ are identical to an unsplit run's. In the run to 2⁴³ the true run passes through each chosen start itself (the
  starts are k · 2³⁹ + c with c ∈ {0, 1, 2}, congruent mod 3·2²⁰ to 2²¹, 2²⁰ + 1 or 2, which the run visits early on,
  and its residues mod 3·2²⁰ nearly repeat from lap to lap: "Laps repeat" in the notes), and the two lists agree over
  the whole window at all seven joins, 115,621 to 115,648 clean tapes.
- **`settle.c`** against the exhaustive check's class engine (`../csearch/settle.c`, the depth at which n's class
  settles with n in it) on 6,000 clean tapes, 3,000 of the run's pass-start cycles above 10⁶ and 3,000 random n in
  [2³⁰, 2³³): the same depth for 5,923; for the other 77 both find n's class open at every depth below n's bit
  length.

## Running it

```sh
gcc -O3 -march=native -o follow follow.c -lm
./follow blank 549755813888 1048576 > c0.txt &                         # blank tape to n = 2^39
./follow chunk 549755813888 1099511627777 1048576 > c1.txt &           # stretches start at clean tapes n = 2 mod 3
./follow chunk 1099511627777 1649267441666 1048576 > c2.txt &
./follow chunk 1649267441666 2199023255552 1048576 > c3.txt &          # to n = 2^41 (width 2^42)
./follow chunk 2199023255552 2748779069441 1048576 > c4.txt &
./follow chunk 2748779069441 3298534883330 1048576 > c5.txt &
./follow chunk 3298534883330 3848290697216 1048576 > c6.txt &
./follow chunk 3848290697216 4398046511104 1048576 > c7.txt &          # to n = 2^42 (width 2^43)
wait
python3 stitch.py c?.txt > stitched.txt                                # checks the joins
python3 report.py stitched.txt --from 15
gcc -O2 -o settle settle.c
python3 passes.py ./settle c?.txt --window w35.txt ...                 # w35.txt: follow chunk S S+Z Z from a checkpoint
python3 pack.py ./settle packed c?.txt
```

Each stretch of 2³⁹ clean-tape numbers takes 105 minutes on one core, with four running (5.2 × 10⁹ numbers and 580
million cycles a minute). Output lines are described at the top of `follow.c`.
