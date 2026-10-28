# The run from blank tape, followed to width 2⁴² (untrusted)

The machine's own run from blank tape in the mark model, cycle by cycle (one clean tape to the next), with every round
start of three walls analysed as it comes: which pass starts the run passes, how it reaches them (an entry into the
loop, or a landing of the loop's chain after a full pass, a half pass or a round-7 break), and how close each comes to
the eight halting families (`../lean/thm/PassOpenHalt.lean`), to the halting lanes Q = 2^(j+2), to failing the wide
condition W ≤ 64R + 6 or 15W ≤ 64(W − b), and to the clean-tape classes the exhaustive check leaves open. None of it is
proved; the engine follows the proved rules and stops on anything they do not cover.

## What the run does to width 2⁴²

From the first round start the model reaches the clean tape of width exactly 2⁴² (n = 2,199,023,255,549) after
242,444,389,027 cycles and 1,233,200,303,024 rounds, with no halt and no uncovered round; the trailing-wall
canonical form is never written. Tables: `results/tables.md`; data: below.

*Against the earlier follower.* Where the notes give numbers for `../csearch/fastfollow.c` (a different program,
table lookups of settled classes), they agree: the first clean tape past 10¹² is n = 10¹² + 1 after 110,250,943,953
cycles (the notes: 110,250,943,952; the count here includes the cycle from blank tape to n = 2), the 11-meeting cascade
at n = 37,558,132,238 comes back at 140,637,347,342, and the longest cascade is 14 meetings at n = 391,305,139,022
(here also the closest end meeting of the run, 14.01 halvings).

*Pass starts.* 903,101,649 of them (every three-wall round start but 52), 3.7 per 1,000 cycles at
every width. How the run reaches them: 899,194,579 entries, 3,765,080 half-pass landings, 40,577 round-7 breaks,
26,225 full-pass landings, and 75,188 pass starts inside a stretch (code i); no landing with a gap below 448. After an
entry the chain lands 0 times in 99.57% of stretches, once 3,826,787 times, twice 2,528 times and three times 13 times.
80% of the entries come in round 10 of their cycle, all with the same shape (R/W = 0.3496, (W − b)/W = 0.8369).
Every landing lies on the plane 2(b − a) = W − 2R − 6 (`landing_plane`); so do 96.05% of the entries (3.42% are
one step off, at +2, 0.22% at −2, 0.32% elsewhere), at every width; every i start is at +2.

*The halting families and lanes.* No pass start is in any of the eight families, and none comes near: the families
fix R and W − b, while along the run R/W ≥ 0.0011 and (W − b)/W ≥ 0.127, so the scale distance grows with the width
(27 halvings at 2⁴¹). Q = (W − b) + 2R + 22 is never a power of two or three times one (the lanes need Q = 2^(j+2), or
3·2^j on the other route). v2(Q) is distributed exactly like the 2-adic valuation of a random even number (the share
with v2(Q) ≥ v is 2^-(v−1) to within sampling error up to v = 32); the largest is v2(Q) = 32, Q = 809 · 2³², at the
round-10 entry of n = 1,130,966,187,986 (width 2.26 × 10¹²), and the largest v2(Q)/log2 Q is 0.768, there. The
smallest odd part of Q is u = 463 (Q = 463 · 2²¹, width 6.3 × 10⁸).

*The wide condition* (`../lean/thm/WideHalt.lean`): the last pass start of the loop's chain from a loop entry of the
clean-tape tree (whose entries have W ≤ 32R) has W ≤ 64R + 6 or 15W ≤ 64(W − b). Along the run the first pass start of
every cycle is an entry within the bounds `EntryForms.lean` finds on the tree's entry classes, R > W/29.02 and
W − b > 0.4558W (at most W/R = 27.8, at least (W − b)/W = 0.45582, over all 3,457,596 cycles with a pass start below
width 2³⁴ and the 1/1,024 sample of cycles above). Later in
the same cycle, after the first entry's chain has ended, the run can enter the loop again (54,785 such re-entries
below 2³⁴, 1.6% of the entries), and these can be narrow: below 2³⁴ two of them have W > 32R, and in [2⁴¹, 2⁴²)
the narrowest entries (re-entries, by the bounds above) have R/W = 0.0097 and (W − b)/W = 0.133. W > 64R + 6 at 31,154 pass
starts (from width 2¹⁷ on), 15W > 64(W − b) at 680 (from 2³² on), and both at 9: one in [2³⁹, 2⁴⁰), one in
[2⁴⁰, 2⁴¹) and seven in [2⁴¹, 2⁴²). The four of them that set a record of the slack
max(64R + 6 − W, 64(W − b) − 15W)/W are half-pass landings two rounds after such a re-entry, which has W/R from 32.9
to 34.6 and 15W > 64(W − b), in cycles of one pattern: the first entry at round 37, an i start at 43, a full-pass
landing at 45, the re-entry at 50 and the half-pass landing at 52 (each a round earlier in one of them). The lowest
slack is −0.0756, at n = 2,041,590,924,626 round 52 (a = 1,582,197,073,573, b = 3,564,811,270,690,
W = 4,083,181,849,436, R = 58,976,727,598; the re-entry at round 50 has W/R = 34.6). By the step maps only entries
and half-pass landings can fail both: a full pass lands inside 15W ≤ 64(W − b) − 144R − 375 (all 26,225 of the run's
do), and a round-7 break with 32R′ > 4E − b > 3E, so W′ < 11R′. The run on to width 2⁴³ (under way) writes every pass
start with 15W > 64(W − b) and counts those that fail both by how the run reached them.

*The open clean-tape classes* (`settle.c`, `passes.py`). Of the run's clean tapes, 4.4 to 5.3 in 100,000 have a class
still open at 36 digits (eight windows of 3.7 million consecutive clean tapes from 2³⁴ to 2⁴¹), twice the cut classes'
measure 2.4 × 10⁻⁵: every open class has n ≡ 2 (mod 4), and the run lands there 51% of the time, not 25%. The cycles
of entries and half-pass landings are open at 36 digits about 0.45% of the time at every width (0.42 to 0.52% in
each binary length from 2²⁶ on, but for the sample's noise), about 90 times the rate of a clean tape of the run;
those of full-pass landings 74%, of round-7 breaks 27%, of i starts 53%. The deepest cycle with a pass start needs
81 digits; the four identified pass starts that fail both wide conditions, 45 to 48.


## Data

In `results/` (tab-separated, one row per three-wall round start: n of the cycle's clean tape, round, a, b, c, W, R,
W − b, code, chain position, sigma, family distance at the start and at the next step, v2(Q), log2 of Q's odd part,
settle depth of n, flags):

| file | contents |
|---|---|
| `tables.md` | the tables of `report.py` and `passes.py` |
| `stitched.txt` | `stitch.py`'s output: the joins, checkpoints (K: widths 2^k; P: multiples of 10¹¹), the cascades of 11 or more meetings (C), the statistics per binary length of the width (B), the closest-end-meeting records (H) |
| `landings_F7.tsv.gz` | every full-pass and round-7 landing of the run (26,225 and 40,577) |
| `records_EH.tsv` | the entries and half-pass landings above width 2³⁴ written as records of their stretch (slack, R/W, (W − b)/W, v2(Q)/log2 Q, ...) |
| `sample16k.tsv.gz` | every three-wall round start in a 1/16,384 sample of the cycles (by a hash of n), at every width (55,166) |

In the project's shared folder `blank-run/`: every three-wall round start below width 2³⁴ (3,527,686), the 1/1,024
sample at every width (881,705), every i, x, full-pass and round-7 start (142,157 with the records), and each
stretch's output without its pass-start lines.

## Programs

| file | what it does |
|---|---|
| `engine.h` | the mark model on integer positions: the rules of the fixed engines (`../csearch/lined.c`, `nrefdfs2.c`) with the trailing-wall canonical form, and every contact condition of `roundZ` (`../lean/BB6/Round.lean`: `gapEvent`, `pktBack`, `pktLand`); a round those conditions do not cover stops the run (`bad` ≠ 0) instead of applying a rule outside them |
| `fast.h` | the same rules and checks, rearranged for speed (one array of marks with room at both ends; positions relative to an offset that grows at each round end) |
| `blankrun.c` | the plain follower on `engine.h`: checkpoints, every three-wall round start, end-meeting records |
| `follow.c` | the follower used for the run (`fast.h`): skips the five quick classes (81% of the cycles: odd n, n ≡ 0 mod 4, 6 and 10 mod 16, 2 mod 32, each with a fixed jump, round count and halving chain and no three-wall round start), simulating every 65,536th one as a check; analyses each cycle's three-wall round starts with the loop's chain stretches as `EndEvent` defines them (`../lean/BB6/Ends.lean`), the landings as `StepMap` and `StepWall` give them; keeps statistics per binary length of the width; runs the stretch from any clean tape |
| `stitch.py` | joins the stretches of a parallel run and checks the joins (below) |
| `report.py` | the tables of a stitched run (Markdown) |
| `settle.c` | the settle depth of clean tapes n: how many low binary digits of n the exhaustive check needs to settle n's class |
| `passes.py` | tables over the written pass starts: offsets from the landing plane, the rounds the entries come in, settle depths of their cycles and of every clean tape in windows of the run (Markdown) |

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
- **The joins.** Two paths of clean tapes started up to 90 apart meet within 18 cycles, having moved at most 129
  (4,000 trials near 10¹² and 10¹⁴; 7 to 8 cycles on average), and paths 300,000 apart within about 33,000 cycles;
  from a shared clean tape on they are the same. So the run is split into stretches started at chosen clean tapes;
  each stretch writes every clean tape it visits in a window at its head and at its tail, and `stitch.py` checks that
  the earlier stretch's tail (the true run, by induction from blank tape) meets the later stretch's head inside the
  window, and that the two agree from there on. Each stretch counts only the cycles from clean tapes after its head
  window, so the counts add up exactly; the stitched statistics of stretches started at 4 different clean tapes near
  2²⁶ are identical to an unsplit run's. In the run to 2⁴² the true run passes through each chosen start itself (the
  starts are 2³⁹, 2⁴⁰ + 1 and 3·2³⁹ + 2, congruent mod 3·2²⁰ to 2²¹, 2²⁰ + 1 and 2, which the run visits early on,
  and its residues mod 3·2²⁰ nearly repeat from lap to lap: "Laps repeat" in the notes), and the two lists agree over
  the whole window, 115,621 to 115,646 clean tapes.
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
wait
python3 stitch.py c0.txt c1.txt c2.txt c3.txt > stitched.txt           # checks the joins
python3 report.py stitched.txt --from 15
gcc -O2 -o settle settle.c
python3 passes.py ./settle c0.txt c1.txt c2.txt c3.txt --window w35.txt ...  # w35.txt: follow chunk S S+Z Z from a checkpoint
```

Each stretch of 2³⁹ clean-tape numbers took 105 minutes on one core, with four running (5.2 × 10⁹ numbers and 580
million cycles a minute). Output lines are described at the top of `follow.c`.
