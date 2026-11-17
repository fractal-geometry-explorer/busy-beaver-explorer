# Block lists in the class search, and the F01 sweep with them (16–17 November 2026)

## Why

With inner cycle rules (`INNER.md`) the F01 class searches stopped stalling inside a round, but the sets of classes
kept growing. Most of the new classes were *lists* of short blocks, written out because their counts were below
`BIG`: `10 (101)^n`, `10110 (101)^n`, `10110110 (101)^n`, … are three classes, though they are one family
`1 (011)^m 0 (101)^n`. Each one then made more classes of the same kind.

## What changed

`pclosure_list.py` (on `paccel_inner.py`) changes what a class is:

* **A free count for each block, with its own lower bound.** A class is a list of cells and repeats `(w)^{>=lo}`.
  Each repeat's count is `lo + x` with `x >= 0` free and independent, and `lo` may be 0 (the block may be missing).
  A node's cells are factored into repeats (at least 2 copies of a word of at most 3 cells), and every repeat gets the
  free count `min(count, 2) + x`. So a list such as `011011` turns into `(011)^{>=2}`, and is no longer written out.
* **Cover check instead of equal text.** A node is *covered* by a class when a matcher shows that every instance of
  the node (its counts may carry variables) lies in the class's language. Cells match cells. A class repeat takes
  whole literal copies of its word and whole node repeats with the same word, and the count it takes must be at
  least `lo` for every value of the variables. A covered node needs no new class.
* **Widening.** When no class covers a node, but a class would if some of its lower bounds were smaller, those
  bounds are lowered. The class only grows, the old class is dropped, and the wider class is explored instead.
* **Final strict check.** "Closed" means: every piece of every class reaches, at its first event, a node covered
  by a class of the final set; no piece halts or is undecided; and the start node is covered.

Search fixes (they help `pclosure_inner.py` as well):

* `pclosure_inner.splits` answers the sign of `k + Σ c_v x_v`, when one sign has one variable and the other sign has
  several, by peeling one variable (`x = 0`, `x >= 1`). That never ends. The new split works on the part with one
  variable of each sign. In one half the other variables push the form further the same way. The other half asks
  again, with one variable fewer.
* A question asked by a machine step (`safe_step` asks before anything changes) splits the piece, and each part
  goes on from that point instead of from the start. The run's cycle history is kept. The point where cycles are
  looked for moves along with the substitution, so the history stays usable.
* `BBJOBS` worker processes, and a checkpoint file (`BBCKPT`) that a run resumes from. The container restarted
  twice during this work, and everything after the last checkpoint was lost each time.

**Checked against a plain simulator.** `vlist.py` writes out the start tape of every leaf at x = 0 and at random
values. It runs the plain machine cell by cell to the next event and compares the tape with the predicted node. It
also checks, with a plain regular expression per class (`(w){lo,}`), that the predicted node is in some class. On a
240 s search of `1RB1LD_0RC1RC_1RD0RE_0LA0LF_0RF---_1RA1LA` (32 classes, 197 inner rules) it made 40,551
checks with 0 mismatches.

```sh
D=holdouts/1RB0LE_1RC---_0RD0RE_1LE0RB_0LA0LF_0RC0LD/py/closure
export BBM=1RB1LD_0RC1RC_1RD0RE_0LA0LF_0RF---_1RA1LA BBEV=5 BBMIRROR=0 BBINNER=1 BBBIG=6 BBTBASE=2
python3 $D/pclosure_list.py /tmp/l.json 5 240         # the search, 240 s
python3 $D/vlist.py /tmp/l.json 2 2e6                 # plain-simulator and regex check
```

## Results

**The sets get much smaller, but none closes.**

On `1RB1LD_0RC1RC_1RD0RE_0LA0LF_0RF---_1RA1LA` (left end, F), the old search reached 339 classes in 25 minutes with
425 still waiting. The new search finished its whole set: 80 classes with nothing waiting, no halting piece and
every node covered. Only 19 pieces stayed open, all from the three-count splits fixed above. After that fix, a
longer run (4 workers, resumed from checkpoints, about 52 classes explored) found the real obstruction. The class
`0 (011)^{>=2} 0 (011)^{>=2} 010 (101)^{>=1}` has **62 halting pieces**. They lie along lines such as
`(a, b, c) = (28, 8, 5), (52, 16, 9), (76, 24, 13)`, that is `(24k+4, 8k, 4k+1)`. The plain machine confirms it:
the tape `0 (011)^28 0 (011)^8 010 (101)^5` at F on the left end halts within one round. With independent counts,
this class cannot be part of a closed set. Closing it needs classes that carry linear relations between their counts
(the run reaches this shape, but presumably never with `a = 3b + 4`).

**F01 sweep** (all 56 machines, the 103 side and event-state choices of the earlier sweeps, 600 s each, 3 at a
time, `BBCLASSTIME=200`; raw output and logs in `/mnt/project-files/f01-closedset-sweep/lists/sweep/`):

| outcome | configurations |
|---|---|
| closed | 0 |
| finished, only undecided pieces | 27 |
| finished, with halting pieces | 4 |
| still growing, no open piece | 4 |
| still growing, open pieces | 37 |
| stopped inside one class (time limit) | 31 |

Most of the 27 "finished, only undecided" runs are a single class whose one piece hits the 200 s class time
limit. In these the first round is already a Collatz-like map of one count (for example
`1RB0LE_1RC---_0RD0RE_1LE0RB_0LA0LF_0RC0LD` at RD, and `1RB0LD_0RC0RF_1LD0RB_1LE---_0LA0LB_0LE0RA` at LA, whose
`halts_iff` is already proved in Lean), and no finite class set of this kind exists. The 4 runs with halting pieces
(`1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA` LC, `1RB0RF_1LC0RA_1LD1LB_0LE---_1LA0LA_1RE1LD` LA,
`1RB1RE_0RC---_1RD0RD_1LE0LF_1RA0LD_1LC1RB` RC, `1RB0RB_1LC0LF_1RD0LB_1RE1RC_0RA---_1LA1RE` RA) have small
finished sets (4 to 15 classes). Their halting pieces come from the same cause: independent counts let a class hold
tapes the machine never reaches.

So block lists were the next thing in the way, and they are now handled. What stops the F01 searches now is that
the counts of a class are independent. The next step is classes with linear relations between counts (a lattice of
`(b + M x)` vectors instead of a box), or a check that the halting members of a class are unreachable. No set
closed, so there is no new certificate and no new Lean replay. The Lean replays of PR 259 are unchanged.

## Every configuration (600 s sweep)

| machine | side, event state | outcome | classes | waiting | halting pieces | undecided pieces | widenings |
|---|---|---|---|---|---|---|---|
|`1RB---_0RC1RA_1RD1RF_1LE0LF_1RB0LD_0RE0LC`|LE|stopped by the time limit inside a class|||||
|`1RB---_0RC1RA_1RD1RF_1LE0LF_1RB0LD_0RE0LC`|RB|finished, undecided pieces|2|0|0|1|0|
|`1RB---_1RC1RE_1LD0LE_1RF0LC_0RD0RA_0RB1RD`|RB|still growing, open pieces|206|109|0|3|1016|
|`1RB0LA_1RC---_1RD1RA_0RE1LC_1LF0RF_1LD0RC`|LA|stopped by the time limit inside a class|||||
|`1RB0LA_1RC---_1RD1RA_0RE1LC_1LF0RF_1LD0RC`|RD|still growing, open pieces|13|439|26631|167705|2|
|`1RB0LA_1RC0RE_0LD0RF_1LA1LD_0RA1RE_---0LC`|LA|stopped by the time limit inside a class|||||
|`1RB0LA_1RC0RE_0LD0RF_1LA1LD_0RA1RE_---0LC`|RC|still growing, open pieces|3|545|467|870|220|
|`1RB0LB_1RC0LD_0LA1RD_1LC1LE_1LF0RE_1LD---`|LA|stopped by the time limit inside a class|||||
|`1RB0LB_1RC0LD_0LA1RD_1LC1LE_1LF0RE_1LD---`|RE|stopped by the time limit inside a class|||||
|`1RB0LC_1LA1RD_1LA1LF_0RE---_1RA1RE_0RB0LA`|LA|stopped by the time limit inside a class|||||
|`1RB0LC_1LA1RD_1LA1LF_0RE---_1RA1RE_0RB0LA`|RA|finished, undecided pieces|1|0|0|1|0|
|`1RB0LC_1RC0RA_1LA0LD_1LE0RB_1LC1LF_0LA---`|LA|still growing, no open piece|3451|2126|0|0|3125|
|`1RB0LC_1RC0RA_1LA0LD_1LE0RB_1LC1LF_0LA---`|RA|still growing, open pieces|7|5|0|162|13|
|`1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1RF`|LA|still growing, open pieces|14|3361|0|1|3515|
|`1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1RF`|RC|still growing, open pieces|3|61|0|123|39|
|`1RB0LD_0RC0RF_1LD0RB_1LE---_0LA0LB_0LE0RA`|LA|finished, undecided pieces|2|0|0|1|0|
|`1RB0LD_0RC0RF_1LD0RB_1LE---_0LA0LB_0LE0RA`|RF|still growing, open pieces|14|74|18|4|35|
|`1RB0LD_0RC1RA_1RD1RB_1RE1LE_1LF0LA_---1LA`|LA|finished, undecided pieces|4|0|0|1|0|
|`1RB0LD_0RC1RA_1RD1RB_1RE1LE_1LF0LA_---1LA`|RC|still growing, open pieces|60|491|0|17882|85|
|`1RB0LD_0RC1RA_1RD1RE_1LA0LE_0RA0RF_1RC---`|LA|finished, undecided pieces|5|0|0|117|0|
|`1RB0LD_0RC1RA_1RD1RE_1LA0LE_0RA0RF_1RC---`|RC|still growing, open pieces|222|119|0|3|1103|
|`1RB0LD_0RC1RA_1RD1RF_1LA0LE_0RA0LC_0RA---`|LA|stopped by the time limit inside a class|||||
|`1RB0LD_0RC1RA_1RD1RF_1LA0LE_0RA0LC_0RA---`|RA|finished, undecided pieces|2|0|0|1|1|
|`1RB0LE_1RC---_0RD0RE_1LE0RB_0LA0LF_0RC0LD`|LF|still growing, open pieces|40|173|96|8|170|
|`1RB0LE_1RC---_0RD0RE_1LE0RB_0LA0LF_0RC0LD`|RD|finished, undecided pieces|1|0|0|1|0|
|`1RB0LE_1RC1RA_1RD0RF_1RE0RA_1LA1LD_1RA---`|LA|stopped by the time limit inside a class|||||
|`1RB0LE_1RC1RA_1RD0RF_1RE0RA_1LA1LD_1RA---`|RA|finished, undecided pieces|1|0|0|1|0|
|`1RB0LE_1RC1RF_1RD0RA_1LE0RC_1LC0LD_0RD---`|LC|still growing, open pieces|9|5|0|436|12|
|`1RB0LE_1RC1RF_1RD0RA_1LE0RC_1LC0LD_0RD---`|RD|still growing, no open piece|2585|1862|0|0|3923|
|`1RB0LF_1LC0LA_---1RD_1RF1RE_1LF1RD_1LB0RE`|LA|stopped by the time limit inside a class|||||
|`1RB0LF_1LC0LA_---1RD_1RF1RE_1LF1RD_1LB0RE`|RD|finished, undecided pieces|2|0|0|1|0|
|`1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA`|LC|finished, halting pieces|4|0|2|0|1|
|`1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA`|RB|still growing, open pieces|7|1|15|12|3|
|`1RB0RB_1LC0LF_1RD0LB_1RE1RC_0RA---_1LA1RE`|LB|stopped by the time limit inside a class|||||
|`1RB0RB_1LC0LF_1RD0LB_1RE1RC_0RA---_1LA1RE`|RA|finished, halting pieces|11|0|1|9|3|
|`1RB0RC_1LC0LD_1RA0LB_1LE0RA_1LB1LF_0LC---`|LC|still growing, no open piece|2336|2043|0|0|4274|
|`1RB0RC_1LC0RB_1RE1LD_0LB0LF_---0RA_1LB1LD`|LB|finished, undecided pieces|2|0|0|1|0|
|`1RB0RC_1LC0RB_1RE1LD_0LB0LF_---0RA_1LB1LD`|RB|finished, undecided pieces|7|0|0|3|3|
|`1RB0RC_1LC1LA_1RD0LB_1RE1RC_1RA0RF_1RC---`|LC|stopped by the time limit inside a class|||||
|`1RB0RC_1LC1LA_1RD0LB_1RE1RC_1RA0RF_1RC---`|RA|finished, undecided pieces|1|0|0|1|0|
|`1RB0RD_1LC0RA_1LA0LB_1RE0LC_1RA1RF_0RB---`|LA|still growing, open pieces|7|6|0|453|11|
|`1RB0RD_1LC0RA_1LA0LB_1RE0LC_1RA1RF_0RB---`|RA|still growing, no open piece|1663|2646|0|0|3391|
|`1RB0RE_0LC0RF_1LD1LC_1RA0LD_0RD1RE_---0LB`|LD|stopped by the time limit inside a class|||||
|`1RB0RE_0LC0RF_1LD1LC_1RA0LD_0RD1RE_---0LB`|RB|still growing, open pieces|6|3|0|3|4|
|`1RB0RE_1LC0LE_---1LD_1LE1LB_1RA0LF_0RD1LA`|LA|finished, undecided pieces|1|0|0|1|0|
|`1RB0RE_1LC0LE_---1LD_1LE1LB_1RA0LF_0RD1LA`|RA|finished, undecided pieces|2|0|0|1|0|
|`1RB0RE_1LC0RA_0LD1LB_1LA1LE_0LB0LF_1LD---`|LA|still growing, open pieces|119|177|0|9|1040|
|`1RB0RE_1LC0RA_0LD1LB_1LA1LF_0LB0RD_0LB---`|LA|finished, undecided pieces|1|0|0|1|0|
|`1RB0RE_1LC0RA_0LD1LB_1LA1LF_0LB0RD_0LB---`|RA|stopped by the time limit inside a class|||||
|`1RB0RF_0LC---_1LD1LC_1RE0LA_1RA1RD_0RD1RF`|LA|stopped by the time limit inside a class|||||
|`1RB0RF_0LC---_1LD1LC_1RE0LA_1RA1RD_0RD1RF`|RA|still growing, open pieces|7|29|0|144|174|
|`1RB0RF_1LC0RA_1LD1LB_0LE---_1LA0LA_1RE1LD`|LA|finished, halting pieces|15|0|1|7|2|
|`1RB0RF_1LC0RA_1LD1LB_0LE---_1LA0LA_1RE1LD`|RA|stopped by the time limit inside a class|||||
|`1RB0RF_1LC0RC_0LD1LC_1RE1LB_1RF---_1LE1RA`|LC|stopped by the time limit inside a class|||||
|`1RB0RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_0RD---`|LB|still growing, open pieces|178|196|0|3|215|
|`1RB0RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_0RD---`|RD|still growing, open pieces|73|24|0|3327|79|
|`1RB0RF_1RC0RD_1LD1LB_1RE0LC_1RA1RD_1RD---`|LD|stopped by the time limit inside a class|||||
|`1RB0RF_1RC0RD_1LD1LB_1RE0LC_1RA1RD_1RD---`|RA|finished, undecided pieces|2|0|0|1|0|
|`1RB1LB_1LC0LD_---1LD_1RE0LA_0RF1RD_1RA1RE`|LD|finished, undecided pieces|4|0|0|1|0|
|`1RB1LB_1LC0LD_---1LD_1RE0LA_0RF1RD_1RA1RE`|RA|still growing, open pieces|4|400|0|21693|1587|
|`1RB1LC_1LA---_1LD0LA_1RE0LE_0RF1RE_1LB1RD`|RE|stopped by the time limit inside a class|||||
|`1RB1LC_1LA0RE_0LD---_1LB1LD_1RB1RF_0LA0RB`|LA|finished, undecided pieces|1|0|0|1|0|
|`1RB1LC_1LA0RE_0LD---_1LB1LD_1RB1RF_0LA0RB`|RB|stopped by the time limit inside a class|||||
|`1RB1LC_1LC0RD_0LE1LA_0RF1RA_1LA0LA_---0RB`|LA|still growing, open pieces|14|137|0|3|107|
|`1RB1LC_1LC0RD_0LE1LA_0RF1RA_1LA0LA_---0RB`|RA|stopped by the time limit inside a class|||||
|`1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LF---_0RA1LA`|LA|still growing, open pieces|1862|3564|1603|0|2977|
|`1RB1LD_0LC1RC_1RA1RD_1LE0RB_---1LF_0LC0LA`|LC|finished, undecided pieces|1|0|0|1|0|
|`1RB1LD_0LC1RC_1RA1RD_1LE0RB_---1LF_0LC0LA`|RB|stopped by the time limit inside a class|||||
|`1RB1LD_0RC1RC_1RD0RE_0LA0LF_0RF---_1RA1LA`|LF|still growing, open pieces|43|45|0|2|52|
|`1RB1LD_0RC1RC_1RD0RE_0LA0LF_0RF---_1RA1LA`|RB|finished, undecided pieces|1|0|0|1|0|
|`1RB1LD_1LC0RC_0RF1RA_0LE1LA_1RC0LA_---0RB`|LA|still growing, open pieces|3|22|0|3|0|
|`1RB1LD_1LC0RC_0RF1RA_0LE1LA_1RC0LA_---0RB`|RA|still growing, open pieces|18|11|4|4|47|
|`1RB1LD_1RC1RE_1LA0RA_1RC0LB_0LA1RF_---1RD`|LD|still growing, open pieces|83|107|6379|2|1461|
|`1RB1LD_1RC1RE_1LA0RA_1RC0LB_0LA1RF_---1RD`|RA|still growing, open pieces|27|1|4396|186|19|
|`1RB1LD_1RC1RF_1LA1RD_1RE0LB_---0RA_0LA1RC`|LD|still growing, open pieces|66|32|2037|1285|379|
|`1RB1LD_1RC1RF_1LA1RD_1RE0LB_---0RA_0LA1RC`|RA|still growing, open pieces|27|1|6775|148|19|
|`1RB1RA_1LC0RB_1LE0LD_0LB1LD_0RA0LF_---0RE`|LE|stopped by the time limit inside a class|||||
|`1RB1RA_1LC0RB_1LE0LD_0LB1LD_0RA0LF_---0RE`|RB|stopped by the time limit inside a class|||||
|`1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1LF`|LD|still growing, open pieces|12|159|0|106|158|
|`1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1LF`|RA|stopped by the time limit inside a class|||||
|`1RB1RD_1LC0RF_1LD0LB_1RE0RB_---1RA_0LA1RC`|LB|finished, undecided pieces|1|0|0|1|0|
|`1RB1RD_1LC0RF_1LD0LB_1RE0RB_---1RA_0LA1RC`|RB|finished, undecided pieces|1|0|0|1|0|
|`1RB1RD_1RC1LD_0LA1RA_1LE0RC_---1LF_0LA0LB`|LA|finished, undecided pieces|1|0|0|1|0|
|`1RB1RD_1RC1LD_0LA1RA_1LE0RC_---1LF_0LA0LB`|RC|stopped by the time limit inside a class|||||
|`1RB1RE_0RC---_1RD0RD_1LE0LF_1RA0LD_1LC1RB`|LD|still growing, open pieces|26|16|229|6|37|
|`1RB1RE_0RC---_1RD0RD_1LE0LF_1RA0LD_1LC1RB`|RC|finished, halting pieces|11|0|1|9|3|
|`1RB1RE_1LC0LE_1RD0LB_0RA1RC_0RC0RF_1RA---`|RA|stopped by the time limit inside a class|||||
|`1RB1RE_1LC0RA_1LA0LD_1LB0LF_0RB0LE_0LA---`|LA|still growing, open pieces|73|24|0|3350|79|
|`1RB1RE_1LC0RA_1LD1LB_1LE0LF_1LA0LB_1LB---`|LA|finished, undecided pieces|1|0|0|1|0|
|`1RB1RE_1LC0RA_1LD1LB_1LE0LF_1LA0LB_1LB---`|RB|stopped by the time limit inside a class|||||
|`1RB1RE_1LC0RC_1RA1LD_1RB0LA_0LC1RF_---1RD`|LD|still growing, open pieces|593|531|1804|0|3550|
|`1RB1RE_1LC0RC_1RA1LD_1RB0LA_0LC1RF_---1RD`|RA|still growing, open pieces|11|4|2429|116|13|
|`1RB1RE_1RC0LD_1LB---_1RA1LD_1RA0RF_1RE0LC`|RA|stopped by the time limit inside a class|||||
|`1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE1RF`|LB|stopped by the time limit inside a class|||||
|`1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE1RF`|RB|still growing, open pieces|8|36|0|144|195|
|`1RB1RF_1LC0LF_1RD0LB_0RA1RE_1RD---_0RC0LA`|LB|stopped by the time limit inside a class|||||
|`1RB1RF_1LC0LF_1RD0LB_0RA1RE_1RD---_0RC0LA`|RA|finished, undecided pieces|1|0|0|1|0|
|`1RB1RF_1LC0RF_1LE0LD_1RC0LB_---1RA_1LB1RA`|LD|stopped by the time limit inside a class|||||
|`1RB1RF_1LC0RF_1LE0LD_1RC0LB_---1RA_1LB1RA`|RA|finished, undecided pieces|1|0|0|1|0|
|`1RB1RF_1LC1RD_1RA1LD_1RE0LA_---0RC_0LC1RB`|LD|still growing, open pieces|79|46|828|826|491|
|`1RB1RF_1LC1RD_1RA1LD_1RE0LA_---0RC_0LC1RB`|RA|still growing, open pieces|11|4|3407|99|13|
|`1RB1RF_1RC1LC_1LD0LE_---1LE_1RF0LB_0RA1RE`|LE|finished, undecided pieces|3|0|0|1|1|
|`1RB1RF_1RC1LC_1LD0LE_---1LE_1RF0LB_0RA1RE`|RA|still growing, open pieces|92|329|0|44591|174|
