# Inner cycle rules for the class search, and the F01 sweep with them (16 November 2026)

## Why

The class search (`pclosure.py` on `paccel.py`) looks for cycle rules only at *events* (the event state arriving at
the end of the tape). On most F01 machines a round contains a loop whose number of turns depends on a free count:
the head bounces between two inner blocks, moving a block by a few cells per turn. The symbolic run of a piece
cannot finish that loop, so it peels the count one value at a time (a new piece and a rerun per value) until it hits
the move limit. In the first F01 sweep (`/mnt/project-files/f01-closedset-sweep/NOTES.md`) about 284 of about 490
finished configurations ended that way, with "no node within 150000 moves".

## What changed

`paccel_inner.py` and `pclosure_inner.py` are `paccel.py` and `pclosure.py` with:

* **Inner cycle rules** (`BBINNER=1`). Every shift-rule move (a block crossed at once) is a *checkpoint*. There the
  whole tape is re-bracketed and its shape recorded (counts of at least `BBBIGC`, default 6, are wild). When a shape
  comes back three times at equal distance with the wild counts moving by constant amounts, the rule is proved by a
  symbolic run of the same engine, as event rules are: the moving counts become `b + M x`, a count that does not move
  and is below `BIG` stays a fixed number, and the run must end in the same shape with counts `b + D + M x`. A
  proved rule is applied N times at once, N affine in the variables, so the whole loop is one move.
* **Inner rules never jump over a node.** The proof run of an inner rule fails if it meets an event, a checkpoint
  that is itself an event is not used for inner rules, and a shift rule that crosses the block at the left end
  is not used when the event state would arrive at the end in the middle of it (`evmid`). A shift rule that ends at
  the left end in the event state is now an event.
* **Canonical node text from the cells** (`BBFLATCANON=1`): blocks with a number count below 1,000 are written out
  and re-bracketed before the text is made, so that a node's class depends only on its cells and not on how the
  tokens happened to be bracketed. On a test machine this cut the classes found in 90 s from 83 to 18.
* Three fixes of the search (the first also made in `pclosure.py`): a class that hits "too many pieces" counts as
  undecided (`pclosure.py` could print CLOSED; no certificate in the repository has such a leaf); a split into more
  than `BBMAXSPLIT` pieces makes the piece undecided (it used to try to list up to ~10^30 pieces); the cycle-search
  point `ENV` has values for any number of variables (the KeyErrors of the first sweep).

**Checked against a plain simulator.** `vinner.py` writes out the start tape of every leaf of a search output at
x = 0 and at random values, runs the plain machine cell by cell to the next event, and compares the tape cell by
cell with the predicted node. On a 90 s search of `1RB1LD_0RC1RC_1RD0RE_0LA0LF_0RF---_1RA1LA` (62 inner rules):
27,021 checks, 0 mismatches. (Before the two left-end fixes it found mismatches: the engine reached a later node
than the first one. That was never unsound, since every leaf statement is still a true "reaches", but it broke the
first-node bookkeeping, so it is fixed.)

```sh
D=holdouts/1RB0LE_1RC---_0RD0RE_1LE0RB_0LA0LF_0RC0LD/py/closure
export BBM=1RB1LD_0RC1RC_1RD0RE_0LA0LF_0RF---_1RA1LA BBEV=5 BBMIRROR=0 BBBIG=6 BBTBASE=2 BBNODE='.*' BBMOD=1 BBMOVES=150000 BBINNER=1
python3 $D/pclosure_inner.py bfs /tmp/lf.json 5 90      # the search, 90 s
python3 $D/vinner.py /tmp/lf.json 3 2e6                  # the plain-simulator check, about 10 minutes
```

## The F01 sweep with inner rules

All 56 F01 machines, at the 103 side and event-state choices of the first sweep (`configs.txt` there), 150 s each,
`BBBIG=6 BBTBASE=2 BBMOD=1 BBINNER=1`. Raw output, logs and the scripts are in
`/mnt/project-files/f01-closedset-sweep/inner/`.

**Result: no configuration closes.** 102 of 103 finished:

| outcome | configurations |
|---|---|
| closed | 0 |
| no undecided piece, but the set of classes keeps growing | 46 |
| some undecided pieces | 6 |
| one class ran past the time limit (with undecided pieces) | 19 |
| one class ran past the time limit | 31 |

Inner rules were proved and used in 17 configurations (762 rules in all). The stall that motivated them is mostly
gone: 25 of 102 configurations still have a piece with "no node within 150000 moves", against about 284 of 490 in the first sweep.
What stops the search now is different: the set of classes does not stop growing. The new classes are mostly
*lists*: a prefix of short blocks with small counts (written out, e.g. `0011011011011010 (101)^n 0 (101)^n 1`) that
gets longer, or extra counters (`010 (1)^n 0000 (1)^n 00 (1)^n 0 (1)^n`). A longer run on the most promising one,
`1RB1LD_0RC1RC_1RD0RE_0LA0LF_0RF---_1RA1LA` (left end, F), reached 339 classes in 25 minutes with no undecided
piece and no halting piece, and the queue was still growing (425 classes waiting).

Halting pieces (members of a class that halt; not a halt of the machine) turned up in 9 configurations, all on
machines whose halting is a question about one orbit (e.g. `1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA`, whose
halting values are known).

So inner cycles were necessary but are not enough. Closing these machines needs an abstraction of the lists (a
block of small blocks as one repeat with a free count, or nested repeats), which this engine does not have. No new
certificate came out of the sweep, so there is no new Lean replay; the replays of PR 259 are unchanged.

## Every configuration

Columns: classes found, undecided pieces, halting pieces, inner rules (empty when the run did not finish).

| machine | side, event state | outcome | classes | undecided | halting | inner rules |
|---|---|---|---|---|---|---|
|`1RB---_0RC1RA_1RD1RF_1LE0LF_1RB0LD_0RE0LC`|LE|did not finish (one class ran past the time limit)|||||
|`1RB---_0RC1RA_1RD1RF_1LE0LF_1RB0LD_0RE0LC`|RB|did not finish (one class ran past the time limit)|||||
|`1RB---_1RC1RE_1LD0LE_1RF0LC_0RD0RA_0RB1RD`|RB|still growing (no undecided)|3638|0|0|0|
|`1RB0LA_1RC---_1RD1RA_0RE1LC_1LF0RF_1LD0RC`|LA|did not finish (one class ran past the time limit)|||||
|`1RB0LA_1RC---_1RD1RA_0RE1LC_1LF0RF_1LD0RC`|RD|did not finish (one class ran past the time limit)|||||
|`1RB0LA_1RC0RE_0LD0RF_1LA1LD_0RA1RE_---0LC`|LA|still growing (no undecided)|3525|0|0|0|
|`1RB0LA_1RC0RE_0LD0RF_1LA1LD_0RA1RE_---0LC`|RC|did not finish, undecided pieces|||||
|`1RB0LB_1RC0LD_0LA1RD_1LC1LE_1LF0RE_1LD---`|LA|did not finish (one class ran past the time limit)|||||
|`1RB0LB_1RC0LD_0LA1RD_1LC1LE_1LF0RE_1LD---`|RE|did not finish (one class ran past the time limit)|||||
|`1RB0LC_1LA1RD_1LA1LF_0RE---_1RA1RE_0RB0LA`|LA|did not finish (one class ran past the time limit)|||||
|`1RB0LC_1LA1RD_1LA1LF_0RE---_1RA1RE_0RB0LA`|RA|did not finish (one class ran past the time limit)|||||
|`1RB0LC_1RC0RA_1LA0LD_1LE0RB_1LC1LF_0LA---`|LA|still growing (no undecided)|4308|0|0|0|
|`1RB0LC_1RC0RA_1LA0LD_1LE0RB_1LC1LF_0LA---`|RA|did not finish, undecided pieces|||||
|`1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1RF`|LA|still growing (no undecided)|3779|0|0|0|
|`1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1RF`|RC|did not finish, undecided pieces|||||
|`1RB0LD_0RC0RF_1LD0RB_1LE---_0LA0LB_0LE0RA`|LA|did not finish (one class ran past the time limit)|||||
|`1RB0LD_0RC0RF_1LD0RB_1LE---_0LA0LB_0LE0RA`|RF|still growing (no undecided)|2851|0|3|0|
|`1RB0LD_0RC1RA_1RD1RB_1RE1LE_1LF0LA_---1LA`|LA|still growing (no undecided)|2491|0|0|0|
|`1RB0LD_0RC1RA_1RD1RB_1RE1LE_1LF0LA_---1LA`|RC|did not finish (one class ran past the time limit)|||||
|`1RB0LD_0RC1RA_1RD1RE_1LA0LE_0RA0RF_1RC---`|LA|did not finish, undecided pieces|||||
|`1RB0LD_0RC1RA_1RD1RE_1LA0LE_0RA0RF_1RC---`|RC|still growing (no undecided)|3754|0|0|0|
|`1RB0LD_0RC1RA_1RD1RF_1LA0LE_0RA0LC_0RA---`|LA|did not finish (one class ran past the time limit)|||||
|`1RB0LD_0RC1RA_1RD1RF_1LA0LE_0RA0LC_0RA---`|RA|did not finish (one class ran past the time limit)|||||
|`1RB0LE_1RC---_0RD0RE_1LE0RB_0LA0LF_0RC0LD`|LF|still growing (no undecided)|2805|0|0|0|
|`1RB0LE_1RC---_0RD0RE_1LE0RB_0LA0LF_0RC0LD`|RD|did not finish (one class ran past the time limit)|||||
|`1RB0LE_1RC1RA_1RD0RF_1RE0RA_1LA1LD_1RA---`|LA|did not finish (one class ran past the time limit)|||||
|`1RB0LE_1RC1RA_1RD0RF_1RE0RA_1LA1LD_1RA---`|RA|still growing (no undecided)|165|0|0|0|
|`1RB0LE_1RC1RF_1RD0RA_1LE0RC_1LC0LD_0RD---`|LC|still growing (no undecided)|5|0|0|36|
|`1RB0LE_1RC1RF_1RD0RA_1LE0RC_1LC0LD_0RD---`|RD|still growing (no undecided)|4416|0|0|0|
|`1RB0LF_1LC0LA_---1RD_1RF1RE_1LF1RD_1LB0RE`|LA|still growing (no undecided)|3748|0|0|0|
|`1RB0LF_1LC0LA_---1RD_1RF1RE_1LF1RD_1LB0RE`|RD|did not finish, undecided pieces|||||
|`1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA`|LC|still growing (no undecided)|11|0|1|5|
|`1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA`|RB|did not finish (one class ran past the time limit)|||||
|`1RB0RB_1LC0LF_1RD0LB_1RE1RC_0RA---_1LA1RE`|LB|undecided pieces|65|1|0|4|
|`1RB0RB_1LC0LF_1RD0LB_1RE1RC_0RA---_1LA1RE`|RA|did not finish, undecided pieces|||||
|`1RB0RC_1LC0LD_1RA0LB_1LE0RA_1LB1LF_0LC---`|LC|still growing (no undecided)|4426|0|0|0|
|`1RB0RC_1LC0RB_1RE1LD_0LB0LF_---0RA_1LB1LD`|LB|did not finish, undecided pieces|||||
|`1RB0RC_1LC0RB_1RE1LD_0LB0LF_---0RA_1LB1LD`|RB|still growing (no undecided)|1226|0|266|0|
|`1RB0RC_1LC1LA_1RD0LB_1RE1RC_1RA0RF_1RC---`|LC|still growing (no undecided)|104|0|0|14|
|`1RB0RC_1LC1LA_1RD0LB_1RE1RC_1RA0RF_1RC---`|RA|still growing (no undecided)|89|0|0|0|
|`1RB0RD_1LC0RA_1LA0LB_1RE0LC_1RA1RF_0RB---`|LA|did not finish, undecided pieces|||||
|`1RB0RD_1LC0RA_1LA0LB_1RE0LC_1RA1RF_0RB---`|RA|still growing (no undecided)|4031|0|0|0|
|`1RB0RE_0LC0RF_1LD1LC_1RA0LD_0RD1RE_---0LB`|LD|still growing (no undecided)|3761|0|0|0|
|`1RB0RE_0LC0RF_1LD1LC_1RA0LD_0RD1RE_---0LB`|RB|did not finish, undecided pieces|||||
|`1RB0RE_1LC0LE_---1LD_1LE1LB_1RA0LF_0RD1LA`|LA|did not finish (one class ran past the time limit)|||||
|`1RB0RE_1LC0LE_---1LD_1LE1LB_1RA0LF_0RD1LA`|RA|did not finish (one class ran past the time limit)|||||
|`1RB0RE_1LC0RA_0LD1LB_1LA1LE_0LB0LF_1LD---`|LA|still growing (no undecided)|3786|0|0|0|
|`1RB0RE_1LC0RA_0LD1LB_1LA1LF_0LB0RD_0LB---`|LA|did not finish (one class ran past the time limit)|||||
|`1RB0RE_1LC0RA_0LD1LB_1LA1LF_0LB0RD_0LB---`|RA|did not finish (one class ran past the time limit)|||||
|`1RB0RF_0LC---_1LD1LC_1RE0LA_1RA1RD_0RD1RF`|LA|still growing (no undecided)|2496|0|0|0|
|`1RB0RF_0LC---_1LD1LC_1RE0LA_1RA1RD_0RD1RF`|RA|did not finish, undecided pieces|||||
|`1RB0RF_1LC0RA_1LD1LB_0LE---_1LA0LA_1RE1LD`|LA|did not finish, undecided pieces|||||
|`1RB0RF_1LC0RA_1LD1LB_0LE---_1LA0LA_1RE1LD`|RA|undecided pieces|65|1|0|4|
|`1RB0RF_1LC0RC_0LD1LC_1RE1LB_1RF---_1LE1RA`|LC|undecided pieces|237|2|0|0|
|`1RB0RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_0RD---`|LB|did not finish (one class ran past the time limit)|||||
|`1RB0RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_0RD---`|RD|still growing (no undecided)|3393|0|0|142|
|`1RB0RF_1RC0RD_1LD1LB_1RE0LC_1RA1RD_1RD---`|LD|still growing (no undecided)|104|0|0|14|
|`1RB0RF_1RC0RD_1LD1LB_1RE0LC_1RA1RD_1RD---`|RA|still growing (no undecided)|321|0|0|0|
|`1RB1LB_1LC0LD_---1LD_1RE0LA_0RF1RD_1RA1RE`|LD|still growing (no undecided)|2506|0|0|0|
|`1RB1LB_1LC0LD_---1LD_1RE0LA_0RF1RD_1RA1RE`|RA|still growing (no undecided)|884|0|0|0|
|`1RB1LC_1LA---_1LD0LA_1RE0LE_0RF1RE_1LB1RD`|RE|undecided pieces|173|3|0|0|
|`1RB1LC_1LA0RE_0LD---_1LB1LD_1RB1RF_0LA0RB`|LA|still growing (no undecided)|79|0|0|46|
|`1RB1LC_1LA0RE_0LD---_1LB1LD_1RB1RF_0LA0RB`|RB|did not finish (one class ran past the time limit)|||||
|`1RB1LC_1LC0RD_0LE1LA_0RF1RA_1LA0LA_---0RB`|LA|did not finish (one class ran past the time limit)|||||
|`1RB1LC_1LC0RD_0LE1LA_0RF1RA_1LA0LA_---0RB`|RA|did not finish (one class ran past the time limit)|||||
|`1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LF---_0RA1LA`|LA|still growing (no undecided)|3140|0|305|0|
|`1RB1LD_0LC1RC_1RA1RD_1LE0RB_---1LF_0LC0LA`|LC|did not finish, undecided pieces|||||
|`1RB1LD_0LC1RC_1RA1RD_1LE0RB_---1LF_0LC0LA`|RB|did not finish (one class ran past the time limit)|||||
|`1RB1LD_0RC1RC_1RD0RE_0LA0LF_0RF---_1RA1LA`|LF|still growing (no undecided)|99|0|0|111|
|`1RB1LD_0RC1RC_1RD0RE_0LA0LF_0RF---_1RA1LA`|RB|still growing (no undecided)|17|0|1517|40|
|`1RB1LD_1LC0RC_0RF1RA_0LE1LA_1RC0LA_---0RB`|LA|did not finish (one class ran past the time limit)|||||
|`1RB1LD_1LC0RC_0RF1RA_0LE1LA_1RC0LA_---0RB`|RA|did not finish (one class ran past the time limit)|||||
|`1RB1LD_1RC1RE_1LA0RA_1RC0LB_0LA1RF_---1RD`|LD|still growing (no undecided)|4468|0|0|0|
|`1RB1LD_1RC1RE_1LA0RA_1RC0LB_0LA1RF_---1RD`|RA|still growing (no undecided)|29|0|159|47|
|`1RB1LD_1RC1RF_1LA1RD_1RE0LB_---0RA_0LA1RC`|LD|still growing (no undecided)|4149|0|0|0|
|`1RB1LD_1RC1RF_1LA1RD_1RE0LB_---0RA_0LA1RC`|RA|still growing (no undecided)|29|0|159|47|
|`1RB1RA_1LC0RB_1LE0LD_0LB1LD_0RA0LF_---0RE`|LE|did not finish, undecided pieces|||||
|`1RB1RA_1LC0RB_1LE0LD_0LB1LD_0RA0LF_---0RE`|RB|still growing (no undecided)|3577|0|0|0|
|`1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1LF`|LD|did not finish, undecided pieces|||||
|`1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1LF`|RA|still growing (no undecided)|3182|0|0|0|
|`1RB1RD_1LC0RF_1LD0LB_1RE0RB_---1RA_0LA1RC`|LB|did not finish (one class ran past the time limit)|||||
|`1RB1RD_1LC0RF_1LD0LB_1RE0RB_---1RA_0LA1RC`|RB|did not finish (one class ran past the time limit)|||||
|`1RB1RD_1RC1LD_0LA1RA_1LE0RC_---1LF_0LA0LB`|LA|did not finish, undecided pieces|||||
|`1RB1RD_1RC1LD_0LA1RA_1LE0RC_---1LF_0LA0LB`|RC|did not finish (one class ran past the time limit)|||||
|`1RB1RE_0RC---_1RD0RD_1LE0LF_1RA0LD_1LC1RB`|LD|undecided pieces|65|1|0|4|
|`1RB1RE_0RC---_1RD0RD_1LE0LF_1RA0LD_1LC1RB`|RC|did not finish, undecided pieces|||||
|`1RB1RE_1LC0LE_1RD0LB_0RA1RC_0RC0RF_1RA---`|RA|still growing (no undecided)|3701|0|0|0|
|`1RB1RE_1LC0RA_1LA0LD_1LB0LF_0RB0LE_0LA---`|LA|still growing (no undecided)|3344|0|0|142|
|`1RB1RE_1LC0RA_1LD1LB_1LE0LF_1LA0LB_1LB---`|LA|still growing (no undecided)|78|0|0|0|
|`1RB1RE_1LC0RA_1LD1LB_1LE0LF_1LA0LB_1LB---`|RB|still growing (no undecided)|272|0|0|6|
|`1RB1RE_1LC0RC_1RA1LD_1RB0LA_0LC1RF_---1RD`|LD|still growing (no undecided)|4455|0|0|0|
|`1RB1RE_1LC0RC_1RA1LD_1RB0LA_0LC1RF_---1RD`|RA|still growing (no undecided)|17|0|271|50|
|`1RB1RE_1RC0LD_1LB---_1RA1LD_1RA0RF_1RE0LC`|RA|did not finish (one class ran past the time limit)|||||
|`1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE1RF`|LB|did not finish, undecided pieces|||||
|`1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE1RF`|RB|did not finish, undecided pieces|||||
|`1RB1RF_1LC0LF_1RD0LB_0RA1RE_1RD---_0RC0LA`|LB|undecided pieces|35|33|0|0|
|`1RB1RF_1LC0LF_1RD0LB_0RA1RE_1RD---_0RC0LA`|RA|did not finish (one class ran past the time limit)|||||
|`1RB1RF_1LC0RF_1LE0LD_1RC0LB_---1RA_1LB1RA`|LD|still growing (no undecided)|3193|0|0|0|
|`1RB1RF_1LC0RF_1LE0LD_1RC0LB_---1RA_1LB1RA`|RA|did not finish, undecided pieces|||||
|`1RB1RF_1LC1RD_1RA1LD_1RE0LA_---0RC_0LC1RB`|LD|still growing (no undecided)|4266|0|0|0|
|`1RB1RF_1LC1RD_1RA1LD_1RE0LA_---0RC_0LC1RB`|RA|still growing (no undecided)|17|0|271|50|
|`1RB1RF_1RC1LC_1LD0LE_---1LE_1RF0LB_0RA1RE`|LE|still growing (no undecided)|1241|0|0|0|

Follow-up (17 Nov 2026): block lists as repeats with their own free counts, with cover checks and widening, are in `pclosure_list.py`; see `LISTS.md`.
