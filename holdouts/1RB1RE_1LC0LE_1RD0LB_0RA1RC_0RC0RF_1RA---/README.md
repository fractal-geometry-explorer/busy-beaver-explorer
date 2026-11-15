# 1RB1RE_1LC0LE_1RD0LB_0RA1RC_0RC0RF_1RA---

bbchallenge id 116343. One of the six-state holdouts whose halting from blank tape is open. Group G07
(fixed/sqrt growth), family **nested run counter, x10/3 per epoch**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RE |
| B | 1LC | 0LE |
| C | 1RD | 0LB |
| D | 0RA | 1RC |
| E | 0RC | 0RF |
| F | 1RA | --- |

## Status

Open; conjectured not to halt. No closed invariant was found in the dedicated pass of 15 November 2026; what was
settled instead:

* The machine is exactly a rewriting system with twelve local rules on two stacks (`lean/Macro.lean`, kernel), and
  it halts only through the rule `A> 111`.
* **No halting case exists among short left contexts.** Call an *excursion* the run from "A on blank tape at the
  right end of the written tape" to the next such moment. For *every* tape to the left (not only those of the run
  from blank tape), every excursion that reads at most 60 cells left of where it starts ends in another such moment
  without halting: 200,500,042 cases, none halts (`c/excursion_tree.c`, a complete case tree by direct simulation).
  So the epoch map has no halting case whose outcome is decided by 60 cells of context; a halt would need the head
  to go further left than that in one excursion and then meet something no shorter context produces.
* Every rule found continues without halting, and the accelerated simulation runs 8,000 epochs (about 10^8021 steps)
  from blank tape without a halt.
* Why a proof is still missing: the natural invariant is "any tape to the left, A at the right end", and its
  excursions go arbitrarily deep (through chains of runs of 2 and units); the configurations inside an excursion
  tie the tape left of the head to the tape right of it over unbounded distances, and no finite-automaton
  certificate of the kinds tried captures that (see "Certificate searches that fail").

## Symbolic class search (13 November 2026)

The engine with several free counts of `holdouts/1RB0LE_1RC---_0RD0RE_1LE0RB_0LA0LF_0RC0LD/py/closure/` (programs, not Lean), with the tape
mirrored so that the right end is the near end:

```sh
D=holdouts/1RB0LE_1RC---_0RD0RE_1LE0RB_0LA0LF_0RC0LD/py/closure
export BBM=1RB1RE_1LC0LE_1RD0LB_0RA1RC_0RC0RF_1RA--- BBEV=0 BBMIRROR=1 BBNODE='^00 \(1\)\^n' BBMOD=1
python3 $D/pclosure.py bfs /tmp/c116343.json 5 900
```

A node is the tape `... 1^n 0 0 A>` with n >= 20 (the active run at the right end, no units); a class is such a tape
with n and every other run or block of at least 20 words free. Each class is run symbolically to the next node, for
all values at once and every residue. In 15 minutes: 2,517 classes cut into 67,561 pieces; every piece reaches a
node, **none halts**, none is undecided. The set is not closed (555 classes still queued; the list of runs left of
the active one keeps getting longer), as for the relative 1RB---_1RC1RE_1LD0LE_1RF0LC_0RD0RA_0RB1RD. A plain simulator
agrees on a random sample of 200 classes (8,165 piece runs, 0 problems).

## What it does

Read the tape, at the moments the head is in state A just right of the last written cell, as a list of **runs of
1s separated by single 0s** (two adjacent 0s are an *empty run*, of length 0). A run of length 1 is a *unit*;
`u^k` is k units in a row. The tape is then always

    ... runs ...  [a]  u^B   A>

with one long *active* run `a` followed by B units. Everything happens at the right end:

* **cycle** (`cycle` in `lean/Rules.lean`, 6B+39 steps): the head walks left over the units to the active run,
  takes 3 cells from it and comes back writing 5 more units: `[a+3] u^B  ->  [a] u^(B+5)`.
* The cycles repeat until the active run has 0, 1 or 2 cells left: an *epoch* ends, and what happens next depends
  on `a mod 3`, and on the run to the left of the active one:
  * **a = 1**: the active run is now a unit itself; the active run becomes the next run to the left (the units
    merge). Its own cycles start.
  * **a = 0** (two adjacent 0s): the run on the left gives up one cell (`q0_unit`: a unit disappears; `q0_long`:
    a long run shrinks by 1 and merges with the new run), and the B units are filled into one new run of 2B+11.
  * **a = 2** after a long run `x+3` (`q2_long`): that run loses 3, 7 units join the units before the 2, and the B
    units become a new run of 2B-1. After an empty run or blank tape (`q2_zero`, `q2_blank`): the m units before
    the 2 become a run of 2m+4 (2m+6 after an empty run), then 6 units, then a new run of 2B-5.
  * only units, blank on the left (`units_blank`): they become one run of 2B+11.

Since B grows by 5 for every 3 cells taken from the active run, the new run is about 2·(5/3)·a = **(10/3)·a**: each
epoch multiplies the tape by about 10/3 and the step count by about (10/3)^2, which is why the tape grows like
the square root of the step count. Which branch is taken is decided by `a mod 3`, a residue of a number that is
roughly multiplied by 10/3 every epoch, so the branches come in a pseudo-random order (in 8,000 epochs: 2,634
times 0, 2,629 times 1, 2,737 times 2). The runs left of the active one form a short second-level counter that the
branches decrement, refill and occasionally merge away; in 8,000 epochs it never held more than one long run and
one block of units, and its long run never exceeded 32.

The first epochs (`python3 py/epochs.py 16`):

    epoch     3  step          21645  runs: 4 u^6 [338] u^3      (active run mod 3 = 2)
    epoch     4  step         216882  runs: u^14 [1122] u^3      (active run mod 3 = 0)
    epoch     5  step        2338267  runs: u^13 [3753] u^3      (active run mod 3 = 0)
    epoch     6  step       25890901  runs: u^12 [12523] u^3     (active run mod 3 = 1)
    epoch     7  step      287483938  runs:  [41778] u^3         (active run mod 3 = 0)
    ...
    epoch    14  step       [~10^15]  runs: 32 u^4 [191048923] u^3   (active run mod 3 = 1)
    epoch    15  step       [~10^16]  runs:  [32] u^318414878        (the run 32 becomes active)

## Where it could halt

The only halting transition is F reading 1. F is entered only from E reading 1 (`0RF`), and E from A reading 1
(`1RE`) or B reading 1 (`0LE`, moving left: then F reads the 0 that B just wrote). So a halt needs A moving right
onto `1 1 1`: A entering a run of three or more 1s from the left. In the rules above A moving right meets only
units and, in the a = 2 rules, the run of 2 itself (`A> 1 1 0`: E reads 1, F reads 0); the three near misses of the
first 10^9 steps (steps 97, 21,273 and 215,726) are of that kind. Each rule is a theorem that the stated number of
steps runs without a halt, so none of them halts. Window-based closed tape languages (`bbtools.ctl`, K up to 6; K = 8 does not
close) cannot rule this out: the invariant needs counting.

## Evidence and proofs

* `lean/Macro.lean` (kernel): the twelve local rules, including `aa111` (the only halting move).
* `c/excursion_tree.c` (trusted): the case tree of all excursions within N cells, by plain simulation.
* `lean/Rules.lean` (kernel): the cycle rule and the epoch-end rules listed above, each for all values of its
  parameters, generated from symbolic traces by `py/rules.py` (shift rules `cross_l`/`cross_r`, `rfl`, `omega`).
* `py/epochs.py` (trusted): an exact accelerated simulator, `py/fastsim.py` (run-length tape, shift rules of
  `bbtools.symtm`, words re-cut when a shift rule needs a multiple) with the proved cycle rule applied k times at
  once (`k(6B+39) + 15k(k-1)` steps). `python3 py/epochs.py 12 check` compares the whole tape at the start of each of
  the first 8 epochs (up to step 3,197,349,547) with the C simulator: identical. 8,000 epochs take 18 s and reach
  about 10^8021 steps without a halt.

## The machine as twelve rules on two stacks

Every step sequence of the machine is a sequence of these moves (`lean/Macro.lean`, each a kernel theorem for
arbitrary tapes on both sides; `py/macro.py check 14` compares them with the plain machine on all words up to 14
cells). `X> w` is state X with `w` under and right of the head; `cb <B` is state B standing on b with c to its left.

    A> 00  -> <B 01     A> 01 -> 01 A>     A> 10 -> 10 C>     A> 110 -> 101 A>     A> 111  halts
    C> 0   -> 1 D>      C> 1  -> <B 0      D> 0  -> 0 A>      D> 1   -> 1 C>
    10 <B  -> <B 01     00 <B -> 11 C>     01 <B -> 01 D>     11 <B  -> 01 A>

So B walks left over the tape two cells at a time: a pair `10` is flipped and put on the right, any other pair sends
the head back to the right (`00`: filling 1s, which builds the new long run; `11`: the bite of 3 cells out of the
active run; `01`: a unit). What the left-moving rules put on the right is only `01` and `0`, so the right tape is a
stack of pieces `01` with single 0s in between. Two 1s side by side appear on the right only when `A> 00` is applied
to `0 0 1` (it leaves `0 1 1`); in every reachable configuration found, B then stands on a pair `01`, and the two
1s are used up at once by `D> 0` and `A> 110`. A halt needs a third 1 there, and whether that can happen depends on
what is on the left at that moment.

## Excursions: the exhaustive check

An excursion starts from `w A>` (any word w, blank from the head on) and ends at the next configuration of that
form; the run from blank tape is a sequence of excursions, so **if no word w has a halting excursion, the machine
never halts**. `c/excursion_tree.c` builds the complete case tree by plain simulation: the cells left of the start
are unknown and a cell is fixed, both ways, only when the head first reads it.

    N (cells that may be read)   excursions that end   halting   not decided within N cells
    32                                    17,566           0              11,111
    48                                 3,531,878           0           2,350,679
    60                               200,500,042           0         134,459,620      (3.1x10^10 steps, 3 minutes)

No branch runs long (the longest excursion within 60 cells has 1,553 steps). The fraction of contexts in which the
head goes d cells deep falls by about 0.7 per cell (`py/macro.py depth 60 100000`); the deep ones are chains of runs
of 2 and units such as `2 2 u 2 2 u^3 2 2 2 0`, which the head threads through pair by pair.

What this does and does not show: it excludes a halting case in any excursion confined to 60 cells, for arbitrary
tapes. The excursions of the real run cross the whole block of units, far more than 60 cells, so it is not a
statement about them; for those the evidence is the proved rules (uniform in the block lengths) and the symbolic
class search below. A proof needs the excursions with *blocks of arbitrary length*, for arbitrary depth.

## Certificate searches that fail

A regular (finite-automaton) certificate would be a set of pairs (language of the tape left of the head, language
right of it) closed under the twelve rules, containing `w A>` for the tapes of the run, without `A> 111`.

* Windows around the head (`bbtools.ctl` up to K = 8, `tools/c/ngramcps.c` up to width 7 with histories): no.
* "Any tape beyond the last k cells on the left, the right tape exact" (a pushdown reachability computation, k up to
  10), and direct FAR with a last-k-cells automaton on either side (`py/far.py`, k up to 8): a halt is reachable
  in the abstraction for every k.
* Left tape as run-length blocks (alternating and solid blocks with capped counts, the far part arbitrary, reset
  to "any tape" at each `w A>`), right tape exact: block length 2 and 4, caps 2 to 6, up to 8 blocks: a halt is
  reachable in the abstraction or the set does not close within 3 million transitions.
* Automata read off the data: the classes of left tapes by which (state, right tape) can go with them, for all
  words up to 26 cells. The number of classes keeps growing with the length (58 classes among tapes of at most 16
  cells), mostly through relations of the kind "a run of n 1s on the left goes with a right tape `(01)^j 0001..`
  only if n + 2j is large enough". The exact set of reachable configurations therefore does not look regular; a
  certificate has to be a regular superset, and the ones built from those classes (up to 30 states) fail the FAR
  check.

A concrete instance of what a certificate has to know (from all words up to 26 cells): with the right tape exactly
`01 01 0001` state B meets a pair `10` or `11` on its left, never `01` or `00`, while with `01 0001` it meets `01`
or `10`. Which pair it meets was decided earlier in the same excursion, by cells that in general lie behind an
alternating stretch of unbounded length. An abstraction that forgets them lets B meet `01` there, which leads to
`D> 0001`, then to a `0 1 1` buried on the right tape, and to `A> 111`.
(The programs of the last three items were exploratory and are not kept in the repository; `py/far.py` and
`c/excursion_tree.c` are.)

## What is open, and next steps

The rules of `lean/Rules.lean` cover every epoch end that has occurred, but not every one the rewriting can produce:
an active run of 2 whose left neighbour is a run of 2 (`2 u^p 2`) recurses further left, its result depends on p
(for p >= 3 roughly `y u^s 2 u^p 2 u^B -> (y-3) u^(s+7) (2p-6) u^6 (2B-8)`). With adversarial residues the
second-level counter can grow without bound (a breadth-first closure of the prefixes with all three residues allowed
does not terminate), so a proof cannot just enumerate prefixes. Two ways forward:

* **All words.** Prove that no word has a halting excursion. The case tree above is the finite part; what is
  missing is an induction for the chains of runs of 2 and units (the head's walk through `(2 | u)*` is a walk of B
  over pairs in which the alignment shifts by one cell at each run of 2), with block lengths as parameters.
* **Only the reachable prefixes.** Show that the residues needed to grow the prefix never occur; this is a
  Collatz-like question about a mod 3 for a number multiplied by about 10/3 each epoch, and looks harder.

Heuristically the machine never halts.

## Pages

- [`pages/holdouts/1RB1RE_1LC0LE_1RD0LB_0RA1RC_0RC0RF_1RA---/explainer.html`](../../pages/holdouts/1RB1RE_1LC0LE_1RD0LB_0RA1RC_0RC0RF_1RA---/explainer.html)
- [`pages/holdouts/1RB1RE_1LC0LE_1RD0LB_0RA1RC_0RC0RF_1RA---/proof-status.html`](../../pages/holdouts/1RB1RE_1LC0LE_1RD0LB_0RA1RC_0RC0RF_1RA---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RE_1LC0LE_1RD0LB_0RA1RC_0RC0RF_1RA---/lean/check.sh
python3 holdouts/1RB1RE_1LC0LE_1RD0LB_0RA1RC_0RC0RF_1RA---/py/epochs.py 12 check   # accelerated run vs C
python3 holdouts/1RB1RE_1LC0LE_1RD0LB_0RA1RC_0RC0RF_1RA---/py/rules.py > /tmp/Rules.lean   # regenerate the rules
M=holdouts/1RB1RE_1LC0LE_1RD0LB_0RA1RC_0RC0RF_1RA---
python3 $M/py/macro.py check 14                 # the twelve rules against the plain machine
gcc -O2 -o /tmp/excursion_tree $M/c/excursion_tree.c
/tmp/excursion_tree 1RB1RE_1LC0LE_1RD0LB_0RA1RC_0RC0RF_1RA--- 48    # 3 s; 60 takes 3 minutes
python3 $M/py/far.py 6                          # no last-k-cells FAR certificate
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0LD_0RC1RA_1RD1RE_1LA0LE_0RA0RF_1RC---`](../1RB0LD_0RC1RA_1RD1RE_1LA0LE_0RA0RF_1RC---/README.md): rename A→C, B→D, C→A, D→B, E→E, F→F; it is this table started in state C
- [`1RB---_1RC1RE_1LD0LE_1RF0LC_0RD0RA_0RB1RD`](../1RB---_1RC1RE_1LD0LE_1RF0LC_0RD0RA_0RB1RD/README.md): rename A→B, B→C, C→D, D→F, E→E, F→A; it is this table started in state F
- [`1RB0RE_1LC0RA_0LD1LB_1LA1LE_0LB0LF_1LD---`](../1RB0RE_1LC0RA_0LD1LB_1LA1LE_0LB0LF_1LD---/README.md): rename A→D, B→A, C→B, D→C, E→E, F→F and exchange left and right; it is this table started in state B, in a mirror

<!-- end of related machines -->
