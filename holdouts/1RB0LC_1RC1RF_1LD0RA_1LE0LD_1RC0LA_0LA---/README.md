# 1RB0LC_1RC1RF_1LD0RA_1LE0LD_1RC0LA_0LA---

bbchallenge id 16113. Group G01. **Doubling counter paid by a block** (structure found, map not yet): Y(n) = (101)^n 10 A> recurs; in between a (110)^b counter doubles while the (101)s last. Open. **Same table as 1RB0LD_1LC0RD_1LA0LC_1RE0LB_1RB1RF_0LD--- with the states renamed** (another start state); the quadrupling round is now exact.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LC |
| B | 1RC | 1RF |
| C | 1LD | 0RA |
| D | 1LE | 0LD |
| E | 1RC | 0LA |
| F | 0LA | --- |

## What it does

    Y(n) = 0^inf (101)^n 10 A> 0^inf

occurs from blank tape for n = 23 (step 2,879), 69 (23,111), 349 (556,423), 965 (4,542,211), 4657
(121,371,567), 11789 (804,211,967).

Between two Y's (moments with the head in A at the right end), the tape is `(101)^a w (110)^b A> 0`:

    Y(23) → (101)^3 100 (110)^32 → (101)^3 (110)^34 → (110)^68 → Y(69)
    Y(69) → (101)^38 100 (110)^82 → (101)^38 (110)^84 → (101)^5 0 (110)^168 → … → (110)^348 → Y(349)

The `110` counter doubles in each round (b → 2b or 2b + 4; from synthetic starts 10, 24, 52, 108, 220) and the
`101` block pays for it; when it is used up the counter becomes the next Y. Synthetic starts can halt (e.g. Y(43) in
421,588 steps). This is the same idea as the doubling counter of 1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE; the
cost of a round and the endings are not yet worked out.

## Same table as 1RB0LD_1LC0RD_1LA0LC_1RE0LB_1RB1RF_0LD---

Renaming the states (A→D, B→E, C→B, D→C, E→A, F→F) turns this transition table into the one of `1RB0LD_1LC0RD_1LA0LC_1RE0LB_1RB1RF_0LD---`; only the start state differs.
So both holdouts are runs of one table from two different starts (two separate halting questions) and every rule below holds for both (tape words are unchanged; this
machine's state C is the other's B).

## The quadrupling round (exact)

With the head at the left end in state C reading `000`:

    C> 000 (100)^c (010)^(b+2c+1) X   →   C> 000 (100)^(4c) (010)^b X       in 60c² + 13c + 39 steps   (c ≥ 3)

for any tape X to the right (the round never reaches X). Checked by direct simulation for c = 3..39, b = 0..7 and
four tails X, 1,184 cases with their step counts (`py/quadround.py`). In the run the counter
goes 10, 40, 160, 640, … until the block of `010`s cannot pay; the ending depends on the remainder and on the list
to the right and is not yet mapped.

## The list form and its rules (third pass)

Sampled when the head is in state C at the left end reading `000`, **every** tape seen (from blank tape and from
thousands of synthetic starts) is a list of runs of the word `100` with short separators:

    [n1 s1, n2 s2, ..., nk 1]  =  C> 000 (100)^n1 s1 (100)^n2 s2 ... (100)^nk 1          s_i in {0, 1, 00, ...}

(`(010)^b 01` is `0 (100)^b 1`, so P(c, b) = `000 (100)^c (010)^b 01` is [c 0, b 1], and `000 (100)^c 1 (100)^d 1`
is [c 1, d 1].)  The head works on the first runs only. The rules found, each checked against direct simulation for
every parameter below 40 (`py/listmap.py check`, 60,000 cases, all agree):

| list | next event | name |
|---|---|---|
| [c 0, b s, …], b ≥ 2c+1, c ≥ 3 | [4c 0, b−2c−1 s, …] in 60c²+13c+39 steps | quad |
| [c 0, b 1], b = 2c | [4c−1 1] | |
| [c 0, b 1], b = 2c−1 | [2 0, 4c 1] | |
| [c 0, b 1], b ≤ 2c−2 even | [2c−b−1 1, 2b+2 1] | P even |
| [c 0, b 1], b ≤ 2c−3 odd | [2 0, 2c−b−3 0, 2b+2 1] | P odd |
| [c 1, d 1], d ≥ 2c | [2 0, 2d 1] | |
| [c 1, d 1], d < 2c even / odd | [2c−d−1 0, 2d+2 1] / [2c−d+1 0, 2d+1 1] | R even / odd |
| [n 1], n ≥ 2 | [2 0, 2n 1] | single |
| [2 0, x s, …] / [1 0, x s, …] | [10 0, x−6 s, …] / [8 0, x−5 s, …] | restart |
| [c 0, b 0, e 1], b < 2c−1 odd, e even | [2 0, 2c−b−1 1, 2b−e−1 1, 2e+2 1] if 2b−e−1 ≥ 1, else [2 0, 2c+b−e−3 00, 2e+2 1] | P3 odd |
| [c 0, b 1, d s, …], b < 2c−1 odd, d ≥ 2b+2 | [2 0, 2c−b−3 00, 4b+2 1, d−2b−2 s, …] | carry 1 |
| [c 0, b 1, d 1, e s, …], b odd, d ≤ 2b−2 even, e ≥ 2d+2 | [2 0, 2c−b−1 1, 2b−d−1 00, 4d+2 1, e−2d−2 s, …] | carry 2 |
| [c 0, b 00, d 1, …], b < 2c−3 odd, d even | [2 0, 2c−b−3 0, 2b+d+4 1] (3 runs) or [2c−b 1, 2b+d+1 0, e−1 s, …] | P00 odd |

(lists are normalised: a run of length 0 merges its two separators.)  So the first run is a counter that
quadruples (10, 40, 160, 640, …, paid 2c+1 at a time by the second run) and, when the second run cannot pay, a
**flip** rewrites the front of the list: x → 2x − y − 1 for consecutive runs, doubling the run that is reached, with
the parity of the second run deciding whether a new head `[2 0 …]` is pushed (which restarts the counter at 10). Odd
remainders push the flip deeper into the list, like a carry. The rules depend on parities and separators; lists with
odd runs further down follow rules not yet written (for example [c 0, b 1, d 1, e 1] with d odd).

**The run from blank tape** (`py/listmap.py blank`, direct simulation; `data/blank_events.txt`) is
[2 0, 2 1] at step 91, …, [160 0, 148 1], [171 1, 298 1], [43 0, 598 1], [172 0, 511 1], [688 0, 166 1],
[1209 1, 334 1], [2083 0, 670 1], …, [17404 0, 34303 1] (step 1.37·10¹⁰), then the odd flip
[2 0, 502 0, 68608 1] and the restart 10, 40, 160, 640, then [2 0, 137216 1] (step 8.80·10¹⁰), …,
[40960 0, 109904 1] at step 94,680,031,989 and [163840 0, 27983 1] at step 195,343,860,508: every one of these events is the one the table predicts. The rules then
predict (`py/listmap.py iterate 40960:0,109904:1`) 29 further events, through three- and four-run lists such as
[2 0, 137218 1, 324953 1, 111938 1] and [2 0, 299692 00, 111942 1, 268981 1, 111938 1], to
[137221 1, 492861 0, 268980 1, 111938 1], where a case not in the table (an odd run below the front) is met. The
quadrupling rounds alone on this stretch cost more than 4·10¹² steps.

**Halting.** One way to halt is known, and it is exact: a quadrupling round that leaves 0 copies of the second run,
in a list of at least three runs whose second separator is 1,

    [c 0, 2c+1 1, d s, …]  →  [4c 01, d s, …]  →  halt before the next event        (c ≥ 3)

checked for every c = 3..39 with many tails (3,498 cases, `py/listmap.py check`); for example
[640 0, 98 01, 162 1] halts after 5,029,947 steps. (With two runs there is no halt: [c 0, 2c+1 1] → [4c 01] goes on.)
So the run from blank tape halts if, in a list of three or more runs, the second run is hit exactly:
b = (2c+1) + (8c+1) + … + (2·4^k c+1) for the counter c at which the phase started. A phase starts from c = 10
(or 8) after each restart, so for a second run of size b there are about log₄ b target values among b: a chance of
about (log b)/b per phase, with b doubling from flip to flip. The sum over phases converges and is small from where
the run is now (b > 10⁵): **probably non-halting, but nothing proved**; in the run so far (46 events) and in the 10¹⁸
steps of the macro simulator no halt occurs. Whether other list shapes (odd runs below the front) can halt is not
known.

## How far (third pass)

The macro simulator `c/msim.c` of holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA--- (blocks of 6 cells; checked
against the direct simulator at 10⁹ steps by `../1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA/py/check_msim.py check`)
runs this machine and its twin 1RB0LD_1LC0RD_1LA0LC_1RE0LB_1RB1RF_0LD--- to 10¹⁸ steps without a halt
(`check_msim.py run MACHINE 1e18`).

No pushdown certificate with a small DFA exists: the reduction of `bb6-1RB0LF_1RC0LB/c/pds.c` (one side of the tape
exact, the other a DFA, post* saturation) fails for every DFA with at most 6 states, on either side.

## What is proved

| level | result | where |
|---|---|---|
| kernel | halting configurations; no halt in 10⁴ steps (10⁷ by native_decide) | `lean/Blank.lean` |
| trusted | no halt in 10⁹ steps | `holdouts/triage.json` |
| trusted | the Y-events above; the counter rounds | `py/explore.py 23` (and 30, 69) |
| trusted | the quadrupling round, exact, c ≥ 3 (1,184 cases) | `py/quadround.py` |
| trusted | the list rules of the table and the halting rule (60,000 cases) | `py/listmap.py check` |
| trusted | every event from blank tape to step 1.95·10¹¹ (46 events) is the one the rules predict | `py/listmap.py blank`, `data/blank_events.txt` |
| trusted | no halt in 10¹⁸ steps (both start states) | `msim.c` via `check_msim.py run` |
| heuristic | the next 29 events, from the rules applied beyond their tested range | `py/listmap.py iterate 40960:0,109904:1` |
| open | the rules for odd runs below the front; halting | |

## Further work

- The general flip: write the carry through the list for every parity pattern (the table has the cases met so far)
  and iterate the list map with big integers; then make the estimate of the halting chance (an exact hit of the second run) precise.
- Lean: the quadrupling round for all c. Its inner loops are known (a phase in which the `(100)^c` block becomes
  `(101)^(2c)`, then 2c−2 passes `(101)^k 1 00 A> (001)^(2i) 000 (100)^n 1` → `(101)^(k−1) 1 00 A> (001)^(2i+2) 000
  (100)^(n−1) 1`), but `bbtools.symtm` does not cross the `(110)^n 1 1 D>` sweep inside a pass without a re-bracketing
  it does not find; a hand-written shift lemma and an induction as in `../1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---/lean/Macro.lean`
  would do it.

## Pages

- [`pages/holdouts/1RB0LC_1RC1RF_1LD0RA_1LE0LD_1RC0LA_0LA---/explainer.html`](../../pages/holdouts/1RB0LC_1RC1RF_1LD0RA_1LE0LD_1RC0LA_0LA---/explainer.html)
- [`pages/holdouts/1RB0LC_1RC1RF_1LD0RA_1LE0LD_1RC0LA_0LA---/proof-status.html`](../../pages/holdouts/1RB0LC_1RC1RF_1LD0RA_1LE0LD_1RC0LA_0LA---/proof-status.html)

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0LD_1LC0RD_1LA0LC_1RE0LB_1RB1RF_0LD---`](../1RB0LD_1LC0RD_1LA0LC_1RE0LB_1RB1RF_0LD---/README.md): rename A→D, B→E, C→B, D→C, E→A, F→F; it is this table started in state E

<!-- end of related machines -->
