# 1RB---_1RC1RE_1LD0LE_1RF0LC_0RD0RA_0RB1RD

bbchallenge id 78977.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | --- |
| B | 1RC | 1RE |
| C | 1LD | 0LE |
| D | 1RF | 0LC |
| E | 0RD | 0RA |
| F | 0RB | 1RD |

## Status

**Open; probably nonhalting.** A counter multiplied by about 10/3 per phase drives a word of blocks; no halting word
was found. Lean proves the rounds of a phase; the word dynamics is measured by simulation (trusted).

## What it does

At every phase start the head, in state A, is at the right end of the tape and the tape reads `P 1^n 01010 A>0` (P a word
ending in 0, blank beyond). Each round of a phase takes three 1s from the counter and writes five pairs `01` at the
right. With fewer than three 1s left, the residue n mod 3 sends the head into P, which it edits, and on the way back the
pairs become the new counter: n' = 10(n div 3) + d, with d and the next word depending only on P and n mod 3. A
residue-0 phase absorbs the last block of P into the counter; the other residues push or edit blocks, often by a
smaller phase of the same kind run on a block of P: the word is a stack of nested counters.

Exploring the word dynamics breadth first for every sequence of residues (600 words, the longest 194 cells): no transition halts, and every one returns to a phase start.

From the first phase start (step 49, P empty, n = 8), computed exactly: no halt in 3,000 phases (n then has 5,214 bits); 94 distinct words, the longest 89 cells.

No halting word is known, so there is no coin-flip argument for a halt (unlike Antihydra-type machines); nonhalting is
plausible but needs an invariant on all reachable words, more than this pass could do.

**Related machines.** 1RB---_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA and 1RB0LC_1RC1RE_1LA0LD_0RB0RA_1RB1RF_1RD--- (one table, relabelled) have the same kind of phase with factor 8/3: three 1s of the counter become four pairs instead of five.

## Symbolic class search over every residue sequence (13 November 2026)

Tools: the engine with several free counts of `holdouts/1RB0LE_1RC---_0RD0RE_1LE0RB_0LA0LF_0RC0LD/py/closure/` (`paccel.py`, `pclosure.py`,
`pvalidate.py`; programs, not Lean), set to this machine by the environment (the tape is mirrored, so that the phase
start `P 1^n 01010 A>0` is an event at the near end):

```sh
D=holdouts/1RB0LE_1RC---_0RD0RE_1LE0RB_0LA0LF_0RC0LD/py/closure
export BBM=1RB---_1RC1RE_1LD0LE_1RF0LC_0RD0RA_0RB1RD BBEV=0 BBMIRROR=1 BBNODE='^001010 \(1\)\^n' BBMOD=1
python3 $D/pclosure.py bfs /tmp/c78977.json 5 1500       # 25 minutes; BBBIG=12 BBTBASE=6 or BBBIG=7 BBTBASE=4
                                                         # BBMODULI=1,2,3 for the smaller thresholds
```

A *node* is a phase start with n >= 20. A *class* is the word P with every block of at least 20 words (`1^a`,
`(01)^b`) free, together with a free n; the engine runs the class to the next phase start for all values at once and
splits it into pieces when the outcome depends on a residue (n mod 3, ...) or on the order of two counts. This
replaces the three sample counts per word of `py/phases.py bfs` by a symbolic run, and it covers every sequence of
residues, not only the real one.

| threshold | classes explored | pieces | halting pieces | undecided | classes still queued | most free counts |
|---|---|---|---|---|---|---|
| 20 | 3,619 | 101,407 | 0 | 0 | 891 | 5 |
| 12 | 3,911 | 90,505 | 0 | 0 | 540 | 5 |
| 7 | 2,418 | 105,665 | 0 | 0 | 547 | 6 |

**No piece halts, but the set does not close**: the stack gets deeper as the search goes on (words with five and six
big blocks, such as `1^a (01)^b 1 (01)^c 1 (01)^d ...` in the tape's orientation mirrored), and the queue keeps
growing. Checked against a plain simulator on a random sample of 400 classes of the first row: 16,900 piece runs and
2,400 class points, 0 problems.

**Two-sided search for chains of any length** (`py/closure/bclosure.py`). The class is a window around the head:
at most DEPTH big blocks on each side, exact cells between them, and beyond the window on each side "whatever may
follow this block", given by a successor relation on blocks that the search builds (a regular over-approximation of
the tape on both sides, so chains of big blocks of any length are covered). A class is run symbolically, with a wall
cell where a side is open, until the head reaches a wall, a phase start or a halt.

```sh
export BBM=1RB---_1RC1RE_1LD0LE_1RF0LC_0RD0RA_0RB1RD BBEV=0 BBMIRROR=1 BBNODE='^001010 \(1\)\^n' BBMOD=1
export BBBIG=7 BBTBASE=4 BBMODULI=1,2,3 BBDEPTH=1
python3 holdouts/1RB---_1RC1RE_1LD0LE_1RF0LC_0RD0RA_0RB1RD/py/closure/bclosure.py /tmp/b.json 300
```

Result: **no halting piece, and it does not close.** (This search has not been compared with a plain simulator; only its
engine has, in the one-sided search above.) With DEPTH 1, in 280 s: 7,011 classes explored, none halts,
none undecided, 97,624 queued and growing (DEPTH 2: 3,197 classes, no halt, 52,724 queued). The big blocks are not
the obstacle any more. What explodes is the exact part: blocks shorter than the threshold (7 words) are kept cell by
cell, and the tape holds chains of such short blocks (`0 (01)^5 0 (01)^6 0 (01)^5 ...`) of any length and with many
combinations of sizes. Lowering the threshold to 4 does not work with this engine: its cycle rules (needed to drain
the counter in one symbolic step) are not found from so small a base, and every class runs out of pieces.
**Two thresholds** (`BBLOW`, tried the same day). The engine keeps its threshold (7) and the classes use a lower
one: `BBLOW=4 BBDEPTH=1` makes every repeat of 4 or more words free, so short blocks are abstracted too and the
engine peels the small values off by itself. This stalls as well. In the first 890 classes no piece halts, but the
queue grows about seven classes for each one explored, and the coarser relation now produces tapes the machine
never makes (for example `(01010)^n 1 1010101 D> (10)^n ...`), on which a symbolic run does not come to an end
(3,000 pieces and 410 s for one class, then given up as undecided). A successor relation that only remembers one
block is too coarse once short blocks are free; remembering two or three blocks multiplies the number of classes.

So no class description of this kind closes the machine. What is left to try is an alphabet made of the machine's
own units instead of cells: the run/unit rule system of the relative 1RB1RE_1LC0LE_1RD0LB_0RA1RC_0RC0RF_1RA---,
with a closed set of rule-level configurations.

The accelerated simulator alone follows the run from blank tape to 3.8·10^60 steps without a halt (tape then:
`1^23 0 (10)^13 1^45 (01)^N B>` with N of 31 digits).

## Results

- `lean/Rules.lean` (generated by `py/rules.py`), `lean/Phase.lean`: `first_X`, `drain_X`, `drain_iter`: the rounds
  of a phase for every count and every word P (kernel).
- `py/phases.py check 4e8`: At all 7 transitions between the 8 phase starts of the first 4·10^8 steps (the last at step 195,362,811, n = 34,398) the measured word map predicts the next phase start.
- `py/phases.py bfs 600`, `orbit 3000`: the word dynamics and the real orbit (trusted; the
  word map by simulation from three sample counts per word and residue, which must agree).
- Lean (`lean/Blank.lean`): no halt in 10^7 steps; C (`tools/c/triage.c`): none in 10^9.

## First look

Growth class **fixed/sqrt** (left: fixed, exponent 0.06; right: sqrt,
exponent 0.531). After 1,000,000,000 steps: 85,710 cells visited (11 left of the
start, 67,834 right), 49,084 ones.

- right, step 971,537,836: `1^32 0 1 0 1 0 1 0 1 0 1 0 1 0 1^12822 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0`
- right, step 987,371,317: `1^32 0 1 0 1 0 1 0 1 0 1 0 1 0 1^12603 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0`

## Pages

- [`pages/holdouts/1RB---_1RC1RE_1LD0LE_1RF0LC_0RD0RA_0RB1RD/explainer.html`](../../pages/holdouts/1RB---_1RC1RE_1LD0LE_1RF0LC_0RD0RA_0RB1RD/explainer.html)
- [`pages/holdouts/1RB---_1RC1RE_1LD0LE_1RF0LC_0RD0RA_0RB1RD/proof-status.html`](../../pages/holdouts/1RB---_1RC1RE_1LD0LE_1RF0LC_0RD0RA_0RB1RD/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB---_1RC1RE_1LD0LE_1RF0LC_0RD0RA_0RB1RD/lean/check.sh
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0LD_0RC1RA_1RD1RE_1LA0LE_0RA0RF_1RC---`](../1RB0LD_0RC1RA_1RD1RE_1LA0LE_0RA0RF_1RC---/README.md): rename A→F, B→C, C→D, D→A, E→E, F→B; it is this table started in state D
- [`1RB1RE_1LC0LE_1RD0LB_0RA1RC_0RC0RF_1RA---`](../1RB1RE_1LC0LE_1RD0LB_0RA1RC_0RC0RF_1RA---/README.md): rename A→F, B→A, C→B, D→C, E→E, F→D; it is this table started in state B
- [`1RB0RE_1LC0RA_0LD1LB_1LA1LE_0LB0LF_1LD---`](../1RB0RE_1LC0RA_0LD1LB_1LA1LE_0LB0LF_1LD---/README.md): rename A→F, B→D, C→A, D→B, E→E, F→C and exchange left and right; it is this table started in state C, in a mirror

<!-- end of related machines -->
