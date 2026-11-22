# 1RB1RA_1LC0RF_1LD1LC_1LE0LB_0LF---_1RA1RB

bbchallenge id 7085. One of the six-state holdouts whose halting from blank tape is open (group G07, family: **rows of blocks of 1s rewritten by two sweeps (parity and mod 4 structure, chaotic)**).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RA |
| B | 1LC | 0RF |
| C | 1LD | 1LC |
| D | 1LE | 0LB |
| E | 0LF | --- |
| F | 1RA | 1RB |

## What it does

The tape is a list of **odd** blocks of 1s separated by **single** 0s: at step 10^9 exactly, and at 27
snapshots every 3.7·10^7 steps up to it, all runs but at most two (one even block or a double 0, presumably where
the sweep is at work) follow this rule. At step 10^9: 62,751 cells, 11,687 blocks of 1s, every 0 isolated; block lengths 1 (5,058 blocks),
3 (2,443), 5 (1,297), 7 (1,128), 9 (431), 11 (487), 13 (163), 15 (261), ... The head sweeps across the whole tape;
the right end grows like the square root of the steps and the left end stopped early. The order of the blocks looks
disordered (no long periodic stretch), and blocks of length 1 mod 4 are more common than 3 mod 4 (7,114 against
4,571).

## The two sweeps as rules on blocks

Write the tape as a row of blocks of 1s split by single 0s. The head does two things: C sweeps left, A sweeps
right. Four rules say all that happens away from the two ends (`lean/Blocks.lean`, kernel, for all sizes and any
tape around them; `py/blocks.py check` tests them on the machine):

    pass     x 1 0 1 0 1^c <C          ->  x <C 1 1 0 1^(c+2)          C passes a single 1
    bounce   1 1 0 1^c <C              ->  0 1 1 A> 1^(c+1)            C meets a block of two or more
    shred    A> 1^a 0 1^(2k+1) 0       ->  1^(a+1) 0 (1 0)^k 1 A>      A meets an odd block
    turn     A> 1^a 0 1^(2k+2) 0       ->  1^(a+1) (0 1)^k 0 <C 1 1    A meets an even block

In blocks: going left, C needs every *second* block to be a single 1. It deletes that single 1 and adds one cell
to the block on each side of it, so a block between two single 1s grows by 2, and the row `X 1 Y 1 Z 1` becomes
`X+2, Y+2, Z+2`. At the first block of two or more 1s in a "single" position, the block loses two cells and the head
turns round (`bounce`). Going right, A treats the blocks in turn: one block is shredded (`2k+1` cells become k
single 1s), the next is kept and grows by 2, and so on. A block of even length in the shredding position turns
the head round. In 2·10^10 steps C read a 0 1,250,049,447 times and bounced 208,505 times.

**The halt.** The machine halts when E reads a 1. E is entered only by C reading a 0 and then D reading a 0 on
the cell to its left, so the machine halts exactly when **C, going left, reads a 0 and the two cells to its left
are `1 0`** (`halt_pattern` in Lean). A double 0 with 1s on both sides appears in one way only: a bounce off a
block of exactly two 1s that is not the leftmost block. In 2·10^10 steps this never happened: the smallest block
bounced off (other than the leftmost) had 3 cells, and D read a 0 only 56 times, each time on the blank cell
left of the whole tape (`c/echeck.c`), where the tape then grows by four cells.

**What keeps it alive, in numbers.** `bounce` and the kept blocks keep the parity of a block; the ends of the
tape do not. At the moments C reads a 0 in the first 4·10^6 steps (`py/ngrams.py`, `py/evens.py`, 50,072 sampled
moments):

* right of the head 5,365,538 of 5,366,200 blocks (not counting the first and the last) have length 3 mod 4;
* left of the head the blocks at odd distance from the head (the "single" positions) are single 1s in 75% of
  the cases, and the blocks at even distance are single 1s or have length 1 mod 4 in 90%;
* an even block left of the head, other than the leftmost block (which is a 2), has length 0 mod 4 and is followed
  on its right by an odd number of single 1s and then a block of length 1 mod 4 (5, 9, ...) in 54,250 of 55,259
  sightings (in the others the head's own block comes next). In that place C passes it (it is in a "passing"
  position) or bounces off the block before it.

So the row carries a structure mod 4, not only mod 2: a block of length 3 mod 4 shreds into an odd number of
single 1s, which keeps the next kept block in a passing position for the sweep back; lengths 1 mod 4 put it in a
bouncing position.

**Robustness** (`py/perturb.py`): take the tape at step 3·10^5 and change one block far from the head. Adding 2,
4 or 8 cells to a block, adding one or two single 1s, or deleting a block, left or right of the head, never led to
a halt in the next 6·10^5 steps (30 trials each). Adding 1 or 3 cells to a block right of the head: no halt.
Adding 1 or 3 cells to a block **left** of the head: halt in 16 of 30 trials. Random rows of odd blocks with a
random head state halt quickly in more than half of the trials. So the run from blank tape stays inside a small
set of rows, and that set is not just "odd blocks".

**Attempts at a proof.** A closed regular set of tapes without the halting pattern would prove that the machine
runs forever. Two searches, both with automata that read a side of the tape from its far end and remember the last
few runs by length class (exact up to a bound, then mod 2 or mod 4), runs of single 1s by the parity of their
count, and flags for even blocks further out: (a) a closed position set on pairs of such automata
(`py/rlctl.py`, `py/rlf.py`): no closed set (up to 6 runs: the set grows past 1.5·10^6 abstract configurations);
(b) finite automata reduction with such an automaton on one side and the saturated automaton on the other
(`py/far.py`, `py/sat.py`): no proof with 2 to 8 runs on the left or 2 to 6 runs on the right (up to 5,471
states). The left automaton on 4 runs is complete (315 states, none new after 2·10^6 steps); the larger ones
still meet new states after 10^7 steps, and a state that the run reaches but the automaton lacks defeats the
method.

## Pascal's triangle, in a mirror (22 November 2026)

This table is the table of [`1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF`](../1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF/README.md)
(the "Pascal machine") read in a mirror, with that machine's states A, B, C, D, E, F renamed D, E, F, A, B, C
(`is_mirror`, `lean/Mirror.lean`). The blank tape is its own mirror image, so **this machine's run from blank tape
is, cell for cell in the mirror, the run of the Pascal table started in state D** (`halts_iff`). Everything proved
about the Pascal table holds for any surrounding tape, so it holds here with left and right exchanged. Read in this
machine's own terms:

* The two sweeps of "The two sweeps as rules on blocks" are the Pascal machine's: the sweep right in A/F is its
  left sweep (running parity), the sweep left in C its right sweep. The Pascal machine's right turn (E reading a 1)
  is a **left turn in B** here. The zone that is rewritten every bounce lies right of the head, next to the growing
  right end. The frozen tape lies left of the head, toward the start.
* `bounce` (Lean): at a left turn in B, with the zone a word in the 4-cell letters `0111` (1) and `1111` (0) read
  outward from the head, and the frozen tape `1 1 1 ...` left of the head, one bounce turns the zone into the next row
  of Pascal's triangle mod 2 and takes two cells from the frozen block. `bounces`: a frozen block of `2k + 1` cells
  gives `k` bounces. The rows have a closed form by Lucas' theorem (`closed_form` of `lean/P75625/Lucas.lean`, a
  statement about lists that holds as it stands).
* `halts_of_odd`, `halts_of_odd_wall` (Lean): a left turn in B at a frozen block of odd length followed by `0 1`
  halts, whatever the zone, clean or walled. That is the halt of `halt_pattern` above (C reading 0 with `1 0` to its
  left), reached by bouncing an odd block down to a single 1.
* `start` (Lean): the first left turn in B is at step 46, the list state `EO [b, a, b, a, a, a] none 0` of the
  Pascal machine's list machine (`lean/P75625/End.lean`): B on the last 1 at the left end, zone `b a b a a a`, no
  prefix. The Pascal machine's own run starts the same list machine at `EO [b, a] none 1`.
* `not_halts_of_arun` (Lean): **if that list machine never fails from `EO [b, a, b, a, a, a] none 0`, this machine
  never halts.** So this holdout is the same list program as the Pascal machine, started in another state. Every
  further theorem about the list machine (the Pascal machine's folder works on it) settles both.

How it was done: rather than restating every proof with the sides exchanged, `py/port_mirror.py` copies the Pascal
machine's Lean files unchanged into `lean/P75625/` (only their imports are renamed, so they compile next to this
folder's `Machine.lean`), and `lean/Mirror.lean` carries the theorems over with the mirror lemmas of
`tools/lean/TM/Insert.lean`. Rerun the script after that folder's files change. Kernel only, no `native_decide`.

**Where the list machine can fail (`lean/Fail.lean`, kernel, for every state).** A turn with no lone 1 in the zone
(`T`, or `EO` outside a crossing) never fails (`astep_T`, `astep_EO`). A crossing turn whose far part is clean and
whose tape ends in a single 1 never fails (`astep_T2_end`). Plain and crossing turns whose tape ends in a single 1
pass that on (`astep_endOne`), so a blank end comes only after an `EO` turn (the head on the last 1). Together
(`astep_none`): the list machine fails only at a crossing turn with blank end, at an `EO` turn during a crossing, or
at a crossing turn whose far part is not clean. This is about the Pascal machine's list machine, so it holds for all
three runs.

**The list machine from this start (`py/mirror_run.py`, computed).** Run on its own from `start`, the list machine takes 40,000 list steps without failing (19,948 `T` turns, 20,033 `T2` turns, 19 `EO` turns, zone up to 19,162 letters, every far part clean), about 15 minutes. Four of the `EO` turns come during a crossing (after list steps 34, 811, 1,408 and 4,552, zone 9 letters each time); they are the only source of the 2,343 crossing turns with blank end, and 2,339 of those have a witness (`lean/Race.lean`). The other 4 are the first bounce after each of those `EO` turns, with frozen word `s = 0`; the list machine gets past them. After list step 4,552 no `EO` turn comes during a crossing. Run in lockstep with the real machine (`python3 py/mirror_run.py lockstep D 2e8`), the list machine agrees at all 20,967 right turns of the first 2·10^8 steps of the Pascal table started in D.

## Status

Open. It halts if and only if the Pascal table started in D halts (Lean). If the Pascal machine's list machine never
fails from `EO [b, a, b, a, a, a] none 0`, it never halts (Lean). See the section above.

Open. Lean (kernel): the halting configurations and 10^4 steps, 10^7 native (`lean/Blank.lean`); the crossings
of a block of 1s (`lean/Shifts.lean`); the four block rules and the halting pattern (`lean/Blocks.lean`).
Trusted: no halt in 2·10^10 steps (`c/echeck.c`, direct simulation), with the counts above.
Trusted: no halt in 10^12 steps (`c/mrun.c` of the 1RB1LE_0LC1RE_---1LD_0RD1LA_0RF1RF_1RA0LB folder, a direct
simulator on blocks of 16 cells; the tape is then about 1.9 million cells long).

## Second look

Up to 3·10^8 steps (21,560 visits of the right end in state A, tape 33,829 cells at the end) the tape has no long
periodic stretch at all: the longest repeated words are `1^49`, `(10)^24` and a few copies of 8- and 12-cell words.
Every sweep changes the whole tape. A test of whether a sweep acts as a sliding-block code (each new cell a function
of a window of at most 15 old cells, any fixed shift, on the last 400 sweeps) finds none: the rewriting carries
information along the tape, like arithmetic on a number written on the tape rather than a cellular automaton.
The invariant "odd blocks, single 0s" still holds at every sampled moment except near the head.

## Next steps

* Write the two sweeps as a machine on rows of blocks (the four rules plus the two ends: at the right end the head
  turns in three ways, at the left end the tape grows by `1 1 0 1`), and look for the invariant there. The
  numbers say: lengths mod 4, the alternation of "single" and "passing" positions, and a short list of defects
  (the leftmost block 2, the last block, an even block of length 0 mod 4 followed by an odd number of single 1s).
* Even blocks as defects. By the rules, `pass` (a block between two single 1s: +2), `bounce` (-2 for the block
  bounced off; +2 for the block the head turns in, which also got +1 when C entered it and gets +1 when A leaves it) and a kept block of the
  right sweep (+2) keep the parity of a block. Parity changes only at the two ends of the tape and at a `turn`:
  the even block in the shredding position is shredded, and the blocks on both sides of it change parity. The halt
  is the end of an even block that sits in a "single" position when C arrives: it is bounced off again and again
  (C passes on only over a single 1), shrinks by 2 each time, and at 2 leaves a double 0. An odd block in that
  place ends as a single 1 and is passed. So the invariant has to say: no even block, other than the leftmost, is
  ever in a "single" position of a left sweep. Whether a block is in such a position depends on the parity of
  the number of blocks between it and the place where the sweep started, and on the lengths mod 4 of the blocks
  shredded on the way (an odd or even number of single 1s): counts over long stretches, which is why windows fail.
  An automaton for a certificate must carry these parities.
* With that invariant as an automaton, `py/far.py` (or `tools/lean/TM/CTL.lean` for a Lean proof) checks it.

## First look

Growth class **fixed/sqrt** (left: fixed, exponent 0.11; right: sqrt,
exponent 0.505). After 1,000,000,000 steps: 62,751 cells visited (166 left of the
start, 42,569 right), 51,067 ones.

- right, step 969,632,382: `1^2 0 1 0 1 0 1^3 0 1 0 1^5 0 1^5 0 1^7 0 1^5 0 1 0 1^3 0 1^3 0 1^5 0 1 0 1^3 0 1^3 0 1^5 0 1 0 1 0 1^7 0 1^5 0 1 0 1^5 0 1 0 1^3 0 1^3 0 1^5 0 1 0 1^3 0 1 0 1^7 0 1^5 0 1 0 1 0 1^5 0 1^5 0 1 0 1 0 1^31 0 1^5 0 1 0 1^5 0 1 0 1^5 0 1 0 1^5 0 1 0 1 0 1^9 0 1 0 1 0 1 0 1 0 1^15 0 1^5 0 1 0 1^3 0 1^5 0 `
- right, step 985,355,035: `1^2 0 1 0 1 0 1^3 0 1 0 1^5 0 1^5 0 1^7 0 1^5 0 1 0 1^3 0 1^3 0 1^5 0 1 0 1^3 0 1^3 0 1^5 0 1 0 1 0 1^7 0 1^5 0 1 0 1^5 0 1 0 1^3 0 1^3 0 1^5 0 1 0 1^3 0 1 0 1^7 0 1^5 0 1 0 1 0 1^5 0 1^5 0 1 0 1 0 1^31 0 1^5 0 1 0 1^5 0 1 0 1^5 0 1 0 1^5 0 1 0 1 0 1^9 0 1 0 1 0 1 0 1 0 1^15 0 1^5 0 1 0 1^3 0 1^5 0 `

## Deciders tried (F11, 13 November 2026)

None closes. Each reaches a halting configuration in its abstraction, which says nothing about halting.

- n-gram CPS (`tools/c/ngramcps.c`), equal widths on both sides: a halting local configuration is reached with plain up to width 24, history 1 up to width 24, history 2 up to width 24, history 3 up to width 24, LRU history up to width 3 (larger widths ran out of the 150 s or 60 million configuration budget).
- n-gram CPS with every cell tagged by its position mod p: fails for p = 2 up to width 20, p = 3 up to width 20, p = 4 up to width 20, p = 6 up to width 20.
- n-gram CPS where each side also carries the state of a small automaton that has read that side from the far end (every automaton with up to 3 states on both sides, or 4 states on one side), with position mod 1..4 and widths 4, 6, 8: no closed set without a halt in all 120 parameter sets.
- Run-length windows (the K nearest runs of equal macro cells on each side, run lengths kept exactly below T and mod M above): fails for all 72 parameter sets (cells of 1 to 4 bits, K = 2, 4, 6, T = 2, 4, M = 1, 2, 4).
- Two-automaton closed tape language by SAT (a deterministic automaton reading each side inward, n states each, CaDiCaL): no solution for n = 2..7; n = 8 not finished in 150 s.

## Where a halt can come from

`lean/Route.lean` (kernel, written by `py/route.py`): `halt_route`, two steps before any halt the machine is in one
of: C with 1 two left, 0 left, 0 under the head.

## Pages

- [`pages/holdouts/1RB1RA_1LC0RF_1LD1LC_1LE0LB_0LF---_1RA1RB/explainer.html`](../../pages/holdouts/1RB1RA_1LC0RF_1LD1LC_1LE0LB_0LF---_1RA1RB/explainer.html)
- [`pages/holdouts/1RB1RA_1LC0RF_1LD1LC_1LE0LB_0LF---_1RA1RB/proof-status.html`](../../pages/holdouts/1RB1RA_1LC0RF_1LD1LC_1LE0LB_0LF---_1RA1RB/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RA_1LC0RF_1LD1LC_1LE0LB_0LF---_1RA1RB/lean/check.sh
python3 holdouts/1RB1RA_1LC0RF_1LD1LC_1LE0LB_0LF---_1RA1RB/py/port_mirror.py      # refresh lean/P75625, Mirror.lean (both folders)
python3 holdouts/1RB1RA_1LC0RF_1LD1LC_1LE0LB_0LF---_1RA1RB/py/mirror_run.py run D 40000   # the list machine, ~15 min
python3 holdouts/1RB1RA_1LC0RF_1LD1LC_1LE0LB_0LF---_1RA1RB/py/mirror_run.py lockstep D 2e8
cd holdouts/1RB1RA_1LC0RF_1LD1LC_1LE0LB_0LF---_1RA1RB/py
python3 blocks.py check                      # the block rules against the machine
python3 blocks.py > ../lean/Blocks.lean      # regenerate the Lean rules
gcc -O2 -o /tmp/echeck ../c/echeck.c && /tmp/echeck 2e10     # bounces, D reading 0 (2 minutes)
python3 ngrams.py 4e6 3 7 2 40               # pairs of neighbouring blocks at the moments C reads a 0
python3 evens.py 3e6 1                       # where the even blocks are
python3 perturb.py 1 3e5 Lb1 30 6e5          # change one block left of the head by one cell: 16 of 30 halt
python3 sat.py 1RB1RA_1LC0RF_1LD1LC_1LE0LB_0LF---_1RA1RB L 4 4 2 2 8e6 FUPZ 4 2    # one of the FAR attempts
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0LE_1RC1RB_1RD0RA_0RE---_1LF1LA_1LA1LF`](../1RB0LE_1RC1RB_1RD0RA_0RE---_1LF1LA_1LA1LF/README.md): rename A→F, B→A, C→B, D→C, E→D, F→E and exchange left and right; it is this table started in state B, in a mirror
- [`1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF`](../1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF/README.md): rename A→D, B→E, C→F, D→A, E→B, F→C and exchange left and right; it is this table started in state D, in a mirror
- [`1RB1RC_1RC1RB_1LD0RA_1LE1LD_1LF0LC_0LA---`](../1RB1RC_1RC1RB_1LD0RA_1LE1LD_1LF0LC_0LA---/README.md): rename A→B, B→C, C→D, D→E, E→F, F→A; it is this table started in state F

<!-- end of related machines -->
