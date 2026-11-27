# Splitting only the end words: the frontier-window decider (27 November 2026)

This is approach 1 of the last section of [`write-only-test.md`](write-only-test.md): keep the classes of the bulk
coarse, and make only the words at the end of the tape exact. Tools are in
[`../tools/frontier-window/`](../tools/frontier-window/).

## The short version

- **It reproduces the first proof of cryptids pull request 42.** For
  1RB0LD_1LC0RE_---1LD_1LE1LA_1RA0LF_1LC1RE the decider closes with no halt, and an independent checker accepts
  the certificate. This is a second, fully automatic proof of a machine that DeepMind proved by hand-built
  tables. Nothing here is in Lean.
- **No learned classes are needed for it.** The 32 cells at the left frontier are kept exact, and the rest of the
  tape is described by its first 8 cells only. The learned 13 or 14 classes make no difference.
- **It does not reproduce the second proof** (1RB0RC_1LC0RB_1LD0LD_1RA1LE_---0LF_1LB1LF), with or without learned
  classes. That proof needs classes that look through any number of runs of 6 or 8 ones. (The token decider of the
  sibling follow-up closes that one, and not this one.)
- **No open holdout is decided.** The four named in the write-only note do not close, with plain or learned
  classes. A screen of all 501 open holdouts, both directions, finds no closure (details below).
- **Of the 107 holdouts already decided by others, it closes on exactly one**, the machine above. So the decider is
  narrow: it fits a machine whose bulk can be arbitrary and whose end is a finite controller.

## The decider (`fwdec.cpp`)

Take the left end (mirror the machine for the right end). The tape is cut into two parts.

1. **An exact window** of TW cells that starts at the left frontier, the leftmost cell the head has reached.
   Everything left of it is blank.
2. **The rest, a half tape**, known only by a class: its first K cells (all of it, if it is shorter).

A step of the head out of the window into the half tape is a **call**. A call (entry state, class) has a
**summary**: the set of (return state, class afterwards). The summary of a class is computed by unfolding the class
into one cell and a class one cell further right, running that cell, and answering the calls it makes from the
summaries one level down. This is the summary decider `sumdec.py` of the write-only note. The new part is the top
level: instead of one cell at the frontier, it is the whole window, simulated exactly. When the frontier moves one
cell left, the last window cell is folded into the class.

Summaries, the unfoldings in use and the top-level configurations grow together to a least fixed point. If no
halting transition is reachable in it, the machine never halts. The argument is the step-budget induction of the
recursive-sweep proofs: a call that returns is made of shorter calls.

A class only has to be a state of some automaton that reads the half tape from its far end. So any such automaton
gives a sound decider, and `endsplit.cpp` is the general version: the class is a pair (learned class of
`learncls.cpp`, first K cells), with options to keep short half tapes exact.

## 1RB0LD_1LC0RE_---1LD_1LE1LA_1RA0LF_1LC1RE

| window TW | prefix K | result | classes | calls | summary facts | top-level configurations | time |
|---|---|---|---|---|---|---|---|
| 1 | 8 to 16 | halt derivable | | | | | |
| 28 to 31 | 8 | halt derivable, at the frontier | | | | | |
| 32 | 6, 7 | halt derivable, at the frontier | | | | | |
| **32** | **8** | **no halt** | 384 | 1,152 | 1,324 | 5,839,125 | 1.4 s |
| 33 | 8 | no halt | 384 | 1,152 | 1,324 | 8,674,415 | 2.6 s |
| 36 | 8 | no halt | 384 | 1,152 | 1,324 | 28,386,861 | 7.8 s |
| 32 | 12 | no halt | 6,150 | 18,450 | 20,217 | 25 million | 46 s |

What the closure says about the machine:

- **The bulk is unconstrained.** With K = 8 all 384 classes occur (every word of 8 cells and every shorter tape),
  and all are entered in each of the three states that move right (A, B, E). So the summaries hold for *every*
  half tape. No call ever halts, whatever is on the tape. The 7-state automaton of the DeepMind proof is not needed
  for this.
- **The halt can only happen at the frontier**, and 32 exact cells there are enough to exclude it. With 31 cells a
  halt is derivable. The DeepMind proof lists 132 exact left words of up to 45 cells; a fixed window of 32 cells
  does the same job at the price of 5.8 million configurations, because it also holds whatever a call left behind.
- **8 cells of look-ahead** is the same number the write-only test measured: at the left end the return state is
  fixed by the end word and 8 more cells.

The certificate (`fwdec ... cert.txt`) lists the class transitions, the summary facts and the top-level
configurations. `check_cert.py` is a separate program that checks the closure conditions directly from the file and
knows nothing of how it was found. With `--run N` it also replays N real steps and checks that every real
configuration inside the window is one of the listed ones (3 million steps: all covered).

The mirror image (frontier at the right end) derives a halt for every size tried.

## What does not close

**1RB0RC_1LC0RB_1LD0LD_1RA1LE_---0LF_1LB1LF.** Halt derivable for every combination tried: windows of 1, 16 and
32 cells; prefixes of 0 to 16 cells; plain classes and the learned ones (129 classes here); short far-end tapes
kept exact up to 32 cells. The halt is derived inside a call in most cases. The proof's classes are grammar
nonterminals, and `RareTail := {6, 8}* ValidR` looks through any number of runs. Neither a prefix nor a return-state
class holds that. This machine needs the token approach (follow-up 2 of the write-only note).

**The four open holdouts of the write-only note** (1RB---_1LC0RF_1RF0LD_0LE1LC_0RC0LC_1RB0RA,
1RB0LA_0RC1LF_0RD0LA_1LD0LE_1RB1LF_---1LA, 1RB0RE_1LC0RD_1LD0LD_1RA0LC_1RA1RF_1RA---,
1RB0LB_1RC1LE_1LD0RF_---1LB_0LA0LC_1LB1RA). Halt derivable in both directions for windows of 16, 32 and 48 cells
and prefixes of 4, 8 and 12 cells, and also with the learned classes (6, 11, 28 and 155 classes) in the direction
of the write-only table. For three of them the halt is derived inside a call: unlike the machine above, their bulk
is not safe for arbitrary content, so the bulk classes themselves have to be right.

**Two other end-word variants on the first machine**, both with the 14 learned classes:

- short half tapes (the words at the far end) kept exact, up to 20 cells: halt derivable;
- the class extended by the longest prefix that occurs inside a frontier window of the real run: halt derivable up
  to a window of 32 cells, and the number of such words explodes beyond (14 million factors at 48 cells).

The exact part has to sit at the top level, as a window, not inside the classes.

## Screen of all 501 open holdouts

Both directions, windows of 16, 32 and 48 cells, prefixes of 4, 8 and 12 cells: 9,018 runs.

| stage | runs | halt derivable | stopped at the limit | no halt |
|---|---|---|---|---|
| limit of 2 million top-level configurations | 9,018 | 7,859 | 1,159 | 0 |
| the 1,159 again, limit 10 million | 1,159 | 392 | 767 | 0 |
| the 767 again, limit 50 million | 767 | 270 | 497 | 0 |

So 8,521 of the 9,018 runs derive a halt and 497 run out of room. A larger window or prefix only refines the
abstraction, so a run that derives a halt rules out every smaller size too. For 843 of the 1,002 directions the
largest size (48 cells, prefix 12) derives a halt, which settles the whole grid for them.

For 212 directions (the other 159 and 53 that were only excluded at the 50 million limit) a bisection looked for the smallest window (1 to 56 cells) at which no halt is derived
within 20 million configurations, for prefixes of 8, 12 and 16 cells. With prefix 8, 42 derive a halt
even at 56 cells, and for the other 170 that smallest window is between 16 and 56 cells (median 41). With prefix
12: 25 and 187 (12 to 56 cells, median 39). With prefix 16 only 42 directions were done, because single runs took
over an hour: 2 and 40. In every case the run at that smallest window stops at the limit. None closes.

A run that stops at the limit is not a negative result: it can hide a halt that a longer run would derive, or a
closure that needs more room. On the machine above the closure appears at exactly 32 cells with 5.8 million
configurations, and the number then grows about 1.5 times per extra cell. So what the screen shows is that no open
holdout closes with fewer than 20 million configurations at the smallest window that could work.

Tables: [`screen-501-nov27.tsv`](../tools/frontier-window/screen-501-nov27.tsv) (final result of each of the 9,018
runs) and [`bisect-nov27.tsv`](../tools/frontier-window/bisect-nov27.tsv).

The 107 holdouts already decided (same grid without 48, limit 6 million): 1 closure (the machine above), 1,202
runs with a halt derivable, 81 at the limit.

## What this means for the method

The write-only note asked for a refinement rule that splits a class only where the difference decides the halt.
For the one machine where "split the end words" is the right rule, no splitting of classes was needed at all: the
end words belong in an exact window at the top level, and the bulk needs no description. Where that is not enough,
the missing information is in the bulk classes, and end words do not supply it.

Two things could widen the decider: a window whose width follows the configuration instead of being fixed (the
5.8 million configurations are mostly remains of calls that a variable window would fold away), and token classes
for the bulk.

## Reproduce

```sh
cd holdouts/recent-proofs/tools/frontier-window
g++ -O2 -std=c++17 -o fwdec fwdec.cpp && g++ -O2 -std=c++17 -o endsplit endsplit.cpp
./fwdec 1RB0LD_1LC0RE_---1LD_1LE1LA_1RA0LF_1LC1RE L 32 8 30000000 cert.txt     # NONHALT, 1.4 s, 250 MB file
python3 check_cert.py cert.txt --run 3e6                                        # certificate OK, 15 s
./fwdec 1RB0RC_1LC0RB_1LD0LD_1RA1LE_---0LF_1LB1LF L 32 12                       # HALT-REACHABLE
TW=32 LEARN=3000000 ./endsplit 1RB0RC_1LC0RB_1LD0LD_1RA1LE_---0LF_1LB1LF L 0 8  # learned classes: HALT-REACHABLE
```

`fwdec MACHINE L|R TW K [MAXTOP] [CERT]` prints `NONHALT` (proved, given the checker), `HALT-REACHABLE` (the
abstraction is too coarse; this says nothing about the machine) or `LIMIT`.
