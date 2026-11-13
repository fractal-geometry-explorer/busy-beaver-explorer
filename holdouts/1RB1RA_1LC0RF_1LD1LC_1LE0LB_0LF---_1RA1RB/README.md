# 1RB1RA_1LC0RF_1LD1LC_1LE0LB_0LF---_1RA1RB

bbchallenge id 7085. One of the six-state holdouts whose halting from blank tape is open (group G07, family: **disordered list of odd blocks of 1s split by single 0s**).

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

## Status

Open. Lean: the halting configurations and 10^7 steps (`lean/Blank.lean`), and the crossings of a block of 1s in
both directions for every length (`lean/Shifts.lean`, kernel). Simulation: no halt in 10^9 steps.

## Second look

Up to 3·10^8 steps (21,560 visits of the right end in state A, tape 33,829 cells at the end) the tape has no long
periodic stretch at all: the longest repeated words are `1^49`, `(10)^24` and a few copies of 8- and 12-cell words.
Every sweep changes the whole tape. A test of whether a sweep acts as a sliding-block code (each new cell a function
of a window of at most 15 old cells, any fixed shift, on the last 400 sweeps) finds none: the rewriting carries
information along the tape, like arithmetic on a number written on the tape rather than a cellular automaton.
The invariant "odd blocks, single 0s" still holds at every sampled moment except near the head.

## Next steps

* Look for an arithmetic reading: the tape as a number in a mixed base (blocks `1^(2k+1)` as digits), and a sweep as
  a multiplication or division with carries (the head direction gives the carry direction).
* Prove the "odd blocks, single 0s" invariant with a CTL certificate (`bbtools.ctl`, K up to 6 with a coarser
  alphabet) and see whether it confines the halt (E1 needs `0 1` with the head in state E).

## First look

Growth class **fixed/sqrt** (left: fixed, exponent 0.11; right: sqrt,
exponent 0.505). After 1,000,000,000 steps: 62,751 cells visited (166 left of the
start, 42,569 right), 51,067 ones.

- right, step 969,632,382: `1^2 0 1 0 1 0 1^3 0 1 0 1^5 0 1^5 0 1^7 0 1^5 0 1 0 1^3 0 1^3 0 1^5 0 1 0 1^3 0 1^3 0 1^5 0 1 0 1 0 1^7 0 1^5 0 1 0 1^5 0 1 0 1^3 0 1^3 0 1^5 0 1 0 1^3 0 1 0 1^7 0 1^5 0 1 0 1 0 1^5 0 1^5 0 1 0 1 0 1^31 0 1^5 0 1 0 1^5 0 1 0 1^5 0 1 0 1^5 0 1 0 1 0 1^9 0 1 0 1 0 1 0 1 0 1^15 0 1^5 0 1 0 1^3 0 1^5 0 `
- right, step 985,355,035: `1^2 0 1 0 1 0 1^3 0 1 0 1^5 0 1^5 0 1^7 0 1^5 0 1 0 1^3 0 1^3 0 1^5 0 1 0 1^3 0 1^3 0 1^5 0 1 0 1 0 1^7 0 1^5 0 1 0 1^5 0 1 0 1^3 0 1^3 0 1^5 0 1 0 1^3 0 1 0 1^7 0 1^5 0 1 0 1 0 1^5 0 1^5 0 1 0 1 0 1^31 0 1^5 0 1 0 1^5 0 1 0 1^5 0 1 0 1^5 0 1 0 1 0 1^9 0 1 0 1 0 1 0 1 0 1^15 0 1^5 0 1 0 1^3 0 1^5 0 `

## Pages

- [`pages/holdouts/1RB1RA_1LC0RF_1LD1LC_1LE0LB_0LF---_1RA1RB/explainer.html`](../../pages/holdouts/1RB1RA_1LC0RF_1LD1LC_1LE0LB_0LF---_1RA1RB/explainer.html)
- [`pages/holdouts/1RB1RA_1LC0RF_1LD1LC_1LE0LB_0LF---_1RA1RB/proof-status.html`](../../pages/holdouts/1RB1RA_1LC0RF_1LD1LC_1LE0LB_0LF---_1RA1RB/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RA_1LC0RF_1LD1LC_1LE0LB_0LF---_1RA1RB/lean/check.sh
```
