# 1RB1RA_1LC0RB_1LE0LD_0LB1LD_0RA0LF_---0RE

bbchallenge id 46435. Open. A **nested drain/copy counter**: a few long blocks `(010)^a` are poured, one after the other, into a final
block `(01011)^b` (b gains 7 cells per 2 pairs drained); when all are poured, the final block is copied back out as
new `(010)` blocks and the next level starts, roughly eight times larger. The two main phases are proved in Lean as
one-cycle rules for all block sizes.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RA |
| B | 1LC | 0RB |
| C | 1LE | 0LD |
| D | 0LB | 1LD |
| E | 0RA | 0LF |
| F | --- | 0RE |

## The tape as words

At the left end of the tape (head on the new leftmost cell) the tape reads, apart from a few cells at each end,

    (010)^a1 1 1 1 ... (010)^ak 1 1 1 (01011)^b 0 1

e.g. step 33,886,934: `0 0 1 1 0 1 0 0 1 0 1 1 (010)^888 1 1 1 0 1 0 0 1 0 1 1 (010)^906 1 1 1 (01011)^981 0 1`.
During a rightward sweep the same blocks show up as rotations of the words (`001`, `00111`, `11100`, `10011`).

## Phases

| phase | tape at the left end | one cycle | proof |
|---|---|---|---|
| drain | `0^inf E>(011)^4 (010)^(a+6) 111 (01011)^(b+1) 0 1` | a-4, b+14, 16 visits, 168a+224b+2978 steps | `drain`, `lean/Rules.lean` |
| split | `0^inf B>0 0 (110101)^c 1101 (100)^(d+3) 10 111 (01011)^(b+1) 0 1` | c+1, d-2, b+2, 4 visits, 32b+50c+24d+228 steps | `split`, `lean/Rules.lean` |
| feed | `(110101)^c 1 1 [short (010) blocks] (010)^e 111 (01011)^b` | c-1, b+~5; the short blocks count | simulation |

(Both rules are for every value of the variables, kernel-checked; `py/rules.py` writes `lean/Rules.lean`.)

When the last `(010)` block is empty the next one to its left drains; when none is left a long copy phase writes the
final block back as a fresh `(010)` block of the same length. Levels seen (the tape at each copy):

| step | tape |
|---|---|
| 5,355 | `(010)^12 111 (01011)^13` |
| 284,266 | `(010)^107 111 (01011)^108` |
| 19,588,355 | `(010)^906 111 (01011)^907` |
| 1,255,481,375 | `(010)^7265 111 (01011)^7265` |
| 6,126,135,498 | `(110101)^3634 1 1 (010)^14532 111 (01011)^14531` |

At the fourth level the split phase appears: the block being drained gives half of itself to a new block
`(110101)^c` at the left end (c reached 3,634) and the other half to the final block; then in the feed phase the
`(110101)` block is fed back one word every few sweeps through a small counter of short `(010)` blocks, which looks
like the whole process again at a small scale. At step 9,775,936,642: `(110101)^2158 1 1 (010)^4 1 1 (010)^4 ...
(010)^14520 111 (01011)^21906`.

## Halting

The only halting transition is F on a 0, and F is entered only from E reading a 1 (moving left). In every phase above
the cell F then reads is a 1 inside the words; a halt needs a phase boundary that puts F next to a 0, which has not
happened in 10^15 steps (accelerated simulator below).

## Copy phase and the accelerated run

The copy phase is now a proved rule (`copy` in `lean/Rules.lean`, kernel): one visit of the right end,

    L (01111)^(n+2) (010)^(m+1) 0 1111 (00111)^(m+1) B> 0^inf   --28m+55 steps-->   same with n-1, m+1

for every n, m and every tape L. A feed round (32b+34c+24d+3813 steps, found by `bbtools.symtm`) is too long for the
kernel to check in reasonable time and memory, so it is described here but not in Lean.

`c/hsim2.cpp` is a block macro simulator that takes a linear jump over k cycles only after checking the cycle
symbolically for every larger count, summing the step count exactly. `py/cmpc.py 5e10` checks it against plain
simulation (`c/dump.c`): state and all 357,144 cells agree at 50,000,245,146 steps. It runs to 1.05e15 steps with no
halt. Final-block size at each copy (heuristic reading of its output):

| b | step |
|---|---|
| 13 | 5.4e3 |
| 108 | 2.8e5 |
| 907 | 1.96e7 |
| 7,265 | 1.26e9 |
| 14,531 (after split) | 6.1e9 |
| 33,000 | 1.67e10 |
| 83,545 | 1.66e11 |
| 375,963 | 3.37e12 |
| about 3.0e6 | 2.15e14 |
| about 6.0e6 (after split) | 5.4e14 |
| 6,015,471 | 1.05e15 |

At 1.05e15 the tape is `(011101)^1503867 (001)^6015471 01110 (10110)^6015471`. The ratios depend on which phase
starts, so the level map looks Collatz-like; its exact form is not derived.

## Levels and the level map (13 November 2026)

Checkpoint: state B on the first blank cell right of the tape. A **level** starts at a checkpoint
`T (01111)^b B> 0^inf` (the final block has just been rewritten as `(01111)^b`); the level is (b, T).
`py/closure.py` (the sibling's closure engine on the mirror image of this machine) runs each level type
symbolically, b and the other block counts free, splitting on residues only when needed. Result (59 s): 14 types,
89 cases pass, 2 fail, **no case halts**; not closed.

Short tails (real orientation; P = `0 111 0 11111 0 1111 0`):

| level | next level |
|---|---|
| (b, P) | b+4, with a block `(100)^(b-5)` in T (the copy) |
| (b, T with `(100)^c`) | 18k0 + 14k1 + const for b = 4k0+r, c = 4k1+s; about 4.5b + 3.5c; next tail by the residues (16 cases) |
| b, tail `1 00 1111 0 1111 00` | doubling: b even -> 2b+1 with `(001111)^m`, m = b/2+1; b odd -> 2b+1 with `(011110)^m`, m = (b+5)/2 |
| b, four other short tails | b = 4k+r -> 18k + const (x 4.5), next tail by r |

(Exact constants: `py/closure.py` prints them, e.g. `4k+216 -> 18k+971`.)

The two types that fail hold a long block of six-cell words `(011110)^m` or `(110011)^m` next to the final block:
proved for the first two values of m only, then "a phase with no linear cycle". That is the feed phase with its
small counter. With made-up counts (`py/levels.py 6 400 1 48`, `py/levels.py 7 400 1 40 300`) every m reaches a next
level and none halts, but b' is not monotone in m (b = 400: m = 13 -> 2048, 14 -> 2441, 15 -> 1862) and the next
tail takes at least nine shapes, two of them outside the 14 types: the outcome depends on the digits of m, as for the
sibling 1RB0RE_0LC0RF_1LD1LC_1RA0LD_0RD1RE_---0LB (whose counter is binary). So the type list does not close with
finitely many count-parametrised shapes.

The run from blank tape as levels (`c/hsim2.cpp` with LEVELS=1, `py/lvx.py`; 570 s, 1.646e15 steps, no halt):

| step | b | type |
|---|---|---|
| 8.05e6 | 906 | P |
| 1.97e7 | 910, `(100)^901` | copy done |
| 5.16e8 | 7,265 | doubling |
| 3.17e9 | 14,531, m = 3,635 | counter |
| 6.82e10 | about 83,546 | short tail |
| 1.39e12 | about 375,960 | P |
| 3.37e12 | about 375,965, `(100)^375959` | copy done |
| 8.85e13 | about 3,007,734 | doubling |
| 5.43e14 | 6,015,471, m about 1,503,869 | counter (still inside at 1.646e15) |

("about": read while the block is being rewritten, a few words short.) The second round repeats the types of the
first, but there is **no exact growth cycle** `C(r) -> C(r + const)`: growth is multiplicative, the next type is
chosen by b mod 4 (or mod 2) and after a counter level by the digits of m, and `4k+r -> 18k+c` does not preserve
b mod 4. Whether the type sequence stays periodic is open.

Halting, exactly: the machine halts iff `0 1 [C on 0]` occurs (C on a 0 with `0 1` to its left): C writes 1 and
steps left, E reads that 1 and steps left, F reads the 0.

Lean: `lean/Visits.lean` (from `py/visits.py`) proves the fourth cycle the closure run uses, the **pour** cycle, as 20
one-visit theorems `pour1`..`pour20`: `0^inf 1 (100111)^3 (001)^(d+4) 1 1 1 0 (01110)^(a+2) 0 1 1 1 B> 0^inf` returns
with d-2, a+10. (The other three cycles are `copy`, `drain`, `split`.) Notes: `/mnt/project-files/g09-drain-copy-1/notes.md`.

## Status

Open. Kernel: halting configurations and 10,000 steps (`lean/Blank.lean`), the drain and split cycles
and the copy cycle (`lean/Rules.lean`), the pour cycle visit by visit (`lean/Visits.lean`). Native: 10^7 steps. Trusted: no halt in 1.6*10^15 steps; the level map for twelve of fourteen level types, no halting case (`py/closure.py`). The simulator is `c/hsim2.cpp` (checked
cell for cell at 5e10 by `py/cmpc.py`). The feed phase and the transitions between phases are described from
simulation only.

## For later

* Prove the feed round (split it into shorter pieces the kernel can check) and the phase transitions as rules, then the level map
  as a function of the block sizes.
* The feed phase has a small counter in the middle; find its rules (it may be the same machine one level down).
* `python3 -m bbtools.cycles` with block size 15 accelerates the run with proved cycles; a long run of it would show
  the next levels.

## First look

Growth class **sqrt/sqrt** (left: sqrt, exponent 0.638; right: sqrt,
exponent 0.46). After 1,000,000,000 steps: 53,968 cells visited (8,338 left of the
start, 31,625 right), 29,068 ones.

- left, step 500,184,998: `E>0 1^2 0 1 0 1 0 1^2 0 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0 1^3 0 1 0 1^2 0 1 0 1^2 0 1 0 1^`
- left, step 515,991,454: `E>0 1^2 0^2 1 0 1^2 0 1 0^2 1 0 1^3 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 `
- right, step 970,063,711: `0 1 0^2 1^4 0 1^4 0^2 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^`
- right, step 985,818,289: `0 1 0^2 1^4 0 1^4 0^2 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^`

## Pages

- [`pages/holdouts/1RB1RA_1LC0RB_1LE0LD_0LB1LD_0RA0LF_---0RE/explainer.html`](../../pages/holdouts/1RB1RA_1LC0RB_1LE0LD_0LB1LD_0RA0LF_---0RE/explainer.html)
- [`pages/holdouts/1RB1RA_1LC0RB_1LE0LD_0LB1LD_0RA0LF_---0RE/proof-status.html`](../../pages/holdouts/1RB1RA_1LC0RB_1LE0LD_0LB1LD_0RA0LF_---0RE/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RA_1LC0RB_1LE0LD_0LB1LD_0RA0LF_---0RE/lean/check.sh
gcc -O2 -o ev holdouts/1RB1RA_1LC0RB_1LE0LD_0LB1LD_0RA0LF_---0RE/c/ev.c && ./ev 1RB1RA_1LC0RB_1LE0LD_0LB1LD_0RA0LF_---0RE 2000000000 L B 1 100000 12 | awk 'NR%200==0'
```
