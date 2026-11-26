# 1RB0RE_1RC1RE_1LD1LC_0RB0LC_1RF0RB_---1RA

bbchallenge id 98995. One of the six-state holdouts whose halting from blank tape is open (group G09: the visited tape grows like the square root of the step count on both sides).

**What it does.** A bouncer. The right 60% of the tape is the word `01011111` repeated, crossed word by word by both sweeps (proved); the left 40% is a zone in which every run of 1s is odd and every 0 single (observed at every sweep end), rewritten every round trip like a cellular automaton. The leftward sweep just moves each 0 one cell left; the rightward sweep zigzags through the zone. The halt (F0) needs E on two 0s in a row, which no run has shown. Decision: open. Since 26 November the whole run is known to be the iteration of one 4-state automaton on a bit word (section "The bit model").

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RE |
| B | 1RC | 1RE |
| C | 1LD | 1LC |
| D | 0RB | 0LC |
| E | 1RF | 0RB |
| F | --- | 1RA |

## The sweeps

Each round trip adds 1 cell at the left end and 3 at the right (2,094 and 2,090 of 2,100 visits in the first 2·10^7 steps). The leftward sweep is C
running left over the 1s (`left_ones`); a 0 with a 1 before it moves one cell left (`shift_zero`: `1 1 C>0` becomes `C>1 0 1`). The rightward sweep
zigzags through the irregular zone (B, E, F, A; `right_E`, `right_A`, `right_F` inside long stretches) and runs straight through the periodic block
(`right_block`) to the right end, where A, B and C write three new cells and C turns back (`right_end`).

## The tape as words

The right end of the tape is `(01011111)^n`, a steady 60% of the tape (at visits to the left end: 2,088 of 2,818 cells at step 2.2·10^6, 15,448 of 25,718
at step 1.9·10^8). The rest, at the left, satisfies at every sweep end checked (816 visits to the left end, 817 to the right, first 3·10^6 steps): every
run of 1s has odd length and every 0 is single (apart from the two 0s at the left end and the three at the right end). For example, run lengths of 1s at
one visit to the left end: `3 1 1 3 3 1 1 3 3 7 5 1 1 7 5 1 3 5 5 9 1 3 1 1 1 1 1 1 9 11 5 7 ...` So the zone is a list of odd numbers; a round trip
rewrites the list with no known rule, and the zone grows by about 1.6 cells per round trip while the block grows by 2.4.

## The bit model (26 November 2026): one round trip is a 4-state automaton

Computed, not proved. Scripts: `py/bitmodel.py` (the model and its checks) and `c/model.c` (the model run far).

**The tape is a bit word.** At a left-end turn (D on the leftmost visited cell) the tape is `w0 1 w1 1 ... wm 1`
with `w0 = 0`: every second cell is 1, and the other cells spell a word w. The "odd runs, single 0s" rule above is
this fact. The periodic block is `w = ... 0011 0011 0`.

**One round trip.** The new word is g(w) with two or three bits added at the end. g keeps w0 and reads w1, w2, ...
with this automaton, started in X:

| state | read 0 | read 1 | mode |
|---|---|---|---|
| X | write 1, go to P | write 0, stay in X | invert |
| P | write 1, go to X | write 0, go to Y | invert |
| Y | write 0, go to X | write 1, go to Q | copy |
| Q | write 0, go to Y | write 1, go to Y | copy |

Read as tokens: in invert mode `1` becomes `0`, `00` becomes `11`, and `01` becomes `10` and switches to copy mode;
in copy mode `10` and `11` stay as they are, and `0` stays and switches back to invert mode.

**The end of the pass decides everything.**
- Pass ends in P: the machine adds `1 0` and turns back.
- Pass ends in Y: it adds `1 1 0` and turns back.
- Pass ends in X or Q: **the machine halts** in that round trip.

So from lap 3 on (step 15, w = `001`) the machine is this iteration, and it halts exactly when a pass ends in X or Q.

**Checks.**
- From blank tape the model reproduces every one of laps 3 to 2,561 (the first 3·10^7 steps), bit for bit
  (`bitmodel.py run 30000000`).
- 20,000 random words of 4 to 40 bits, each run for one round trip on the machine: 0 disagreements. 11,082 of them
  halt, in the machine and in the model alike (`bitmodel.py random 20000`).

**What it explains.**
- *The block repairs the pass.* On `(0011)*` the automaton enters the cycle X P X X from any state and any phase
  within 10 bits (all 16 cases listed), and from then on it inverts the block, which is the same block two bits
  along. A pass that crosses 10 clean block bits therefore ends in P. A halt needs the irregular zone to come within
  10 bits of the right end.
- *The zone is not chaotic.* g is invertible on words of each length, so every prefix of w repeats: the first 4
  cells of the tape with period 2 in the lap number, 8 cells with period 4, 20 with 8, 24 with 16, 32 with 32, 48
  with 512 (model, laps 400 to 6,000). The zone is the orbit of one automaton, like the digits of a counter.
- *The race.* The word grows by 2 bits per lap. In 200,000 laps of the model (about 1.8·10^11 machine steps) the
  last copy-mode state sits at 0.42 to 0.43 of the word from lap 16,384 on, the pass never ends in X or Q, and after
  lap 4 it always ends in P.

**No invariant of the shape "zone, then enough block" can work.** `c/allwords.c` runs the model from every word of
12 bits followed by K periods of the block and a final 0, for 3,000 laps. Some of them halt, even with a long block:
1,272 of 2,048 for K = 0, 577 for K = 1, 412 for K = 2, 185 for K = 3 and 9 for K = 5 (20 block bits), the latest at
lap 162. A zone can also advance faster than the word grows for a while: among 16-bit zones the fastest covers 273
bits of block in 96 laps, against 192 bits of growth. In every such case tried the burst ends and the zone then
falls behind again (six start words, 100,000 laps each, no halt). So whether the real run halts depends on its own
zone, not only on the zone's shape, and the bound has to be about the orbit of `001`.

**What is missing for a proof.** (1) The model itself in Lean: the rightward and leftward sweeps as two passes over
the bit pairs, by induction on the word. The cases are finite and small. (2) A bound that keeps the last copy-mode
state away from the end of the word. With (1) this is a statement about the 4-state automaton alone:
for the word U = `001` followed by the block forever, the first point where g^t(U) leaves the block pattern stays
below 2t.

## Halting

F0 is the only halting transition and F is entered only by E0 (write 1, move right): the machine halts exactly when E reads two 0s in a row. With every
0 single inside the tape, that needs a new double 0 or E at the blank right end; the periodic block always brings A there instead. In the first 10^9
steps F is entered 60,675,981 times and reads 1 every time.

## Sweep rules (`lean/Rules.lean`)

Generated by `py/rules.py` with `tools/py/bbtools/symtm.py`; every rule holds for all values of `n` and every tape `L`, `R`, with the exact step count. `S>` is the head in state S on the next cell, `(w)^n` is n copies of w, `0^inf` is blank tape.

| rule | from | to | steps |
|---|---|---|---|
| `left_ones` | `L 1^n C> 1 R` | `L C> 1 (1)^n R` | n |
| `shift_zero` | `L 1 1 C> 0 R` | `L C> 1 0 1 R` | 2 |
| `left_block` | `L (11010111)^n C> 1 R` | `L C> 1 (01011111)^n R` | 8 · n |
| `right_block` | `L B> (11111010)^n R` | `L (10101111)^n B> R` | 8 · n |
| `right_E` | `L E> (011)^n R` | `L (110)^n E> R` | 3 · n |
| `right_A` | `L A> (101)^n R` | `L (011)^n A> R` | 3 · n |
| `right_F` | `L F> (110)^n R` | `L (101)^n F> R` | 3 · n |
| `right_end` | `L 0 1 0 1 1 F> 1 0^inf` | `L C> 0 0 1 1 1 1 1 0 1 0^inf` | 11 |
| `left_end` | `0^inf C> 0 1 R` | `0^inf 0 1 0 B> R` | 4 |

## Status

Open. Lean, kernel only: the halting configurations, no halt in 10,000 steps (`lean/Blank.lean`), the sweep rules (`lean/Rules.lean`). Lean with `native_decide`: no halt in 10^7 steps. C: no halt in 10^10 steps. Observed: odd runs and single 0s in the left zone, the periodic block on the right.

**For later.** Prove the odd-runs invariant: a closed tape language whose automata track the parity of the current run of 1s, a window near the head, and the phase of the periodic block from the right end. Windows of up to 11 cells with run-length parity alone fail, because they lose the block's phase at the right end.

## First look

Growth class **sqrt/sqrt** (left: sqrt, exponent 0.496; right: sqrt,
exponent 0.496). After 1,000,000,000 steps: 58,449 cells visited (10,724 left of the
start, 32,176 right), 43,788 ones.

- left, step 970,421,129: `D>0 1 0 1^7 0 1 0 1 0 1^13 0 1^7 0 1^3 0 1^7 0 1^13 0 1 0 1 0 1^7 0 1^3 0 1 0 1 0 1 0 1^3 0 1^7 0 1 0 1^5 0 1 0 1 0 1^5 0 1^3 0 1 0 1 0 1^5 0 1^3 0 1 0 1^3 0 1^3 0 1^3 0 1^5 0 1^3 0 1 0 1 0 1^3 0 1 0 1^5 0 1 0 1 0 1^5 0 1^3 0 1 0 1 0 1 0 1^11 0 1 0 1 0 1^9 0 1^5 0 1^5 0 1 0 1 0 1 0 1^3 0 1 0 1 0 1^3`
- left, step 986,046,186: `D>0 1^3 0 1 0 1 0 1^3 0 1^3 0 1^11 0 1^3 0 1 0 1^7 0 1 0 1^7 0 1 0 1 0 1 0 1 0 1^3 0 1^5 0 1^3 0 1^5 0 1^3 0 1 0 1 0 1 0 1 0 1^5 0 1^19 0 1^5 0 1^5 0 1 0 1^9 0 1^3 0 1^9 0 1 0 1^7 0 1 0 1 0 1 0 1^7 0 1^3 0 1^5 0 1^5 0 1 0 1^5 0 1^3 0 1 0 1 0 1 0 1 0 1 0 1^3 0 1 0 1^3 0 1^3 0 1 0 1^5 0 1 0 1^3 0 1^3 `
- right, step 970,499,349: `0 1^3 0 1^5 0 1^5 0 1 0 1 0 1 0 1 0 1 0 1^3 0 1^5 0 1 0 1^3 0 1^5 0 1 0 1 0 1 0 1 0 1 0 1 0 1^7 0 1^5 0 1 0 1^9 0 1^3 0 1^5 0 1^3 0 1^3 0 1 0 1^3 0 1^3 0 1^3 0 1 0 1^3 0 1^3 0 1^3 0 1 0 1 0 1^3 0 1 0 1 0 1^3 0 1^3 0 1^3 0 1 0 1^3 0 1 0 1^3 0 1^3 0 1 0 1^3 0 1^3 0 1^3 0 1 0 1^5 0 1 0 1 0 1 0 1 0 1^7 `
- right, step 986,124,474: `0 1 0 1^7 0 1 0 1 0 1^3 0 1^9 0 1 0 1^5 0 1 0 1 0 1^5 0 1 0 1 0 1^11 0 1 0 1 0 1 0 1^3 0 1 0 1 0 1 0 1^3 0 1 0 1^9 0 1 0 1^3 0 1^17 0 1 0 1 0 1^3 0 1^3 0 1 0 1 0 1 0 1 0 1 0 1^3 0 1 0 1 0 1 0 1 0 1 0 1^5 0 1 0 1 0 1^9 0 1 0 1 0 1^3 0 1 0 1 0 1 0 1^3 0 1^3 0 1 0 1 0 1 0 1^3 0 1 0 1^11 0 1 0 1^3 0 1 0`

## Deciders tried (F11, 13 November 2026)

None closes. Each reaches a halting configuration in its abstraction, which says nothing about halting.

- n-gram CPS (`tools/c/ngramcps.c`), equal widths on both sides: a halting local configuration is reached with plain up to width 24, history 1 up to width 24, history 2 up to width 24, history 3 up to width 24, LRU history up to width 8 (larger widths ran out of the 150 s or 60 million configuration budget).
- n-gram CPS with every cell tagged by its position mod p: fails for p = 2 up to width 20, p = 3 up to width 20, p = 4 up to width 20, p = 6 up to width 20.
- n-gram CPS where each side also carries the state of a small automaton that has read that side from the far end (every automaton with up to 3 states on both sides, or 4 states on one side), with position mod 1..4 and widths 4, 6, 8: no closed set without a halt in all 120 parameter sets.
- Run-length windows (the K nearest runs of equal macro cells on each side, run lengths kept exactly below T and mod M above): fails for all 72 parameter sets (cells of 1 to 4 bits, K = 2, 4, 6, T = 2, 4, M = 1, 2, 4).
- Two-automaton closed tape language by SAT (a deterministic automaton reading each side inward, n states each, CaDiCaL): no solution for n = 2..10; n = 11 not finished in 150 s.

## Where a halt can come from

`lean/Route.lean` (kernel, written by `py/route.py`): `halt_route`, two steps before any halt the machine is in one
of: A with 1 under the head, 0 right, 0 two right; B with 1 under the head, 0 right, 0 two right.

## Pages

- [`pages/holdouts/1RB0RE_1RC1RE_1LD1LC_0RB0LC_1RF0RB_---1RA/explainer.html`](../../pages/holdouts/1RB0RE_1RC1RE_1LD1LC_0RB0LC_1RF0RB_---1RA/explainer.html)
- [`pages/holdouts/1RB0RE_1RC1RE_1LD1LC_0RB0LC_1RF0RB_---1RA/proof-status.html`](../../pages/holdouts/1RB0RE_1RC1RE_1LD1LC_0RB0LC_1RF0RB_---1RA/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RE_1RC1RE_1LD1LC_0RB0LC_1RF0RB_---1RA/lean/check.sh
python3 holdouts/1RB0RE_1RC1RE_1LD1LC_0RB0LC_1RF0RB_---1RA/py/rules.py | diff - holdouts/1RB0RE_1RC1RE_1LD1LC_0RB0LC_1RF0RB_---1RA/lean/Rules.lean
```
