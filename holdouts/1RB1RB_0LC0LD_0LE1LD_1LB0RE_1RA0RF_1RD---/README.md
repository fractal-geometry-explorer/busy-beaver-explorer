# 1RB1RB_0LC0LD_0LE1LD_1LB0RE_1RA0RF_1RD---

bbchallenge id 181063. One of the six-state holdouts whose halting from blank tape is open (group G07, family:
**exponential bouncer with an inner counter**, epochs with T' = 2T + 5).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RB |
| B | 0LC | 0LD |
| C | 0LE | 1LD |
| D | 1LB | 0RE |
| E | 1RA | 0RF |
| F | 1RD | --- |

## Status

**Open.** The run is understood as a sequence of epochs with exact formulas (checked on nine epochs, 5.16·10^10
steps, no halt). Phases 1, 2 and 5 of the five phases of an epoch are proved in Lean for every size (`lean/Phases.lean`, kernel),
and the run from blank tape into the first epoch is proved (`lean/Start.lean`, native_decide). Phases 3 and 4, where
an inner counter runs deep inside the tape, are long exact cycles (144 and 288 visits) that are checked for every
value of the counts by exact symbolic simulation (`py/cycles.py`), but not in Lean; they, and the short transitions
between the phases, are the gap between this and a proof of non-halting.

## Where it can halt

F is entered only by E reading 1 (0RF). E is entered by C reading 0 (0LE: the head moves left, and F then reads the
0 that C just wrote, so no halt) or by D reading 1 (0RE). So **the machine halts exactly when D reads a 1 followed by
two more 1s** (`D> 1 1 1`). Runs of three 1s do appear right next to the head (171,801,958 times in the first 10^9
steps), so no small local invariant excludes the halt (the K-window CTL of `bbtools.ctl` finds spurious halts for
K = 3..8 and no closed set within its round limit for K = 10..14).

## What it does

Write the tape with `a = 10`, `b = 100`, `c = 1000`. A *visit* is a moment when the head, in state D, steps onto a
new cell at the right end (the left end stopped at 37 cells left of the start; the tape grows by 3 cells per visit).
Between visits the head goes left to some point, changes a few cells there and comes back.

### Epochs

An **epoch** starts at a visit where the tape ends in

    ... M (aaacacac)^T aaa cacb (aacaacac)^3 aacaac (baccaaa)^X bab aaa caacaac 1 D>        X = 6T + 17

(this is `P1 X 0` of `lean/Phases.lean`; M is a fixed word, `(c)^5 bacacaacacaacbacb`). `c/epochs.c` finds, by plain
simulation (`./epochs 60000000000`):

| epoch | visit | step | T | X |
|---|---|---|---|---|
| 0 | 733 | 638,914 | 7 | 59 |
| 1 | 1,527 | 2,791,601 | 19 | 131 |
| 2 | 3,185 | 11,869,478 | 43 | 275 |
| 3 | 6,571 | 49,048,755 | 91 | 563 |
| 4 | 13,413 | 199,088,630 | 187 | 1,139 |
| 5 | 27,167 | 801,808,537 | 379 | 2,291 |
| 6 | 54,745 | 3,217,627,644 | 763 | 4,595 |
| 7 | 109,971 | 12,890,601,695 | 1,531 | 9,203 |
| 8 | 220,493 | 51,601,711,810 | 3,067 | 18,419 |

Exactly: **T' = 2T + 5** (T = 3·2^k − 5), X = 6T + 17, an epoch takes **72T + 290 visits** (all eight measured
epochs), and from T = 91 on exactly **16416T² + 151769T + 288000 steps** (T = 91 ... 1531; the first epochs differ
slightly because the deepest visits reach the irregular start of the tape). So each epoch is about four times longer
than the last, and the tape grows like the square root of the step count.

Each epoch leaves behind a block that is never changed again, and adds one word to the block of the epoch before:

    (acacaaac)^(T-10) (ac)^36 (bac)^(6T-3) cc (a)^17 cacb (ac)^3 babac (cba)^3 cacacbacb (ac)^3 bacbacaca
    (bac)^7 acacbacb (ac)^3 (bac)^5 aca U^n (c)^13 ...        U = (c)^7 (bac)^5 acacbacb (ac)^3 (bac)^5 aca

with n = (T − 43)/6 copies of U (0, 8, 24, 56, 120, 248 for T = 43 ... 1531), and n + 1 after the next epoch.
(Read from the epoch-start tapes; `(bac)^(6T-3)` is 255, 543, 1119, 2271, 4575, 9183 and `(acacaaac)^(T-10)` is 33,
81, ..., 1521.)

### The five phases of an epoch (epoch 3, T = 91, visits 6,571 to 13,413)

1. **X visits.** `(baccaaa)^X` is used up from its right end: each visit turns one copy into one `aaaaca` and one
   `caa`. The tape goes from `P1 X 0` to `P1 0 X`, where
   `P1 n m = L (baccaaa)^n ba 1 00 (aaaaca)^m aaa (caa)^(m+2) c 1 D>`. **Proved** (below).
2. **About X visits**, after a few transitional visits that run deep: each visit turns one `aaaaac` into one more
   `bac` on its left and one more `caa` on its right; this builds `(bac)^(6T-3)`:
   `P2 p q r = L (bac)^p 1 00 acccb (aaaaac)^q aaaa (caa)^r c 1 D>` goes to `P2 (p+q) 0 (r+q)`. **Proved**.
3. At the right end `aac` is turned into `aaacac`, one copy every two visits, and
4. then `aaacac` into `aaaac`, two copies every four visits. In phases 3 and 4 **every second visit runs deep** into
   the tape, to the region of irregular words between `(bac)^(6T-3)` and the growing `(aaacacac)^q`: this region is an
   inner counter. The depths of the deep visits follow a ruler-like pattern (one in three goes to a point that moves
   by 11 cells per six visits, the others deeper and deeper, as carries in a counter), and the counter's words
   change at every step (e.g. at visit 8,000: `(bac)^545 b (a)^6 c (a)^8 cac (acb)^3 (ac)^3 ba (c)^5 b (a)^11
   cacacbacb (ac)^5 (bac)^8 (a)^11 cac (acb)^4 a (c)^4 (a)^3 cbaca (ac)^3 aacaca1`). At the end of phase 4 the old
   `(aaacacac)^T` has become `(acacaaac)^(T-10)` of the frozen block, the counter region has become its unit copies,
   and a new `(aaacacac)^(2T+5)` stands right of it.

   Both phases are, after a start-up stretch, **exact cycles**: with `U` as above,

   | phase | cycle | changes per cycle | steps per cycle |
   |---|---|---|---|
   | 3 | 144 visits | U +1, `(acacaaac)` +12, `(acaaac)` +72, `(aac)` −144 | 5616p + 8064q + 4032r + const |
   | 4 | 288 visits | U +1, `(acaaacac)` +12, `(acaaac)` −72, `(acaaa)` +144 | 5616p + 8064q + 5760r + const |

   `py/cycles.py` takes a tape of each cycle from the run (epoch 4, visits 17,264 and 18,500), makes every long
   count a variable and the tape left of `(bac)^(6T-3)` an unknown context, runs the 144 (288) visits with
   `bbtools.symtm` (exact symbolic simulation with shift rules, re-bracketing between visits by `py/tapeeq.py`) and
   checks that the end is the start with the counts moved as in the table, for every value of the counts. Inside a
   cycle the deep visits follow the counter's ruler pattern; the cycle closes when one more copy of U is complete.
5. **Two visits per copy.** `(aaaac)^j` is turned back into `baccaaa`, one copy per two visits:
   `P5 k j = L (baccaaa)^k ccb (aaaac)^(j+2) aaa 1 00 aac 1 D>` goes to `P5 (k+j) 0`. **Proved** (below). A few
   finite visits then give the next epoch start with X' = 6(2T + 5) + 17.

## What is proved

* `lean/Blank.lean` (kernel / native_decide): the halting configurations; no halt in 10^4 / 10^7 steps.
* `lean/Shifts.lean` (kernel): three shift rules for runs of `10` and `01`.
* `lean/Phases.lean` (kernel, written by `py/phases.py` from `bbtools.symtm` traces):
  * `p1_visit`: `P1 (n+1) m L` reaches `P1 n (m+1) L` in 74m + 167 steps, for all n, m, L;
  * `p2_visit`: `P2 p (q+1) r L` reaches `P2 (p+1) q (r+1) L` in 46q + 28r + 127 steps;
  * `p5_cycle`: `P5 k (j+1) L` reaches `P5 (k+1) j L` in two visits and 40j + 253 steps, for all k, j, L;
  * `iterate`, `phase1` (`P1 n 0` reaches `P1 0 n`), `phase2` (`P2 p q r` reaches `P2 (p+q) 0 (r+q)`), `phase5`
    (`P5 k j` reaches `P5 (k+j) 0`).
  The end tape of a symbolic run is re-bracketed into the start form by `py/tapeeq.py`, which writes the equation as a
  chain of `TM.rep_rotate`, `TM.rep_succ` and `TM.rep_add` instances (literal cells moved toward the head past a
  repeat while they match its first cell, then absorbed and merged).
* `lean/Start.lean` (native_decide): after 638,914 steps from blank tape the configuration is `P1 59 0 L0`
  (`blank_to_epoch0`), so with `phase1` the machine reaches `P1 0 59 L0` (`blank_to_phase1_end`).
* Trusted (exact symbolic computation, `py/cycles.py`): the 144- and 288-visit cycles of phases 3 and 4, for all
  counts.
* Trusted (C, plain simulation, `c/epochs.c`): no halt in 6·10^10 steps; the epoch table above.

## The gap, and next steps

An epoch is now: phase 1 (proved) · a transition · phase 2 (proved) · a transition and a start-up stretch of phase 3
(where the words between `(bac)^(6T-3)` and the first copies of U are written) · k3 cycles of 144 visits · a
transition · k4 cycles of 288 visits · a transition · phase 5 (proved) · a few visits to the next epoch start. To
turn this into a proof that the machine never halts:

1. **Lean for the long cycles.** The symtm proofs state the whole configuration at every segment, so 144 visits
   come to hundreds of megabytes of Lean. Two ways out: state each visit with the part of the tape it does not touch
   as a context (most visits touch only the last few dozen cells, the deep ones a few hundred), or write a symbolic
   executor in Lean (run-length tapes with linear counts, proved sound) and check the cycles with `native_decide`.
2. **The transitions**, as symbolic runs from the end of one regime to the start of the next with the counts
   written in T (for example T = 6s + 1, with (T − 43)/6 copies of U), found with the same machinery.
3. **Cycle counts.** k3 and k4 must be linear in T; that needs T in a fixed residue class modulo the cycles'
   periods in the counts (T = 3·2^k − 5 is ≡ −5 modulo 2^j for k ≥ j, and alternates between 1 and 7 modulo 9),
   so expect two kinds of epoch (k even, k odd) and an epoch theorem for each.
4. **The induction** over epochs: `E(T, n, L)` (the epoch start, n copies of U in the previous block) reaches
   `E(2T + 5, (T − 43)/6, L')` for every T of its class from some T0 on; the epochs before T0 by the same rules
   with concrete counts or by `native_decide` (epoch 4 starts at step 199,088,630).

## Second look (earlier pass)

The earlier pass found the doubling exponents ((acb)^B with B' = 2B + 33, (aaacacac)^C with C' = 2C + 5) and the
phases; the third pass made them exact (the table above) and proved phases 1 and 5.

## First look

Growth class **fixed/sqrt** (left: fixed, exponent 0.0; right: sqrt,
exponent 0.499). After 1,000,000,000 steps: 97,518 cells visited (37 left of the
start, 62,618 right), 40,211 ones.

- right, step 970,266,379: `0^2 1 0 1 0 1 0 1 0 1 0 1 0 1 0^3 1 0^2 1 0 1 0^3 1 0 1 0^3 1 0^2 1 0 1 0 1 0^3 1 0^3 1 0^3 1 0 1 0 1 0 1 0^3 1 0^3 1 0^2 1 0 1 0 1 0 1 0 1 0^3 1 0^3 1 0^2 1 0 1 0^3 1 0 1 0 1 0 1 0 1 0 1 0 1 0^3 1 0 1 0^3 1 0 1 0 1 0 1 0 1 0 1 0 1 0^3 1 0^3 1 0 1 0 1 0 1 0^3 1 0^3 1 0 1 0 1 0 1 0^3 1 0^3 1 0 1 0 1 `
- right, step 985,930,618: `0^2 1 0 1 0 1 0 1 0 1 0 1 0 1 0^3 1 0^2 1 0 1 0^3 1 0 1 0^3 1 0^2 1 0 1 0 1 0^3 1 0^3 1 0^3 1 0 1 0 1 0 1 0^3 1 0^3 1 0^2 1 0 1 0 1 0 1 0 1 0^3 1 0^3 1 0^2 1 0 1 0^3 1 0 1 0 1 0 1 0 1 0 1 0 1 0^3 1 0 1 0^3 1 0 1 0 1 0 1 0 1 0 1 0 1 0^3 1 0^3 1 0 1 0 1 0 1 0^3 1 0^3 1 0 1 0 1 0 1 0^3 1 0^3 1 0 1 0 1 `

## Pages

- [`pages/holdouts/1RB1RB_0LC0LD_0LE1LD_1LB0RE_1RA0RF_1RD---/explainer.html`](../../pages/holdouts/1RB1RB_0LC0LD_0LE1LD_1LB0RE_1RA0RF_1RD---/explainer.html)
- [`pages/holdouts/1RB1RB_0LC0LD_0LE1LD_1LB0RE_1RA0RF_1RD---/proof-status.html`](../../pages/holdouts/1RB1RB_0LC0LD_0LE1LD_1LB0RE_1RA0RF_1RD---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RB_0LC0LD_0LE1LD_1LB0RE_1RA0RF_1RD---/lean/check.sh
python3 holdouts/1RB1RB_0LC0LD_0LE1LD_1LB0RE_1RA0RF_1RD---/py/phases.py | diff - holdouts/1RB1RB_0LC0LD_0LE1LD_1LB0RE_1RA0RF_1RD---/lean/Phases.lean
python3 holdouts/1RB1RB_0LC0LD_0LE1LD_1LB0RE_1RA0RF_1RD---/py/start.py | diff - holdouts/1RB1RB_0LC0LD_0LE1LD_1LB0RE_1RA0RF_1RD---/lean/Start.lean
python3 holdouts/1RB1RB_0LC0LD_0LE1LD_1LB0RE_1RA0RF_1RD---/py/cycles.py                      # the phase 3 and 4 cycles
gcc -O2 -o epochs holdouts/1RB1RB_0LC0LD_0LE1LD_1LB0RE_1RA0RF_1RD---/c/epochs.c && ./epochs 60000000000      # about 4 minutes
```
