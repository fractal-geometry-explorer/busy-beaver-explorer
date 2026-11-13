# 1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RB---

bbchallenge id 40361. Halting from blank tape is open. **The machine is a ternary counter, and halting is proved
(Lean, kernel, no hypothesis) to be equivalent to an explicit counter model reaching one pattern.**

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RF |
| B | 1LC | 0RE |
| C | 1RD | 0LC |
| D | 0LB | 0RA |
| E | 1LD | 1RD |
| F | 1RB | --- |

## What it does

Write `x = 1110` and `a = 10`. Whenever the head, in C, is at the left end of the tape (blank to the left), the tape
is a **counter configuration**

    C> 0 10 x^n0 [1 a^d1 x^n1] [1 a^d2 x^n2] ... [1 a^dk x^nk] 1 0^∞          state (n0; (d1,n1), ..., (dk,nk))

with ternary digits `d_i ∈ {0,1,2}` (least significant first). Consecutive visits from step 2,297:

    (2; (2,10), (2,1), (2,0))   (3; (1,10), (2,1), (2,0))   (4; (0,10), (2,1), (2,0))   (5; (2,9), (1,1), (2,0)) ...

**One bounce is a ternary decrement.** C sweeps right, turning the `x` of the first block and of each group with
digit 0 into pairs `a`, removes one `a` at the first nonzero digit, and the head zig-zags back left (each zig-zag eats
`a a` on its left and leaves an `x` on its right):

    C> 0 10 x^n0 [1 x^(m1+1)] ... [1 x^(mj+1)] [1 a^(e+1) x^n] rest  →  C> 0 10 x^(n0+1) [1 a^2 x^m1] ... [1 a^2 x^mj] [1 a^e x^n] rest

The first nonzero digit drops by one, the zeros below it become 2, every group passed loses one `x`, the first block
gains one.

**Rounds.** A round starts with every digit 2 (value 3^m − 1 for m groups) and counts down; group i is passed
3^(m−i) − 1 times. When every digit is 0 the borrow runs off the right end, the head converts the tape back
(`exhaust`), and the next round starts as `(0; (1,n0+1), (0,n1), ..., (0,n_k − 1), (0,0))`; two bounces later all
digits are 2 again with one more group. With the blocks `c_1..c_m` at the start of a round, while nothing runs out:

    (c1, ..., cm)  →  (3^m + 1, c1 − 3^(m−1), c2 − 3^(m−2), ..., c(m−1) − 3, cm − 2)

This is the "geometric decrements" of the plain run: at the right end, the blocks of pairs `10` (two per `x`) lose
4, 6, 18, 54, 162, ... per round and the front block is 5 + 2·3^m (1463, 4379, 13127, ...).

**Running out and merges.** An exhausted block becomes `(2,0)`, `(1,0)`, `(0,0)` (just `1`). An empty group followed
by a group with digit 1 reads `1 · 1 10 = 1110`: one more `x`, so both join the block before them (an identity of
tapes). Empty groups at the right end act as extra digits: one `(0,0)` is used up (`D`), two stay (an endless supply
of borrows, the "A phase", until the last group runs out), three become `(1,0)` (`F`).

**Halting.** F reads 1 exactly when the borrow meets an empty group `(0,0)` followed by a nonempty group with digit
0 (the head then reads `1 1 1 1`), or by `(0,0), (0, n+1)`, or by two more empty groups and anything else (four
empty groups at the end).

**The cases that do not occur in the run** (proved all the same, so that the model is total):
- every digit `e + 1 >= 1` is decremented the same way (not only 1 and 2);
- a round ending with no group: `(n0; ) -> (0; (1,n0), (0,0))`;
- the borrow meeting one or two empty groups and then a group with digit `e + 2`: the machine turns round there as
  at the end of a round, `(n0; Z, (0,0), (e+2,n), rest) -> (0; (1,n0+1), Z, (0,0), (e,n), rest)` (`Z` the passed
  groups, unchanged; the same with `(0,0), (0,0)`). With digit 2 this leaves `(0,0), (0,n)`: a halt two bounces
  later if `n >= 1`;
- `(0,0), (1,n)` and `(0,0), (0,0), (1,n)` are other spellings of one more `x` / of the group `(0, n+1)`: the model
  first reads the list the way the borrow sees it (`norm`, an equality of tapes).

## What is proved (Lean, kernel; `lean/check.sh` prints ALL CHECKED, no `sorry`)

- `lean/Counter.lean`: `bounce_gen` (one bounce = one decrement, for every n0, every list of passed groups and any
  tape after), `bounce_t1`/`bounce_t2`/`bounce_t3` (empty groups at the end), `exhaust` (end of a round, for any
  number of groups), `merge_mid`/`merge_first` (merges as tape identities), `bounce_halt`. The pieces are generated
  by `py/counter.py` (bbtools.symtm); the inductions over the groups are by hand.
- `lean/Counter2.lean` (12 November): `bounce_any` (the decrement for every digit), `exhaust0`, `mid1`, `mid2` (the
  cases above).
- `lean/Model.lean`: `bounceM`, the counter model as a function on every state; `bounceM_ne_stuck` (it always
  answers `next` or `halt`), `bounceM_next` (a `next` is a run of >= 1 machine steps), `bounceM_halt` (a `halt` is a
  halting configuration); `blank_to_counter` (blank tape reaches `(0; (1,5), (0,0))` at step 403); and

      theorem halts_iff_model :
          HaltsFromBlank ↔ ∃ k, runM k (.next 0 [(1, 5), (0, 0)]) = .halt

  In words: the machine halts from blank tape iff iterating the model's bounce from `(0; (1,5), (0,0))` reaches
  `halt`. Nothing is assumed (axioms: propext, Classical.choice, Quot.sound). The earlier version had the hypothesis
  "the model never gets stuck"; it is gone.
- `lean/Rules.lean` (sweep rules), `lean/Blank.lean` (halting configurations; no halt in 10^4 / 10^7 steps).

## Evidence (computation)

- `c/cdump.c` reads the counter off the real machine at every bounce; `py/model.py check` confirms the model at all
  87,809 bounces up to step 4·10^9 (trusted).
- `py/model.py random 3000`: one bounce of the model against the machine itself on 3,000 random states, all cases.
- `py/model.py far` (exact integers, many bounces per jump; the jumps are checked against single bounces): 332,875
  rounds, about 10^292 bounces, without a halt or a stuck state (880 s). The list grows to 608 groups. A phases started only
  at rounds 23 and 49,668.

## Why it has not halted (heuristic)

- In the run, consecutive groups satisfy `n_i ≡ d_(i+1) + 2 (mod 3)` (all of the first 300,000 bounces except 9
  states right after the F event). So when a block runs out, the next digit is 1 and the groups merge: the halting
  pattern cannot form in the middle of the list.
- Counting groups from the right end, per round group p loses 3^(p−1) (the last loses 2), so the differences
  `n_(p+1) − 3 n_p` (p ≥ 2) are conserved between merges. A halt needs the group before the last to be exactly empty
  when the last group runs out during an A phase: one conserved difference equal to one small value at a rare
  moment. Open, Collatz-like.

## For later

- Deciding the model. A halt in the middle of the list needs an empty group in front of a digit 0 or 2; the mod-3
  pattern `n_i ≡ d_(i+1) + 2` excludes it, and is preserved by decrements, merges and the end of a round for all
  pairs except the last two groups (the tail: after `D` the last pair is off by one, after `F` too). A proof needs
  the pattern stated with the tail as a separate small state machine (`D`, `A`, `F`), and then an argument about
  sizes for the A phases: the exact condition on the last groups at the start of an A phase under which it ends in
  a halt.

## Reproduce

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RB---/lean/check.sh
gcc -O2 -o cdump holdouts/1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RB---/c/cdump.c && ./cdump 4000000000 1 > m1c.txt
python3 holdouts/1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RB---/py/model.py check m1c.txt
python3 holdouts/1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RB---/py/model.py random 3000
python3 holdouts/1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RB---/py/model.py far 880
python3 holdouts/1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RB---/py/counter.py      # the symbolic pieces of Counter.lean
```

## Pages

- [`pages/holdouts/1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RB---/explainer.html`](../../pages/holdouts/1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RB---/explainer.html)
- [`pages/holdouts/1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RB---/proof-status.html`](../../pages/holdouts/1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RB---/proof-status.html)
