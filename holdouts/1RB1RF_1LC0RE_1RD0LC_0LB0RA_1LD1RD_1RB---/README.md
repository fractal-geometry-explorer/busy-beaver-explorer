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
- `lean/Charge.lean` (13 November): `good_not_halt`, a list in which every pair is neutral (see "Charged pairs"
  below) does not halt at the next bounce.
- `lean/Rules.lean` (sweep rules), `lean/Blank.lean` (halting configurations; no halt in 10^4 / 10^7 steps).

## Evidence (computation)

- `c/cdump.c` reads the counter off the real machine at every bounce; `py/model.py check` confirms the model at all
  87,809 bounces up to step 4·10^9 (trusted).
- `py/model.py random 3000`: one bounce of the model against the machine itself on 3,000 random states, all cases.
- `py/model.py far` (exact integers, many bounces per jump; the jumps are checked against single bounces): 332,875
  rounds, about 10^292 bounces, without a halt or a stuck state (880 s). The list grows to 608 groups. A phases started only
  at rounds 23 and 49,668.

## Charged pairs: what a halt needs (13 November)

Call two neighbouring groups `(d, n), (d', n')` **neutral** when `n ≡ d' + 2 (mod 3)` and **charged** otherwise
(residue `n − d' − 2 mod 3` equal to 1 or 2).

- **A halt needs a charged pair (Lean, kernel).** In a neutral pair an empty group is followed by a digit 1, and the
  two merge. Every halting pattern starts with an empty group followed by a digit 0. `lean/Charge.lean`,
  `good_not_halt`: if every pair of the list is neutral, the next bounce is not a halt, for every `n0`. The pairs
  behind the empty groups that the end-of-round events leave at the very end of the list (`[X, (0,0)]`,
  `[X, (1,0)]`, `[X, (0,0), (0,0)]`) are exempt: this is the "tail" of the earlier notes, and it turns out to need
  no size argument.
- **Where a charge comes from (checked on all small states, not proved).** A decrement changes `n` and `d'` of
  every pair by the same amount mod 3, and when a group runs out in a neutral pair the merge leaves the residues
  of the pairs around it as they were, so a charge stays on its block. The only new pair is made at the end of a round, `(1, n0+1), (0, m1+1)`, and it
  is neutral exactly when `n0 ≡ 1 (mod 3)`. `n0 + d1 ≡ 1 (mod 3)` holds from the start and is kept by every
  bounce except one in which the first group runs out and merges into the front block. `py/charge.py exhaust`
  checks all three statements on every good list of up to 6 groups with digits < 3 and blocks < 5 (230,592 states).
- **In the run (observed, `py/charge.py run 50000`).** The first group runs out in rounds 22, 183 and 49,668.
  The first two leave `n0` right by the end of the round. Round 49,668 is the second "A phase": the last group
  runs out at the end of a round, two empty groups stay at the end and supply borrows without end, and the counter
  wraps round millions of times while the groups at the right end are used up one after the other. In those wraps the
  whole front of the list runs out, and round 49,669 starts with a **charged pair of residue 1**. It has been there ever since (seen to
  round 255,000, `py/charge.py run 255000`, 9 minutes): the charge sits on one block of about 1.3·10^113 copies of `x`, 214th from the right end.
- **What the charge means.** If the charged block runs out while the group after it is nonempty, the borrow finds an
  empty group followed by a digit 0, which is the first halting pattern. So **the model halts if that block ever
  runs out before its right neighbour does** (read off the definition of the model; for residue 2 the turn `M1`
  comes first and the halt two bounces later).
- **Why it has not happened, and will not soon (heuristic).** A group with p − 1 groups to its right loses
  3^(p−1) per round (the last group 2). At that rate the charged block lasts 3·10^11 rounds and its right neighbour
  1.9·10^11 (the table printed by `py/charge.py run`), so the neighbour would go first, and a group that runs out
  in a neutral pair merges the group after it into the group before it, here into the charged block. The charged
  block is also fed from the left: the young groups born at the front run out sooner (the three to its left would last 10^7 rounds at
  round 255,000) and the last of them merge into it. The first event among the 213 groups to its right is due about 1.9·10^7 rounds
  later, when the second group from the right end (5.7·10^7, losing 3 per round) runs out. A round costs 3^m bounces
  with m > 200 groups, and `py/charge.py` does about 400 rounds a second; the round-skipping simulator of the next
  section follows it further.

So the earlier guess, that a halt would have to come from the tail during an A phase, was wrong: the tail is
harmless, and the A phases matter because their wraps empty the front of the list and can leave a charge there.

## Round-skipping run to round 33,199,619 (13 November, trusted)

`py/skip.py` keeps the state at the start of each round. Between events the group with q groups to its right
loses exactly 3^q per round (the last group 2), so the groups at the right end are stored as "size at some round"
and never touched; only the young groups at the front are run bounce by bounce, against a single counter that
stands for all the groups behind them. When a group is about to run out, or anything other than a plain decrement
happens, the round is done by the exact model (`py/model.py`). A halt is only ever reported by the exact model.

- **Test.** `py/skip.py test 60000` compares every round start with the exact model from the first round to round
  60,000 (59,997 agree, none differ; 58 rounds were handed to the exact model, among them the A phase of round
  49,668). The same from saved exact states at rounds 49,660 and 100,000, 3,000 rounds each.
- **Run (observed).** No halt up to round 33,199,619 (about 2.5 hours in all). The one event behind the front:
  in round 19,080,842 the second group from the right end ran out, as forecast, and the last three groups merged
  into one. This was not an A phase and it made no new charge. There is still exactly one charged pair, residue 1,
  now 212th from the right end instead of 214th.
- **What the event did to the race.** With two groups fewer on its right, the charged block and its neighbour
  both lose 9 times less per round. At round 33,199,619 the charged block (114 digits) would last 2.7·10^12 more
  rounds and its right neighbour 1.7·10^12, so the neighbour would still go first. The eight groups at the right
  end have between 1.0·10^8 and 5.5·10^8 rounds left at their present rates, so events of this kind recur about
  every 10^8 rounds, and each one that removes groups stretches the lifetimes again. On this one observation the
  charged block's remaining life grows faster than the round count; nothing about that is proved.
- **Speed.** The front that has to be simulated grows like the square root of the round count (6,034 groups at
  the end), so the cost grows like rounds^1.5: 5·10^6 rounds took 8 minutes, 3.3·10^7 took 2.5 hours. Reaching
  10^9 rounds needs the front in closed form as well.

## For later

- `good` is preserved by every bounce as long as `n0 + d1 ≡ 1`, and that relation only breaks at a first-group
  merge: both are checked exhaustively on small states but not proved. A Lean proof needs an induction through
  `norm` with the passed groups; it would give "a halt needs an earlier bounce in which the first group ran out".
- The front in closed form. `py/skip.py` skips the groups at the right end but still simulates the young groups
  bounce by bounce; a closed form for their cycle (a new first group, the one before it left with 2 and merged)
  would take the run to the 10^8 to 10^12 rounds on which the charged block's fate (and the charges of later A
  phases) is decided.

## Reproduce

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RB---/lean/check.sh
gcc -O2 -o cdump holdouts/1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RB---/c/cdump.c && ./cdump 4000000000 1 > m1c.txt
python3 holdouts/1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RB---/py/model.py check m1c.txt
python3 holdouts/1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RB---/py/model.py random 3000
python3 holdouts/1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RB---/py/model.py far 880
python3 holdouts/1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RB---/py/counter.py      # the symbolic pieces of Counter.lean
python3 holdouts/1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RB---/py/charge.py exhaust   # neutral lists: no halt, and where a charge can be made
python3 holdouts/1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RB---/py/charge.py run 50000 # the charge made in round 49,668 (40 s)
python3 holdouts/1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RB---/py/skip.py test 60000    # round skipping against the exact model (45 s)
python3 holdouts/1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RB---/py/skip.py run 33200000 # the event of round 19,080,842 (about 2.5 hours)
```

## Pages

- [`pages/holdouts/1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RB---/explainer.html`](../../pages/holdouts/1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RB---/explainer.html)
- [`pages/holdouts/1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RB---/proof-status.html`](../../pages/holdouts/1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RB---/proof-status.html)
