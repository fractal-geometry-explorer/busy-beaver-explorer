# 1RB1LA_0LC0RE_1LD1LB_1RE1LF_1RC0RA_0RC---

bbchallenge id 159355. One of the six-state holdouts. **A base-4 counter of walls in a sea of `100`**, incremented
from the right end; walls drift, merge and are born. Analyzed by hand (group G02, two passes): the sample-to-sample
rules are worked out exactly and the main ones, including the overflow, are proved in Lean for carry chains of any
length. Whether it halts is still open.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LA |
| B | 0LC | 0RE |
| C | 1LD | 1LB |
| D | 1RE | 1LF |
| E | 1RC | 0RA |
| F | 0RC | --- |

## What it does

**Sample point**: C on a 0 at the right end of the tape (not the left end, as in the first pass). There the tape is

    0^inf  (100)^r1 W1  (100)^r2 W2  ...  (100)^rk Wk  (100)^last  1 0 1 C>0  0^inf

a list of *digits* `(100)^r W` (a run of r words `100`, then a wall W), then the last run. The walls:

| wall | cells | role |
|---|---|---|
| S0 | `1000` | digit 0 |
| S1 | `110` | digit 1 |
| S2 | `10000` | digit 2 |
| S3 | `1010` | digit 3 |
| S | `10` | the `10` at the left end, and the left wall of some mergers |

Example (step 1,999,995,206): `[0]S [14]S1 [490]S0 [922]S1 [1642]S0 [427]S0 [5933]S2 [15297]S0 [4360]`.

**One sweep = add one.** From the right end the head walks left across the *carry chain* (the S3 digits next to
the end), changes the first other digit (the *stop*) and walks back, turning every S3 of the chain into S0; the
last run grows by one. The head goes no further left than the stop. In digit form (`lean/Sweeps.lean`, any chain
length, runs unchanged unless shown):

| rule | stop before | stop after |
|---|---|---|
| `sweep_s0` | `[a+1]S0` | `[a+1]S1` |
| `sweep_s1` | `[a+1]S1` | `[a]S2` |
| `sweep_s2` | `[a+1]S2` | `[a+1]S3` |

So each digit cycles S0 → S1 → S2 → S3 → S0 (with a carry): a base-4 counter, lowest digit next to the head. **A
digit's left run shrinks by 1 per cycle** (at its S1→S2 step) and nothing else changes it; the last run grows by
one per sweep (the √t side). The first pass's observation — at each visit of the left end block i has lost 4^(i−1) — is this rule seen
from the left: between two overflows the i-th digit from the left goes round its cycle 4^(i−1) times, and its
left run (block i) loses 1 each time.

**Edge events** (each a symbolic run of the machine; all starred ones are Lean theorems for any carry chain):

- *Overflow* (`overflow`\*): `0^inf 10` followed only by S3 digits: the head crosses the whole tape, every S3
  becomes S0 (runs unchanged) and a new digit S1 is born at the right end, with the old last run as its left run
  and a new last run of 1. These are the first pass's visits of the left end. Example, step 3,364,427,683:
  `[0]S [13]S0 [487]S0 [910]S0 [1595]S0 [239]S0 [5182]S0 [12291]S0 [16383]S1 [1]`.
- *Merger* (a run used up): an S1 with left run 0 receiving a carry cannot shorten it. After S = `10`
  (`merge_s_s1`\*) the two become one S0 (one digit fewer); after S3 (`merge_s3_s1`\*) they become `[a+1]S [0]S0`.
- *Other mergers*: the wall before an S1 of run 0 decides the result, cell by cell `W 110 → W 00`: after S2 it
  becomes X6 = `1000000` (`merge_s2_s1`\*), after S0 it would become X5 = `100000`, after S1 a block `11000`
  outside the vocabulary (which then turns into `1110`, `1100000`, ...). The real run only shows S, S3 and S2
  there (see the K relation in Notes). X6 as a stop becomes `[a]S0 [0]S` (`sweep_x6`\*), X5 becomes `[a+1]S`
  (`sweep_x5`\*).
- *The left end* (all Lean theorems for any carry chain): `0^inf 10 110` (S then S1 with run 0) becomes
  `0^inf 1000` (`left_s_s1`\*). With a first digit of run 0 as the stop: `[0]S0 → [0]S1` (`left_s0`\*),
  `[0]S1 [a]S3... → [a]S0...` (it vanishes, `left_s1`\*), `[0]S2 → [0]S3` (`left_s2`\*), `[0]S3` with only S3
  after it `→ [0]S [0]S0` (`left_s3`\*); `[0]S [0]S0 → [0]S [0]S1` (`left_s_s0`\*), `[0]S [0]S2 → [0]S3 [0]S`
  (`left_s_s2`\*), and `[0]S3 [0]S` followed by S3 digits overflows to `[0]S [0]S0 ...` with a new S1 at the right
  end (`left_s3_s`\*). None halts; all return to the digit form. An S with a run as the stop (from X5) reaches
  further left than `seqtm` allows a fixed window (`TouchContext`); not in Lean.

**Halting**: F reading a 1 is the only halt. None of the rules above passes through it.

## Status

Open. The digit model is exact (checked against the direct run) and it ran to 2.2·10^15 steps without a halt or
an unknown event; every edge event seen is a Lean rule for any carry chain, but no closed set of configurations
has been found (Notes for later).

- **Lean, kernel**: `lean/Sweeps.lean` (from `py/sweeps.py`, lists by `lean/Seq.lean`): `sweep_s0`, `sweep_s1`,
  `sweep_s2`, `sweep_x5`, `sweep_x6`, `merge_s_s1`, `merge_s3_s1`, `merge_s2_s1`, `overflow`, and the eight
  left-end rules `left_s_s1`, `left_s0`, `left_s1`, `left_s2`, `left_s3`, `left_s_s0`, `left_s_s2`, `left_s3_s`:
  each one sweep for every value of the runs, **every carry chain ts (any length)** and every tape L beyond the
  stop. `lean/Rules.lean`: the eight shift rules of the first pass. `lean/Blank.lean`: no halt in 10^7 steps.
- **Trusted** (`py/digits.py`): the digit simulator — each sweep a symbolic run of the machine on a window, cached by
  its shape — agrees with the direct run at all 14,148 sample points up to 2·10^8 steps (`digits.py check 2e8`:
  tapes and step counts); from the sample at 2·10^9 steps it ran 4.9·10^7 sweeps more, to 2.2·10^15 steps: no
  halt, no unknown shape. The first block went 14 → 1 (one per overflow, 13 overflows) and was used up near
  2.1·10^15 steps: the left end went `[0]S [1]S0 ...` → `[0]S3 [0]S [436]S0 ...` → `[0]S [0]S0 [435]S0 ...` (the
  run of 436 is now the first block) and the counter went on. (The long run used a scratch copy of the same code.)
- **Trusted**: no halt in 10^9 steps (C); n-gram CPS fails at widths 3..7.

## Notes for later

The second pass aimed at a full proof and did not get one. What is missing, precisely:

1. **No regular digit language found that is closed.** `py/closure.py ngram N [E MO]` searches for the smallest
   n-gram language over (wall, run class) that contains an early sample and is closed under the window rules
   (every place a sweep can happen, run symbolically). All variants tried fail (heuristic search, open):
   - classes 0, 1, ≥2, bigrams and trigrams: the language drifts into `S1[0] S1[0]`, `[0]S [0]S [0]S`-like
     windows (the head keeps touching the context, or the result leaves the vocabulary);
   - classes 0, 1 and ≥2 by residue mod 4, the first digit marked, compounds `T0 = S[0]S0`, `T1 = S[0]S1` as
     walls: 536 bigrams, then windows with X5 or X6 next to an S1 of run 0, which the real run never shows;
   - a cell-level closed tape language: windows of K cells fail (n-gram CPS, widths 3..7); far-to-near block
     trackers (windows of 2..6 blocks, runs of 100 counted to 2) exceed 4·10^5 abstract configurations without
     closing, far beyond what `decide` can check.
2. **Why: the safe mergers depend on arithmetic between neighbours.** An S1 of run 0 merges safely only after S,
   S3 or S2. With phases S0..S3 = 0..3, for neighbouring digits y x (both S0..S3) the quantity
   `K = phase(y) + run(x) + [x is S2 or S3] mod 4` does not change while both live (x's run drops at its S1→S2
   step, y steps at x's S3→S0 carry), and when x's run reaches 0 the left neighbour is in phase K. Counted over the
   first 3·10^5 sweeps (`py/closure.py kinv`): K is 2 or 3 in 2,091,564 of 2,092,788 neighbour pairs; the 1,224
   others all have y inside an `S[0]S0`/`S[0]S1` compound, which merges before K matters. Also
   `last run ≡ phase(last digit) mod 4` (all but 12 samples). (Heuristic.) So the invariant must at least carry
   runs mod 4 together with the neighbour's phase, and also say what K is for X6, the `S0[0]S` it turns into, and
   the compounds; the bigram search with mod-4 classes loses it through those (over-approximation at the
   compounds and X6), and nothing beyond bigrams of residues has been made to close.
3. **Chains with a run of 0.** The `seqtm` chain `[ (100)^c 1 0 0 1 0 1 0 ]^ts` has every S3 at run ≥ 1. Chains
   with S3 of run 0 occur (after S2, at the left end); `[ (100)^c 1 0 1 0 ]^ts` (c ≥ 0) fails in `seqtm`
   (`TouchContext`): it needs a list of two kinds of block, or a separate rule per position.
4. **Assembly** (not started, waits on 1 and 3): an encoding of digit lists as the left tape, `rep_rotate`
   equalities from each rule's end tape (`(010)^c 0 1 0 0 0 1 0` form) back to the encoding, a Lean predicate for
   the language, a proof that every word of it has a rule that applies (stop, chain, context), and induction over
   sample points with `TM.not_halts_of_forall`.

## Reproduce

```sh
python3 holdouts/1RB1LA_0LC0RE_1LD1LB_1RE1LF_1RC0RA_0RC---/py/digits.py check 2e8       # digit model vs direct run
python3 holdouts/1RB1LA_0LC0RE_1LD1LB_1RE1LF_1RC0RA_0RC---/py/digits.py far 1e6 300000 50000
python3 holdouts/1RB1LA_0LC0RE_1LD1LB_1RE1LF_1RC0RA_0RC---/py/closure.py kinv 3e5      # the mod-4 relation
python3 holdouts/1RB1LA_0LC0RE_1LD1LB_1RE1LF_1RC0RA_0RC---/py/closure.py ngram 2        # closure search: fails
python3 holdouts/1RB1LA_0LC0RE_1LD1LB_1RE1LF_1RC0RA_0RC---/py/sweeps.py > holdouts/1RB1LA_0LC0RE_1LD1LB_1RE1LF_1RC0RA_0RC---/lean/Sweeps.lean
python3 holdouts/1RB1LA_0LC0RE_1LD1LB_1RE1LF_1RC0RA_0RC---/py/rules.py > holdouts/1RB1LA_0LC0RE_1LD1LB_1RE1LF_1RC0RA_0RC---/lean/Rules.lean
```

## Deep exact run

No halt in the first 1.77x10^19 steps: the macro simulator `holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/c/msim.c` with blocks of 6 cells ran
from blank tape to step 17,748,289,296,345,434,315. It is exact, and at this block size it agrees with the
direct simulator after 2,000,017,009 steps (`python3 holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/deep.py run 240`, then `verify`).

## Pages

- [`pages/holdouts/1RB1LA_0LC0RE_1LD1LB_1RE1LF_1RC0RA_0RC---/explainer.html`](../../pages/holdouts/1RB1LA_0LC0RE_1LD1LB_1RE1LF_1RC0RA_0RC---/explainer.html)
- [`pages/holdouts/1RB1LA_0LC0RE_1LD1LB_1RE1LF_1RC0RA_0RC---/proof-status.html`](../../pages/holdouts/1RB1LA_0LC0RE_1LD1LB_1RE1LF_1RC0RA_0RC---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LA_0LC0RE_1LD1LB_1RE1LF_1RC0RA_0RC---/lean/check.sh
```
