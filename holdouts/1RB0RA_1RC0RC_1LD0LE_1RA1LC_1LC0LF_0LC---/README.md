# 1RB0RA_1RC0RC_1LD0LE_1RA1LC_1LC0LF_0LC---

bbchallenge id 130046. One of the six-state holdouts whose halting from blank tape is open. Family: **clock and word map (block grows by 2, the word is rewritten by 2^k excursions)** (with the four other clock machines of this batch).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RA |
| B | 1RC | 0RC |
| C | 1LD | 0LE |
| D | 1RA | 1LC |
| E | 1LC | 0LF |
| F | 0LC | --- |

## What it does

At every visit of the left end in state C the tape is `C>0 1^L 0 W`: a block of L ones and a word W of short
blocks. One step earlier the head was in state D on the first 1, one cell to the right: write `J(k, W)` for
`D>1 1^(3+2k-1) 0 W`.

**The clock.** `0 0 J(k, W)` reaches `J(k+1, W')` two cells to the left, where `W' = P^(2^k)(W)` for one fixed map
`P` on words. One application of P (a *P-step*) is one trip of the head into the word and back:
`L 0^3 1 B> W` → `L D> 1^3 0 W'`. The tick `k` is: the sweep (`0 0 D> 1^(3+2k) 0` → `1 0^(4+2k) 1 B>`),
one P-step, the ticks `0, ..., k-1` (each eats two of the zeros the sweep left), and the merge (`1 0 D>1` → `D>1 1 1`).
Its step count is `E + 12·2^k − 2`, E the total cost of the 2^k P-steps. Proved in Lean for every k and every word, whenever the 2^k P-steps all come back.

**The word.** A short binary counter (digits `1 1` / `3`) followed by a block that shrinks when the counter
wraps: clocks inside the word (blocks 1^17, 1^29, …), so a single P-step can contain whole inner ticks.

**Phases.** A phase ends when a P-step does not come back (the front of the word has run out): the head goes left
over the unfinished recursion, the block is dissolved into the word, and a new phase starts from a short block.
Phases of the exact accelerated run with blocks of 9 or more:

| starts at step | block | last tick at step | block | ticks |
|---|---|---|---|---|
| 356 | 1^1 | 1,854 | 1^13 | 7 |
| 3,235 | 1^1 | 18,551 | 1^19 | 10 |
| 33,776 | 1^1 | 153,534 | 1^25 | 13 |
| 273,075 | 1^1 | 7,946,869 | 1^37 | 19 |
| 15,618,450 | 1^1 | 1,023,836,366 | 1^51 | 26 |
| 1,126,675,985 | 1^1 | 53,022,962,637 | 1^23 | 12 |
| 104,918,848,362 | 1^1 | 2.289·10^14 | 1^87 | 44 |
| 2.2905·10^14 | 1^1 | 4.6000·10^14 | 1^41 | 21 |
| 6.9096·10^14 | 1^1 | 3.5437·10^21 | 1^135 | 68 |
| 3.5446·10^21 | 1^1 | 2.9619·10^23 | 1^109 | 55 |
| 2.9619·10^23 | 1^1 | 4.5936·10^27 | 1^85 | 43 |
| 4.5942·10^27 | 1^1 | 1.3345·10^31 | 1^121 | 61 |
| 1.3345·10^31 | 1^1 | 1.1776·10^32 | 1^103 | 52 |
| 1.1777·10^32 | 1^1 | 4.2461·10^39 | 1^139 | 70 |
| 4.2461·10^39 | 1^1 | 2.0897·10^43 | 1^187 | 94 |
| 2.0897·10^43 | 1^1 | 1.3710·10^54 | 1^193 | 97 |
| 1.3710·10^54 | 1^1 | 4.1389·10^56 | 1^205 | 103 |
| 4.1390·10^56 | 1^1 | 1.2557·10^64 | 1^241 | 121 |
| 1.2557·10^64 | 1^1 | 3.5839·10^71 | 1^265 | 133 |
| 3.5839·10^71 | 1^1 | 4.0639·10^80 | 1^337 | 169 |
| 4.0639·10^80 | 1^1 | 1.4749·10^94 | 1^379 | 190 |
| 1.4749·10^94 | 1^1 | 6.9955·10^107 | 1^463 | 232 |
| 6.9955·10^107 | 1^1 | 3.1641·10^120 | 1^481 | 241 |
| 3.1641·10^120 | 1^1 | 3.8007·10^135 | 1^589 | 295 |
| 3.8007·10^135 | 1^1 | 1.4524·10^154 | 1^637 | 319 |
| 1.4524·10^154 | 1^1 | 5.7923·10^176 | 1^763 | 382 |

The run was followed past 5.792·10^176 steps (28 phases, stopped during the 29th): no halt. (An earlier version of
`clock.py` read the unvisited cells of the word as 0s inside a nested P-step; its run, published here before with 43
phases to 5.845·10^23 steps, was wrong after step 2.290·10^14. A direct C run from the tape at the last visit where the two
versions agree reaches the next visit 113,495,848,649 steps later, as the corrected run does.)

**Rounds: the view of the outside proof of a sibling (worker 3, round 2).** busycoq PR 48 proves in Coq that
`1RB0RA_1RC0LC_0LD1RF_1RA1LE_1LD0LB_0RE---` never halts. Its view is not the clock but the *round*: the moments
`0 u A>0` when A stands on a new blank cell at the right end, the whole tape read from the head outwards as a word
u over three tokens V = `1100`, K = `00`, Q = `10`. A round is a transducer scan of u: the head makes a fixed
number of excursions ("calls") into the first token, each token turns the n calls it receives into n' calls into
the next one (doubling or halving n, by the token, a mode and the parity of n), a four-state automaton run from
the far end says which modes can occur, and the calls that reach the blank end are counted there in binary
(K = 0, Q = 1): these digits are the clock. The invariant of that proof is a shape `head ++ p ++ s ++ digits ++ top`
with fixed head, s and top, arbitrary digits, and two rational potentials of p that pin the leading bits of the
final call count; it is closed under a round, and no rule of the transducer halts.

`py/rounds.py` computes the round words exactly (it reproduces u_0 ... u_10 of the PR for that machine, all eleven
compared). This machine has rounds of the same form with the same tokens, but a different word map:

| round | step | tokens | word |
|---|---|---|---|
| 0 | 29 | 3 | VKQ |
| 1 | 188 | 6 | VVVQQQ |
| 2 | 1,731 | 12 | VVVVVVQQKQQQ |
| 3 | 18,336 | 20 | VVVVVVVVKVVQKKQQQQQQ |
| 4 | 152,357 | 30 | VVVVVVVVQVVVKKVVVVQKKQQKQQQQQQ |
| 5 | 7,944,074 | 44 | VVVVVVVVVKVVVVVVVVKKKVVVVVQKKKKQKQQQQQQQQQQQ |
| 6 | 5.1872e8 | 62 | VVVVVVVVVQVVVVVVVVQVVVVVVVKKKKVKVVVVVVQKKKKKKKKQQQQQQKQQQQQQQQ |

and 72, 102, 118, 164, 202, 232, 274, 310, 358, 422, 488, 558, 640 tokens at rounds 7 to 19 (steps 5.2971e10,
1.1441e14, 4.6000e14, 1.7710e21, 1.4987e23, 2.2964e27, 6.6751e30, 6.5550e31, 2.1230e39, 1.0449e43, 6.8550e53,
2.0762e56, 6.2785e63). Differences from the sibling that matter for a proof (all read off these 20 rounds):

- the head of the word is not fixed: it is `V^a s V^8 s V^9 s V^15 s ...` with the separator s alternating between
  K and Q from one round to the next and a growing by one every two rounds (the sibling's head `V^10 K VV K V^18 K`
  is constant from round 10 on); the tail of Qs also alternates. An invariant would have period 2 and a growing
  head.
- `py/calls.py` counts, in a directly simulated round, how often the head enters each token. On the leading Vs the
  count goes 2, 7, 17, 37, 77, 157, 317, 637 (n -> 2n + 3, rounds 1 to 5); further in, K halves it (270 -> 135,
  1531 -> 766 -> 383) and Q or K can turn n into about 3n/2 (23 -> 34, 191 -> 286, 383 -> 572, 3079 -> 4610) or
  leave it nearly unchanged. The sibling's rules only double, halve or keep; here a 3/2 appears, so the rule table
  of PR 48 does not carry over and the potentials would not be powers of two alone.

So the method of PR 48 applies in outline (same tokens, same round structure), but the transducer, its automaton
and the invariant have to be found again for this machine; none of that is done. The Coq file is 2,620 lines; a
port needs (1) the call types and the token rules of this machine proved for all n, (2) the totality of the rule
table under an automaton on the words, (3) a round-closed shape with the potentials that keep the call count
large and fix the top digits.

**Halting.** The only halting transition is F on 1. F is entered only from E on 1 (0LF), and E only from C on 1 (0LE): the machine halts exactly when C reads a 1 with two 1s to its left, `1 1 C>1`. A normal tick cannot halt (it is proved to reach its end), so a halt can only come
at a phase end. Open: a closed form for P^(2^k) on the words that occur, what a phase end builds, and whether one
ever halts.

## Status

Open.

- Lean, kernel (`lean/Clock.lean`): `tick` (the clock for every k and every word, for each tick whose 2^k P-steps all come back, with the exact step count),
  `tick_left_end`; from `lean/Rules.lean` (`rule_sweep`, `rule_merge`, written by
  `holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/py/gen_clock.py` with `bbtools.symtm.prove`).
- Lean, kernel (`lean/Sweeps.lean`): the sweep rules of the self-loops.
- Lean, kernel (`lean/HaltPred.lean`, written by `python3 ../1RB0LD_0RC---_1LD0RF_0LE0RA_0RA1LF_0LA1LB/py/halt_pred.py 1RB0RA_1RC0RC_1LD0LE_1RA1LC_1LC0LF_0LC--- 1 2 3`):
  every configuration that halts after exactly 1, 2 or 3 more steps; `halt_iff_2`: the machine halts two steps later exactly from `1 1 C>1`.
- Lean (`lean/Blank.lean`): the halting configurations (`step_none_iff`), no halt in 10,000 steps by the kernel, in
  10,000,000 by `native_decide`.
- Trusted computation: `holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/py/clock.py` (the tick done at once, P computed by running the machine
  and memoized) gives the same time, block and word as `tools/c/tmrun.c` at every visit of the left end in the
  first 2·10^10 steps (`tmcheck`), and follows the run through 28 phases past 5.792·10^176 steps without a halt.
- ngramcps (widths 2–6), `bbtools.ctl` and `bbtools.invariants` (earlier batch runs): nothing.

## Scripts

- `py/rounds.py M LOG10STEPS [SECONDS]`: the round words `0 u A>0` over V, K, Q (exact, accelerated by `clock.py`).
- `py/calls.py M MAXSTEPS`: entries of the head into each token during a round (direct simulation).
- `python3 holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/py/clock.py 1RB0RA_1RC0RC_1LD0LE_1RA1LC_1LC0LF_0LC--- tmcheck 2e10` — compare with `tmrun` at every visit (a few minutes).
- `python3 holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/py/clock.py 1RB0RA_1RC0RC_1LD0LE_1RA1LC_1LC0LF_0LC--- run 1000` — the phases up to 10^1000 steps.
- `python3 holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/py/gen_clock.py 1RB0RA_1RC0RC_1LD0LE_1RA1LC_1LC0LF_0LC---` — writes `lean/Rules.lean` and `lean/Clock.lean`.

## Next steps

Describe P^(2^k) on the words of the run in closed form (the word holds a counter that P counts down), accelerate a
phase end, and read off the map from one phase to the next.

## Pages

- [`pages/holdouts/1RB0RA_1RC0RC_1LD0LE_1RA1LC_1LC0LF_0LC---/explainer.html`](../../pages/holdouts/1RB0RA_1RC0RC_1LD0LE_1RA1LC_1LC0LF_0LC---/explainer.html)
- [`pages/holdouts/1RB0RA_1RC0RC_1LD0LE_1RA1LC_1LC0LF_0LC---/proof-status.html`](../../pages/holdouts/1RB0RA_1RC0RC_1LD0LE_1RA1LC_1LC0LF_0LC---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RA_1RC0RC_1LD0LE_1RA1LC_1LC0LF_0LC---/lean/check.sh
./tmrun 1RB0RA_1RC0RC_1LD0LE_1RA1LC_1LC0LF_0LC--- 20000000000 at C L 1500
python3 holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/py/clock.py 1RB0RA_1RC0RC_1LD0LE_1RA1LC_1LC0LF_0LC--- tmcheck 2e10
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0RF_1RC0RA_1LD1RB_1LE0LD_1LB0LB_0RB---`](../1RB0RF_1RC0RA_1LD1RB_1LE0LD_1LB0LB_0RB---/README.md): rename A→D, B→E, C→B, D→C, E→A, F→F and exchange left and right; it is this table started in state E, in a mirror
- [`1RB0RE_1LC1RA_1LD0LC_1LA0LA_1RA0RF_0RA---`](../1RB0RE_1LC1RA_1LD0LC_1LA0LA_1RA0RF_0RA---/README.md): rename A→C, B→D, C→A, D→B, E→E, F→F and exchange left and right; it is this table started in state C, in a mirror
- [`1RB0RB_1LC0LE_1RD1LB_1RA0RD_1LB0LF_0LB---`](../1RB0RB_1LC0LE_1RD1LB_1RA0RD_1LB0LF_0LB---/README.md): rename A→D, B→A, C→B, D→C, E→E, F→F; it is this table started in state B

<!-- end of related machines -->
