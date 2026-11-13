# 1RB0RC_1LC1RF_1RE0LD_1LC1LA_---1RD_0RB0RA

bbchallenge id 132224. One of the six-state holdouts whose halting from blank tape is open; analyzed by hand (group G02). The pages are built from [`status.json`](status.json).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RC |
| B | 1LC | 1RF |
| C | 1RE | 0LD |
| D | 1LC | 1LA |
| E | --- | 1RD |
| F | 0RB | 0RA |

## What it does

With the head in A at the left end and words `a = 10`, `b = 110`, `d = 010`, the tape is `a b`, one big block, and
a short tail:

    step 2,831,052,048:  A>a b d a^34948 0 d^23 a d^10 a^26 d^8 a^8 d^8 a^8 d^4 a^2 1
    step 2,851,126,369:  A>a b d^23325 a d^2 a^32 d^16 a^26 d^4 b d^7 a^8 d^4 a^8 1

The big block alternates between `d^Y` and `a^X` (observed): `d^Y` becomes `a^(2Y+2)` (Y = 17,473 → X = 34,948);
`a^X` becomes a d-block of about 2X/3, the remainder and a little of the tail settled in the tail (X = 34,948 →
Y = 23,325). So Y grows by about 4/3 per cycle: 61, 83, 137, 195, 261, 357, 481, 667, 887, 1239, 1675, 2247,
3009, 4025, 5375, 7171, 9565, 12953, 17473, 23325 (to 2.9·10^9 steps). The tail, a small counter, changes only at
the conversions (logarithmic side); the sweeps over the big block make the bouncer side.

Shift rules proved for every n (`lean/Rules.lean`): B crosses `(10)^n`, F crosses `(01)^n`, A turns `011` into
`110`, B turns `110` into `101` (all going right).

## Status

Open. The only halt is E reading a 0, right after C read a 0 and moved right; in 10^9 steps E was entered
5,798,513 times and always read a 1.

- Lean, kernel: shift rules (`lean/Rules.lean`); halting configurations, 10^4 steps (`lean/Blank.lean`).
  `native_decide`: 10^7 steps.
- Computed: no halt in 10^10 steps (`tools/c/tmrun.c`); `bbtools.ctl` K = 2..7 allows a halt; n-gram CPS fails.

## Notes for later

- Write the exact cycle map: X = 2Y + 2 on the d→a side (seen in most cycles; 61 → 120 and the cycles where the tail merges into the block differ),
  and on the a→d side the dependence on X mod 3 and on the tail. Then the halting question should become a
  question about that Collatz-like map (which tail states let C meet `00`).

## Remainder classes (family survey)

- **Rounds between end events, by remainder class** (trusted). Sample the run whenever the head is in state B reading 1 with only 0s to its right. Read leftwards from the head, the tape is then `A U^m B`: one long periodic block between two short context words. For each class (A, U, B, m modulo 1 or 6 (the smallest modulus that works for the context)) the next sample is simulated for six values of m and extended as an affine map of m (with a cubic step count). Along the direct run from blank tape to 3·10^9 steps (111 events) the class map predicts the next event in all 63 rounds it applies to. This is an extrapolation checked by computation, not a proof. Command: `python3 holdouts/1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---/py/ctxround.py 1RB0RC_1LC1RF_1RE0LD_1LC1LA_---1RD_0RB0RA R B 1 check 3e9`
- **No halting class among 398 contexts** (heuristic). Breadth first from the starting context, with every remainder at every context (whether or not the numbers can really produce that sequence of remainders, and only for m large compared with the contexts): 398 contexts expanded, 775 found, to depth 11. None of them halts; the search is not complete (the set of contexts keeps growing), and it says nothing about a halt that needs a context as long as the block itself. 5,888 classes could not be computed (their six simulations disagree or are too long). 128 contexts longer than 300 cells were not expanded. Command: `python3 holdouts/1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---/py/ctxround.py 1RB0RC_1LC1RF_1RE0LD_1LC1LA_---1RD_0RB0RA R B 1 bfs 398`

## Pages

- [`pages/holdouts/1RB0RC_1LC1RF_1RE0LD_1LC1LA_---1RD_0RB0RA/explainer.html`](../../pages/holdouts/1RB0RC_1LC1RF_1RE0LD_1LC1LA_---1RD_0RB0RA/explainer.html)
- [`pages/holdouts/1RB0RC_1LC1RF_1RE0LD_1LC1LA_---1RD_0RB0RA/proof-status.html`](../../pages/holdouts/1RB0RC_1LC1RF_1RE0LD_1LC1LA_---1RD_0RB0RA/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RC_1LC1RF_1RE0LD_1LC1LA_---1RD_0RB0RA/lean/check.sh
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB1LF_1LC0RD_---1LD_1RB1RE_1LA0LB_0LA0LE`](../1RB1LF_1LC0RD_---1LD_1RB1RE_1LA0LB_0LA0LE/README.md): rename A→E, B→A, C→B, D→D, E→C, F→F and exchange left and right; it is this table started in state B, in a mirror

<!-- end of related machines -->
