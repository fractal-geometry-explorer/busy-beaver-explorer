# 1RB0LC_1RC0RA_1LA0LD_1LE0RB_1RB1LF_0LA---

bbchallenge id 37843.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LC |
| B | 1RC | 0RA |
| C | 1LA | 0LD |
| D | 1LE | 0RB |
| E | 1RB | 1LF |
| F | 0LA | --- |

## Status

**Open.** Seen only in state A the machine is a rewriting system of ten rules, proved in Lean for every tape, and it
halts exactly when state A reads a 1 with `1101` on its left. On the tape these rules move *cursors* through a list
of runs of `01`, tripling each run they cross; cursors are created at the left end, stall behind each other and
collide. Whether a collision ever produces `1101 A>1` is not decided: no halt in 10^11 steps.

## What it does

**The ten rules (Lean, `lean/Rules.lean`).** From any configuration in state A, the next configuration in state A is
given by one of these (L, R: any tape; `py/macro.py` is the exhaustive case split):

    R1   A> 01             ->  10 A>                 (2 steps)
    R2   A> 00 1^k 0       ->  1 0^k A>1 1           (3k+3 steps: k ones erased, the head turns)
    L1   10 A>1            ->  A>1 10
    L2   10101 A>1         ->  A>1 01100
    L3   111 A>1           ->  A>1 101
    L4   1101 A>1          ->  halt (state F reads 1, 4 steps later)
    L5   00 A>1            ->  A>0 10               (the head turns right; at the left end: a new round)
    L6   00101 A>1         ->  A>0 01100
    L7   011 A>1           ->  A>0 101
    L8   001 A>1           ->  10 A>0 0

So the machine halts iff `1101 A>1` ever appears (`bad_halts`).

**Runs, separators, cursors.** At the moments the head is in state A at the left end (an *event*; a *round* is the
time between two) the tape is a list of runs `(01)^n` with other cells between them. Write `n` for a run, `|` for
the separator `00110`, and the other cells in quotes. The run from blank tape starts

    4  ->  3 | 1  ->  2 | 1 | 1  ->  1 | 1 | 1 | 1  ->  | 1 | 1 | 1 | 1  ->  5 "10" 1 | 1 | 1 | 1  ->  ...

In a round the head flips runs (R1) and crosses separators (R2 with k = 2, then L5, R1, R1: `pass_sep`) until the
first *cursor*, a single odd cell: at a `1` it turns at once, at a `0` it turns by R2. On the way back every
separator it crosses moves two pairs from its left to its right (`back_sep`), and the left end gives the first run
one pair (`left_end`). Net effect of a round on `m | a1 | ... | ak "c" b ...`: the first run loses a pair, the runs
between separators keep their length, and the cursor moves:

    a "1" b  ->  a+2 "0" b          a "0" b  ->  a+4 "1" b-2      (round_one, round_zero; first_one, first_zero
                                                                     when the cursor is in the first run)

so a cursor walks through a run of length b in about b rounds and leaves about 3b pairs behind. At the end of a run
it crosses the separator in a few rounds (`zero_sep`, `onezero`, `zerozero`, `zero_at_sep`) and enters the next
run in one of two modes. The law of a whole crossing (`py/laws.py`, checked on random run lists):

    mode A:  b odd -> 3b      (next run in mode B)        b even -> 3b + 4  (next run in mode A)
    mode B:  b even -> 3b + 4 (next run in mode B)        b odd  -> 3b + 8  (next run in mode A)

That is where the layers of the first look come from: (1, 1) -> (3, 11) -> (9, 41) -> (27, 131) -> (81, 401), a
period-2 list in modes A, B, A, B.

**The budget.** Every round costs the first run one pair. A cursor in the first run feeds it instead (three pairs
per pair it moves), so each new cursor starts with a budget of about twice the first run it ate, and spends it one
pair a round while it walks. When the first run is empty the first separator turns into a new cursor (`| a` becomes
`4 "1" a-2`) and the old cursor stays where it is: only the first cursor ever moves. The tape therefore carries a
stack of stalled cursors (six cursors after 10^10 steps), and each new cursor triples the runs up to the next
stalled one and then collides with it. Collisions seen: two cursors `1` side by side vanish (`annihilate`); `1`
one pair behind `1` leaves a separator and one cursor; `0` two pairs behind `0` merges into one cursor `10`. With
no cursor left the head runs to the end of the tape and appends `| 1` every round until the first run is empty.

**Why it is open.** The halting pattern `1101 A>1` needs a cell 1 where the right pass normally leaves a 0, for
instance a separator whose left neighbour is a run of exactly one pair after such a cell; a single cursor among
long runs never makes one (the rounds above), so a halt can only come out of a collision of cursors with short
runs. Which collisions happen depends on the run lengths (parities of numbers that have been tripled many times,
plus 0, 4 or 8) and on when each budget runs out, and no invariant is known that excludes the bad ones. A note on
an outside tracker (not checked here) describes the machine as two arrays of balanced-ternary codes that must
avoid bad values, and says that relaxed versions of the rules do halt.

## Results

- `lean/Rules.lean` (generated by `py/rules.py`, kernel): the ten rules `R1`, `R2`, `L1`..`L8` for every tape, with
  `bad_halts` (`1101 A>1` halts); the passes `pass_run`, `pass_sep`, `back_run`, `back_sep`, `left_end`; and nine
  rounds for all run lengths (`round_one`, `round_zero`, `first_one`, `first_zero`, `zero_sep`, `onezero`,
  `zerozero`, `zero_at_sep`, `annihilate`).
- `py/macro.py`: the case split behind the ten rules (finite; one halting case).
- `py/engine.py`: an exact run-length simulator (machine steps plus the jumps `pass_run` and `back_run`).
  `python3 py/engine.py check 3e8`: the same step count at each of the 22,399 events of the first 3·10^8 steps of the
  C simulator and the same tape at the 409 compared (every event of the first 3·10^7 steps was compared tape for
  tape while writing it). `python3 py/engine.py run 2e10`: no halt in 2·10^10 steps (133,716 events, seconds).
- `py/laws.py`: the crossing law on 300 random run lists.
- C (`tools/c/tmrun`): no halt in 10^11 steps.
- Not done: the rounds with any number of separators as one Lean theorem (the passes are there, the induction over
  the list of runs is not), the complete list of collisions, and any argument about which run lengths occur.
  Next step: write the system as a map on (first run, list of runs, stack of cursors) with the collision table,
  check it against `py/engine.py`, and study the parities along the layers.

## First look

Growth class **fixed/sqrt** (left: sqrt, exponent 0.483; right: fixed,
exponent 0.0). After 1,000,000,000 steps: 71,228 cells visited (53,938 left of the
start, 295 right), 35,574 ones.

- left, step 970,211,403: `C>0 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 `
- left, step 985,863,915: `C>0 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 `

## Pages

- [`pages/holdouts/1RB0LC_1RC0RA_1LA0LD_1LE0RB_1RB1LF_0LA---/explainer.html`](../../pages/holdouts/1RB0LC_1RC0RA_1LA0LD_1LE0RB_1RB1LF_0LA---/explainer.html)
- [`pages/holdouts/1RB0LC_1RC0RA_1LA0LD_1LE0RB_1RB1LF_0LA---/proof-status.html`](../../pages/holdouts/1RB0LC_1RC0RA_1LA0LD_1LE0RB_1RB1LF_0LA---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LC_1RC0RA_1LA0LD_1LE0RB_1RB1LF_0LA---/lean/check.sh
```
