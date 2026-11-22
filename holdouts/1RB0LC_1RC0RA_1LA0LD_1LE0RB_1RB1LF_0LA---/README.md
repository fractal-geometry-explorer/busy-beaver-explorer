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
collide. Lean proves that a collision of two cursors can halt (`m+2 | a+2 "0" 1 "1110" |` halts for all m, a), but
the run from blank tape never builds the `1111` such a halt needs (none in 10^10 steps); whether it ever does is not
decided. No halt in 10^11 steps.

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

## Collisions (22 November 2026)

**What a halt needs.** `py/scan.py halts` runs one round from 573,370 event tapes made of runs, separators and short
cell words: every round that halts starts from a tape containing `001111`, or beginning with `000111` (the left end).
So a halt needs four 1s in a row at a round start.

**Rounds with any number of separators (Lean, `lean/Seps.lean`).** For every list of runs `xi = yi + 2`:

    m+2 | x1 | ... | xk | a "1" R       ->  m+1 | x1 | ... | xk | a+2 "0" R       (round_one_sep)
    m+2 | x1 | ... | xk | a "0" b+2 R   ->  m+1 | x1 | ... | xk | a+4 "1" b R     (round_zero_sep)

by induction over the list (`round_sep` takes what the cursor does as a hypothesis).

**A halting collision (Lean, `lean/Collide.lean`, generated by `py/collide.py`).** A walking cursor `"0"` one pair
before a stalled `"1110"` followed by a separator halts:

    m+2 | a+2 "0" 1 "1110" |   halts in 2a+2m+127 steps, for all m, a      (collide_halt, collide_halts)

with three other collisions proved for all lengths: `m+2 | a "0" 2 "0" R -> m+1 | a+4 "10" R` (`merge_zero`, two
cursors merge), `"0" 1 "1" b+1 -> | 2 "0" b` (`zero_one`, a separator is born) and `one_one`. This is the shape of
the halt found by hand in a synthetic search over two-cursor tapes; the minimal one is `2 | 2 "0" 1 "1110" |`.

**Why the run from blank does not get there (observed).** `py/tok.py` is a token simulator: runs are numbers, and the
double rounds of `lean/Seps.lean` are applied in bulk when two explicit ones agree with the formula
(`python3 py/tok.py check 3e7`: the same tape and step count as `py/engine.py` at all 6,756 events).
`python3 py/scan.py run 1e10` runs it 1.04·10^10 steps (110,575 rounds, 120 bulk jumps): **no round start contains
`1111`**. The walking cursor is always one of `"0"`, `"1"`, `"10"`, `"00"`, `"110"`, `"11"` (counts 1234, 1099, 149,
149, 136, 2; the windows are in `py/lead_windows.json`); `"1110"` never walks. The only way to build `1111` found is a
cursor reaching a stalled `| 1 "110"` with an odd gap:

    "0" 1 | 1 "110"  ->  "10" 1 "110"  ->  "00" 1 "110"  ->  | 1 "1110"  (1111, but after a separator: no halt)  ->  | 4 "10"

In the run every arrival at a stalled `| 1 "110"` came with an even gap (`"0" |`, `"0" 2 |`, `"0" 4 |`). A proof of
non-halting would have to show that this parity is kept: the gap is set by the tripling law and the modes, and no
proof of that is known.

**Experiments (not in the repository).** 174 runs of a C simulator from snapshots of the real run (at 3·10^8 and
2·10^9 steps) with one run length or the budget changed by ±1, ±2, ±4 or ±6, or the budget cut to 1, 2 or 3 at a
random round, each for 2–3·10^9 steps: none halted. A closure search that sends a cursor `"0"` or `"1"` at every
moving-cursor window as a stalled pattern grew to more than 1,000 patterns without finding a halt and without closing.

## A relaxed budget: even gaps are not a parity fact (22 November 2026)

The lead was to prove that every cursor reaching a stalled `| 1 "110"` arrives with an even gap. The tripling law
keeps the parity of every run, and the budget loses one pair a round while the cursor's phase flips, so the hope was
that parities alone fix the gap. They do not.

**The relaxed run (`py/relax.py`).** Let the budget run out early: at a round start the first run may be removed
(or, with `KEEP` = 2, 4 or 8, cut to a smaller value with the same residue). Every tape of the real run is a tape of
the relaxed run, so a proof that the relaxed run never halts would settle the machine without knowing any budget.

- With the residue of the budget kept mod 2, 4 or 8, odd arrivals happen within a few hundred rounds and 1111 forms
  (`| 1 "1110"`, after a separator, as in the README route above). So the even gaps of the real run come from the
  sizes of the budgets, not from parities: an invariant on parities cannot prove them.
- Yet none of these runs halts. `python3 py/relax.py cuts 1-12 20000 0` (any stall) and `... 2` (parity kept):
  24 runs, 183,924 rounds, 22,621 cuts (most at moments when the moving cursor is next to a separator or another
  cursor), 843 round starts with 1111, no halt. Runs stop at 3,000 tokens.

**What a halt needs (`python3 py/relax.py route`).** The halting collision of `lean/Collide.lean` has a stalled
`"1110"` directly before a separator (the only halting collision known). One way to get it: a stalled `| 1 "110" |` receives an odd arrival, which
gives `| 1 "1110" |` three rounds later; if the budget runs out exactly then, any even arrival (`"0" |`, `"0" 2 |`,
`"0" 4 |`) halts. But no `"110"` or `"1110"` has ever been seen directly before a separator: in the real run (no
cut, to round 120,000) and in relaxed runs (`python3 py/relax.py words 1-6 8000 0.02`, 21,000 cursor words), the only
words before a separator are `"0"`, `"1"`, `"00"`, `"10"`, `"11"`. A crossing writes `"110"` at the start of the
next run (`"0" | b` becomes `| 1 "110" b`), never at its end.

So the target is better stated as: **no `"110"` or `"1110"` is ever directly followed by a separator, even in the
relaxed run.** That is a local statement about the relaxed run, which needs no budget sizes.

**Tried and stopped.** An n-gram closed-set search over the relaxed run (a window around the moving cursor, runs
longer than 4 pairs kept by parity, the rest of the tape as the set of its 4- or 6-grams) ran without a halt to
about 8,000 windows but did not close: rounds where the head crosses a whole region (a new cursor's first round
reaches the next stalled cursor and moves it) make the windows explode. The scratch code is kept with the project
notes, not here.

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
- `lean/Seps.lean` (kernel): `round_sep`, `round_one_sep`, `round_zero_sep`, the rounds with any number of
  separators.
- `lean/Collide.lean` (kernel, generated by `py/collide.py`): `collide_halt` / `collide_halts` (a two-cursor tape
  that halts), `merge_zero`, `zero_one`, `one_one`.
- `py/scan.py halts`: which tapes halt in one round. `py/scan.py run 1e10` (on `py/tok.py`): no `1111` in 10^10 steps.
- `py/relax.py`: the relaxed run (the budget may run out at any round): odd gaps and 1111, no halt; the halting
  route through a stalled `| 1 "1110" |`; the words seen before a separator.
- Not done: a proof that no `"110"`/`"1110"` stands directly before a separator in the relaxed run (which would
  replace the even-gap claim, false for the relaxed run), and the complete list of collisions.

## First look

Growth class **fixed/sqrt** (left: sqrt, exponent 0.483; right: fixed,
exponent 0.0). After 1,000,000,000 steps: 71,228 cells visited (53,938 left of the
start, 295 right), 35,574 ones.

- left, step 970,211,403: `C>0 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 `
- left, step 985,863,915: `C>0 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 `

## Accelerated run (13 November 2026)

Observed, not proved: the accelerated simulator `rsim.py` ran 6.03x10^14 steps from blank tape without reaching a halting transition. Its tape, state and head position were equal to those of a plain C simulator at 6 checkpoints, the last at 1.03x10^10 steps. Of these steps, the part after the last checkpoint rests on the simulator alone, including 695 trip-level jumps: a jump applies many identical round trips at once after seeing the same tape shape recur with constant count changes, which is validated against direct simulation but not proved.

```sh
python3 holdouts/1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA1RF_0LC---/py/rsim_screen.py 1RB0LC_1RC0RA_1LA0LD_1LE0RB_1RB1LF_0LA--- 400
```

## Pages

- [`pages/holdouts/1RB0LC_1RC0RA_1LA0LD_1LE0RB_1RB1LF_0LA---/explainer.html`](../../pages/holdouts/1RB0LC_1RC0RA_1LA0LD_1LE0RB_1RB1LF_0LA---/explainer.html)
- [`pages/holdouts/1RB0LC_1RC0RA_1LA0LD_1LE0RB_1RB1LF_0LA---/proof-status.html`](../../pages/holdouts/1RB0LC_1RC0RA_1LA0LD_1LE0RB_1RB1LF_0LA---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LC_1RC0RA_1LA0LD_1LE0RB_1RB1LF_0LA---/lean/check.sh
python3 holdouts/1RB0LC_1RC0RA_1LA0LD_1LE0RB_1RB1LF_0LA---/py/tok.py check 3e7
python3 holdouts/1RB0LC_1RC0RA_1LA0LD_1LE0RB_1RB1LF_0LA---/py/scan.py halts
python3 holdouts/1RB0LC_1RC0RA_1LA0LD_1LE0RB_1RB1LF_0LA---/py/scan.py run 1e10
python3 holdouts/1RB0LC_1RC0RA_1LA0LD_1LE0RB_1RB1LF_0LA---/py/relax.py route
python3 holdouts/1RB0LC_1RC0RA_1LA0LD_1LE0RB_1RB1LF_0LA---/py/relax.py cuts 1-12 20000 2
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0RD_1LC0RA_1LA0LB_1RE0LC_1LC1RF_0RB---`](../1RB0RD_1LC0RA_1LA0LB_1RE0LC_1LC1RF_0RB---/README.md): rename A→B, B→C, C→A, D→D, E→E, F→F and exchange left and right; it is this table started in state C, in a mirror
- [`1RB0RC_1LC0LD_1RA0LB_1LE0RA_1RA1LF_0LC---`](../1RB0RC_1LC0LD_1RA0LB_1LE0RA_1RA1LF_0LC---/README.md): rename A→C, B→A, C→B, D→D, E→E, F→F; it is this table started in state B

<!-- end of related machines -->
