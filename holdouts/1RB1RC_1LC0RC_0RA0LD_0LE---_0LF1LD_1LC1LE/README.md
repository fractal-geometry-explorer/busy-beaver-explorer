# 1RB1RC_1LC0RC_0RA0LD_0LE---_0LF1LD_1LC1LE

bbchallenge id 34590. One of the six-state holdouts whose halting from blank tape is open. Family: separators
on a lattice of `10`s, moving and colliding like particles (exp/sqrt), not solved.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RC |
| B | 1LC | 0RC |
| C | 0RA | 0LD |
| D | 0LE | --- |
| E | 0LF | 1LD |
| F | 1LC | 1LE |

## What it does

Write `a` for `10`. The tape is a long lattice of `a`s cut into blocks by *separators*: a single extra `0`
(`a^x 0 a^y`), or a *wall*, two separators side by side, written `0 0` or `0 1` depending on its phase.
None of the sweeps changes a block of `a`s: A crosses `a^n` to the right, D and E cross it to the left, each in
one go (the shift rules in `lean/Rules.lean`). Only the separators move.

**A bounce.** The head goes back and forth between the left end of the tape and the *first wall*; whatever lies
right of the first wall is frozen until that wall gets there. Number the single separators between the left end
and the first wall 1, 2, 3, ... from the left. One bounce (left end to the wall and back) does this:

* With an odd number of them: the left block gains two `a`s, every odd separator moves one `a` to the right,
  every even one stays, and the wall toggles `0 0` -> `0 1` -> `0 0` and moves one `a` to the right every second
  bounce, eating one `a` of the block after it (`lean/Bounce.lean`, `bounce_w00`, `bounce_w01`).
* With an even number: a new block `a` is written at the left end (which renumbers the separators, so the parity
  flips) and the roles swap: odd separators stay, even ones move (`bounce_even_w00`, `bounce_even_w01`).

These four theorems are proved by Lean's kernel for every number of blocks and every block length (at least 3):
the blocks between the left end and the wall are a `seqtm` sequence of any length, crossed by induction
(`lean/Seq.lean`). So per bounce the left end moves one `a` to the left, the moving separators one `a` to the right,
the fixed ones stay, and the wall creeps right at half that speed. The blocks between a moving separator and the fixed one
after it shrink by one `a` per bounce; those are the "counters that go up and down by one" of the first look.

**Collisions** (computed, from `c/seppos.c`). When a moving separator reaches the fixed one in front of it (the
block between them is used up), the two form a new wall, which becomes the first wall and freezes everything to
its right. When the first wall reaches the separator after it, the three cells merge into a single separator and
the next wall downstream becomes the first wall, unfreezing the stretch in between. Between collisions the motion
rule holds exactly: in the first 3·10^8 steps, all 18,678 bounces without a collision move the separators and the
wall as predicted (`py/spcheck.py`). When no wall is left, bounces run to the right end of the tape and add two
cells there; that is the only way the right side grows, which is why it grows like a logarithm, while the left
end gains one `a` per bounce, so the left side grows like the square root of the step count.

**Halting.** The only halting transition is D1. D is entered from C1 and E1, both moving left, so the machine stops
when it lands on a 1 just after one of them; for example `A> 1 1` (A meets two 1s side by side: A writes 1, C reads
the second 1 and moves left in D onto a 1). That needs a short block in the wrong place: random tapes of the same
shape (blocks of `a`s split by single 0s, `0 1` at the right end) halt within 10^5 steps in about 3 % of cases
when the blocks have length 1 or 2, and never in 1,600 trials with all blocks of length >= 3
(`py/random_tapes.py`). The run from blank tape is not fragile in the same way: lengthening or shortening a single
block of the real tape at step 10^6 by one `a` gave no halt within 2·10^7 more steps in 40 trials. Short blocks
appear in the run only next to the left end and in collisions.

**Far runs.** `py/accel.py` is an exact simulator: the macro machine of `bbtools.macro` (blocks of 2 cells, a whole
run crossed in one macro step) plus jumps over repeated periods of bounces (when three records of the tape at
bounces have the same block structure and the run lengths change by the same vector, the period is repeated as
often as every shrinking run allows). It agrees with the plain C simulator (`c/tapehash.c`, a hash of the whole tape)
at 10^6, 10^8, 10^9, 3.6·10^9, 2·10^10 and 5·10^10 steps. It ran 9.1·10^40 steps in 15 minutes without a halt; at
the end the tape was 3.8·10^20 cells wide, with 1,632 runs.

## Status

Open. Lean, all by the kernel:

* `lean/Blank.lean` (generated): the halting configurations (`step_none_iff`); no halt in 10,000 steps by the
  kernel, in 10,000,000 by `native_decide`.
* `lean/Rules.lean` (`py/gen_rules.py`): 9 shift rules for all n.
* `lean/Bounce.lean` (`py/bounce.py`, with `lean/Seq.lean`): the four whole-bounce rules above, for every list of
  blocks.

Computed: no halt in 9.1·10^40 steps (`py/accel.py`, checked against C up to 5·10^10); the separator motion between
collisions (all 18,678 collision-free bounces in 3·10^8 steps). Trusted: no halt in 10^9 steps (`tools/c/triage.c`).

Closed tape languages: windows of K <= 10 cells do not close without halting (for K = 9, 10 the right automaton is
all windows); windows of K <= 6 *letters* (cells, and runs of `10` of length 1, 2 or >= 3; `py/tctl.py`) close but
allow halts next to rows of blocks of length 1.

## For later

* Write the collision rules as `symtm` theorems (a moving separator meeting a fixed one; a wall meeting the next
  separator, in both phases; births next to the left end; the wall-free bounce to the right end) and check that they
  and the four bounce rules cover every configuration the run reaches. Then the run is a deterministic particle
  system on positions, and the question becomes whether a collision can ever produce the short-block pattern that
  halts.
* The perturbation experiment suggests an invariant on the order and spacing of separators rather than on exact
  lengths. A closed language over letters (`py/tctl.py`) with a smarter alphabet (separators and walls as letters,
  block lengths only as 1, 2, >= 3) and windows that see the left end may close; K = 8 letters needs a faster search
  than the Python one.

## Pages

- [`pages/holdouts/1RB1RC_1LC0RC_0RA0LD_0LE---_0LF1LD_1LC1LE/explainer.html`](../../pages/holdouts/1RB1RC_1LC0RC_0RA0LD_0LE---_0LF1LD_1LC1LE/explainer.html)
- [`pages/holdouts/1RB1RC_1LC0RC_0RA0LD_0LE---_0LF1LD_1LC1LE/proof-status.html`](../../pages/holdouts/1RB1RC_1LC0RC_0RA0LD_0LE---_0LF1LD_1LC1LE/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RC_1LC0RC_0RA0LD_0LE---_0LF1LD_1LC1LE/lean/check.sh
python3 holdouts/1RB1RC_1LC0RC_0RA0LD_0LE---_0LF1LD_1LC1LE/py/accel.py 1RB1RC_1LC0RC_0RA0LD_0LE---_0LF1LD_1LC1LE 2 L 6e10 --hash 1e9 2e10 5e10
gcc -O2 -I tools/c -o tapehash holdouts/1RB1RC_1LC0RC_0RA0LD_0LE---_0LF1LD_1LC1LE/c/tapehash.c && ./tapehash 1RB1RC_1LC0RC_0RA0LD_0LE---_0LF1LD_1LC1LE <the step counts accel.py printed>
gcc -O2 -I tools/c -o seppos holdouts/1RB1RC_1LC0RC_0RA0LD_0LE---_0LF1LD_1LC1LE/c/seppos.c && ./seppos 1RB1RC_1LC0RC_0RA0LD_0LE---_0LF1LD_1LC1LE 300000000 0 > sp.txt && python3 holdouts/1RB1RC_1LC0RC_0RA0LD_0LE---_0LF1LD_1LC1LE/py/spcheck.py sp.txt
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0LB_0LC0RD_1LA1LB_0RE---_0RF1RD_1RB1RE`](../1RB0LB_0LC0RD_1LA1LB_0RE---_0RF1RD_1RB1RE/README.md): rename A→C, B→A, C→B, D→D, E→E, F→F and exchange left and right; it is this table started in state B, in a mirror

<!-- end of related machines -->
