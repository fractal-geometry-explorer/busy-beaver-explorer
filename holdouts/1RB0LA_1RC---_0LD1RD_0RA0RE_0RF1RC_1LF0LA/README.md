# 1RB0LA_1RC---_0LD1RD_0RA0RE_0RF1RC_1LF0LA

bbchallenge id 7846. One of the six-state holdouts whose halting from blank tape is open (group G13). Family: **recursive counter riding a growing wall**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LA |
| B | 1RC | --- |
| C | 0LD | 1RD |
| D | 0RA | 0RE |
| E | 0RF | 1RC |
| F | 1LF | 0LA |

## What it does

One of three G13 machines with the same behaviour (with `1RB0LA_1RC---_0LD1RD_0RB0RE_0RF0LD_1LF0LA` and `1RB1RF_0RC1RD_1LC1LA_0LE1RE_1RA0RB_---0LC`).
After a short start the tape is: debris on the far left, a solid **wall** of 1s, and right of it a short **list**
of blocks. The head shuttles between the wall and the end of the list; each return to the wall makes the wall 3
cells longer, so the tape grows linearly while the list stays short (161 cells after 10^9 steps).

At each visit of the head (state D) to the cell right of the wall, the tape right of the wall is a list of
blocks `1^(3k) 0` (k = 0: an extra 0) and a tail `1^(7+3j)`, written `k1 k2 ... kn Tj`. On the way right each block
`1^(3k) 0` is rewritten as `1^3 0 (1^2 0)^(k-1)` and on the way back as `1^(3k) 0` again.

### The pass map (conjectured, checked)

From one wall visit to the next:

- no 0 in the list: `... Tj -> ... j T0` (j >= 1), `... T0 -> ... 0 T0`;
- otherwise, at the first 0, with n the entry before it: `n 0 X -> (n-2) 1 f(X)` for n >= 2, where
  `f(T0) = 1 T0` and `f(1 Y) = 2 step(Y)` (the part after the empty block takes one step of the same map);
- `a 1 0 T0 -> T(a+1)` and `a 1 0 1 Y -> (a+2) Y`.

So the list is a counter whose digits are counters (each deeper rule fires about half as often). `py/passmap.py`
(with `c/blkev.c`) checks the map on every wall visit: in the first 10^9 steps 1,311,505 visits follow it
(1,311,477 after one pass, 28 after two or three, the intermediate visit being in another state), and
4 passes reach the wall, where the map does not apply. At the end the wall has 3,954,209 cells and the
list is `4 2 1 1 1 2 1 1 8 1 1 1 3 1 1 1 1 3 1 2 1 1 T5`.

### The wall and collapses

When the first 0 is next to the wall, or `a 1 0` has the wall as `a`, the wall takes part. In
`1RB0LA_1RC---_0LD1RD_0RB0RE_0RF0LD_1LF0LA` this caused a collapse at step 1,858,969: the list became `1 T0`, the
tail swallowed the wall, and the head swept left over older walls of lengths 8192, 2048, 512, 128, 32 (ratio 4),
erasing them into markers `1^6 0^(2*4^k - 2)`, before a new wall started. So the run has epochs.

### Halting

The machine halts if and only if the run reaches D>0 0 1 (Lean, `halts_iff_crit`). B is entered only by A0 = 1RB; A is entered by A1 and F1, which move left and leave a 0 right of the head, and by D0 = 0RA. So the only halt is D>0 0 1, 0 A>0 1, 0 1 B>1.
In 10^9 steps D reads a 0 exactly 25 times: 11 times followed by 0 0 0 (first step 42, last 20,653,972), 14 times by 1 1 1 (first 262, last 4,054,180), never by 0 1. All 25 are in the starts and restarts (steps up to 2,740; 3,775,216 to 4,370,514; 13,579,469; 20,653,972). In passes that follow the map D always reads a 1.

## Phase 2 results

`lean/Rules.lean` (`py/gen_rules.py`, symtm) proves the 11-step unit `L 110 111 B>000 R -> L 111 B>000 111 R`
for all tapes; `lean/Unwind.lean` chains it: `L (110)^n 111 B>000 R` reaches `L 111 B>000 (111)^n R` in 11n steps.
(Phase 3 below proves most of the pass map; the wall and collapse events are still not proved.)

## Phase 3 results

`lean/HaltIff.lean` (hand-written, kernel): `halts_iff_crit`: HaltsFromBlank <-> the run reaches a configuration
`D>0 0 1`. The proof is the invariant `Safe` (while no such configuration has occurred, A on a 0 has a 0 on its right and B reads a 0),
kept by every step from a non-critical configuration (`safe_step`).
`c/crit.c` counts how often state D reads a 0 and what is right of it (numbers above).

### The pass map in Lean

`lean/Sweeps.lean`: `rsweep`, `lsweep`: both sweeps for every list of blocks and any tapes around them. State D turns
`1 0 1 1 (111)^j` (a block as D meets it) into `0 111 (011)^j`; state A with the cursor `A>0 000` turns that into
`0 1^(3j+3)`, four cells further right.
`lean/PassTail.lean`, `lean/PassRules.lean`: with a visit written `visit L ks j` = `L 0 D>1 0 ks Tj` (any left tape L),
four complete passes for every list: `pass_tail` (`ks Tj -> ks j T0`, j >= 1), `pass_zero` (`ks T0 -> ks 0 T0`),
`pass_split` (`ks n 0 T0 -> ks (n-2) 1 1 T0`, n >= 3), `pass_merge` (`ks a 1 0 X -> ks [1^(3a+3) X]`, a >= 1, any tape X:
this is both `a 1 0 T0 -> T(a+1)` and `a 1 0 1 Y -> (a+2) Y`). Each adds `111` on the left (the wall grows by 3).
`lean/PassRel.lean`: the inductive relation `Reach` (rules sweep, bounce, tail, zero, split, split2, merge) and `reach_sound`,
`pass_sound`: every derivation is a run of the machine from a visit to the next visit. The bounce (`bounce_turn`, 19 steps)
is `n 0 1 Y -> (n-2) 1 2` with the right sweep going on into Y (n >= 3), so the recursive rule of the pass map needs no
induction on the nesting. Fixed turns used: `tail_turn` 32 steps, `turn_T0` 54, `turn_split` 66, `turn_empty` 8,
`wall_turn` 15 (all by `rfl`).
`split2` (`turn_split2`, 91 steps) is the end `ks 2 0 T0 -> ks 0 1 1 T0`.
`py/passrel.py 1000000000`: of 1,311,509 pairs of consecutive wall visits, 1,270,317 are one proved pass (zero 460,247,
merge 321,518, tail 243,654, split 122,579, split2 122,319), 27 are two or three proved passes in a row, none contradicts
the relation; not covered: 41,162 pairs of the shape `2 0 1 Y`, 3 with `1 0` at the wall.

A proved fact and a conjecture: `wall_turn` (`0 A>0 000 0 X -> 111 0 D>1 0 X`) holds for any left tape, so it needs only two
0s, not a wall. Conjecture (not checked): in the case `2 0 1 Y` the block 2 becomes an empty block while the sweep goes on
into Y, the returning sweep turns at that empty block and a new pass starts on the right part alone; that would be how a
wall starts, and why `py/passmap.py` sees some visits only after two or three passes of the map.

Restarts of this machine (observed, `c/crit.c ... show`, `c/blkev.c`, `tmrun ... at A L`): at the wall visit of step 3,734,901
the list is `0 1 2 2 2 2 2 1 1 1 0 T0` next to a wall of 40,124 cells; the head erases the whole wall (a run of 40,113
zeros at step 3,775,536), goes to the left end of the tape and starts again as from blank tape, the old list left as
debris far right. At step 4,047,887 the tape holds walls of 1283, 2048, 512, 128, 32, 8 ones separated by `0 1^2 0`; at
step 4,052,252 they are markers `1^6 0^1279 1^6 0^2046 1^6 0^510 1^6 0^126 1^6 0^30 1^6 0^6`. Last visit of the left end:
step 4,053,763 (122 visits in 3*10^9 steps). In the zeros the list goes through shrinking rounds (it merges into the tail
as T13, T11, T9, T7); at step 13,579,469 walls of 32768, 8192, 2048, 512, 128, 32, 8 ones stand right of the list; after
step 20,653,972 D reads only 1s up to 10^9 steps (at 10^9 steps the wall has 3,952,883 cells and the list reaches the right
end of the tape).

What was tried and did not work: a direct finite-automaton (FAR) closure with hand-made automata that track the last 2 or 3
runs with lengths mod 3 on either side (56 to 475 states) accepts the start configuration, so no proof that way.

## Status

Open. Lean (`lean/Blank.lean`): the halting configurations, no halt in 10^4 steps (kernel) and 10^7 steps
(`native_decide`). Lean (`lean/HaltIff.lean`, kernel): the machine halts iff the run reaches D>0 0 1. Lean (`lean/Sweeps.lean`, `PassTail.lean`, `PassRules.lean`, `PassRel.lean`, kernel): both sweeps and the pass relation `Reach` with `pass_sound`, for every list. C: no halt in 10^9 steps. The pass map as fitted (`py/passmap.py`): trusted computation for 10^9 steps; the cases `2 0 1 Y` and the passes at the wall are not proved.

## Later

1. Done in Lean for the cases without the wall (see Phase 3). Still to prove: the case `2 0 1 Y` (the block 2 becomes an
   empty block and the sweep goes on into Y; the return has to cross or turn at that empty block) and the turns with the wall as
   left neighbour. Recipe: simulate the turn from `L blkL(js) D>1 0 R` to the next `A>0 000` (or D cursor), state it with
   `app` words and prove it by `rfl`, then chain with `rsweep`/`lsweep` as in `lean/PassRel.lean`.
2. Classify the passes that reach the wall and find the restart rule. Seen so far: the first entry of the list becomes an empty
   block, the whole wall is erased, the head restarts at the left end of the tape and the new structure later absorbs the old
   list (walls and markers of sizes 2*4^k appear on the way). By `halts_iff_crit` a halt needs D>0 0 1; in the machine
   1RB0LA_1RC---_0LD1RD_0RA0RE_0RF1RC_1LF0LA state D reads a 0 only in these restarts, so the proof has to show that a restart
   only ever shows D the words 0 0 0 0 and 0 1 1 1. Derive the restart from the machine: only three have been seen in 10^9 steps (around steps 1,020, 3,734,901 and 4,050,000).
3. Look for a closed form of the counter (the frequencies halve with depth), which would give the exact growth law.
4. The whole-tape frame-map method of 1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC does not apply as it is: the list grows (28 blocks of 0s on the tape at 10^8 steps, 39 at 10^9), and the sweeps cross the whole list. A frame map here would be the pass map on lists, proved by induction on the list.

5. With all turns proved, look for the invariant: a grammar of nested lists (list, wall, older lists in rewritten form, zero
   fields and debris on the right) closed under all rules, in which D never meets `0 0 1` (`halts_iff_crit`). The same Lean files
   should port to the two sibling machines after re-deriving the fixed turns for their tables.

## Pages

- [`pages/holdouts/1RB0LA_1RC---_0LD1RD_0RA0RE_0RF1RC_1LF0LA/explainer.html`](../../pages/holdouts/1RB0LA_1RC---_0LD1RD_0RA0RE_0RF1RC_1LF0LA/explainer.html)
- [`pages/holdouts/1RB0LA_1RC---_0LD1RD_0RA0RE_0RF1RC_1LF0LA/proof-status.html`](../../pages/holdouts/1RB0LA_1RC---_0LD1RD_0RA0RE_0RF1RC_1LF0LA/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LA_1RC---_0LD1RD_0RA0RE_0RF1RC_1LF0LA/lean/check.sh
python3 holdouts/1RB0LA_1RC---_0LD1RD_0RA0RE_0RF1RC_1LF0LA/py/passmap.py 1RB0LA_1RC---_0LD1RD_0RA0RE_0RF1RC_1LF0LA 1000000000   # the pass map, ~1 min
gcc -O2 -o /tmp/crit holdouts/1RB0LA_1RC---_0LD1RD_0RA0RE_0RF1RC_1LF0LA/c/crit.c && /tmp/crit 1RB0LA_1RC---_0LD1RD_0RA0RE_0RF1RC_1LF0LA 1000000000 D   # how often D reads a 0 (add `show` for the tapes)
python3 holdouts/1RB0LA_1RC---_0LD1RD_0RA0RE_0RF1RC_1LF0LA/py/passrel.py 1000000000   # how many passes are proved passes, ~1 min
```
