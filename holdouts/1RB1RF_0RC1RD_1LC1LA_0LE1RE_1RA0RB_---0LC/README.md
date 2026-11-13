# 1RB1RF_0RC1RD_1LC1LA_0LE1RE_1RA0RB_---0LC

bbchallenge id 175438. One of the six-state holdouts whose halting from blank tape is open (group G13). Family: **recursive counter riding a growing wall**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RF |
| B | 0RC | 1RD |
| C | 1LC | 1LA |
| D | 0LE | 1RE |
| E | 1RA | 0RB |
| F | --- | 0LC |

## What it does

One of three G13 machines with the same behaviour (with `1RB0LA_1RC---_0LD1RD_0RA0RE_0RF1RC_1LF0LA` and `1RB0LA_1RC---_0LD1RD_0RB0RE_0RF0LD_1LF0LA`).
After a short start the tape is: debris on the far left, a solid **wall** of 1s, and right of it a short **list**
of blocks. The head shuttles between the wall and the end of the list; each return to the wall makes the wall 3
cells longer, so the tape grows linearly while the list stays short (82 cells after 10^9 steps).

At each visit of the head (state E) to the cell right of the wall, the tape right of the wall is a list of
blocks `1^(3k) 0` (k = 0: an extra 0) and a tail `1^(6+3j)`, written `k1 k2 ... kn Tj`. On the way right each block
`1^(3k) 0` is rewritten as `1^3 0 (1^2 0)^(k-1)` and on the way back as `1^(3k) 0` again.

### The pass map (conjectured, checked)

From one wall visit to the next:

- no 0 in the list: `... Tj -> ... j T0` (j >= 1), `... T0 -> ... 0 T0`;
- otherwise, at the first 0, with n the entry before it: `n 0 X -> (n-2) 1 f(X)` for n >= 2, where
  `f(T0) = 1 T0` and `f(1 Y) = 2 step(Y)` (the part after the empty block takes one step of the same map);
- `a 1 0 T0 -> T(a+1)` and `a 1 0 1 Y -> (a+2) Y`.

So the list is a counter whose digits are counters (each deeper rule fires about half as often). `py/passmap.py`
(with `c/blkev.c`) checks the map on every wall visit: in the first 10^9 steps 1,901,400 visits follow it
(1,901,400 after one pass, 0 after two or three, the intermediate visit being in another state), and
0 passes reach the wall, where the map does not apply. At the end the wall has 5,706,542 cells and the
list is `1 1 2 1 7 3 3 2 1 1 T0`.

### The wall and collapses

When the first 0 is next to the wall, or `a 1 0` has the wall as `a`, the wall takes part. In
`1RB0LA_1RC---_0LD1RD_0RB0RE_0RF0LD_1LF0LA` this caused a collapse at step 1,858,969: the list became `1 T0`, the
tail swallowed the wall, and the head swept left over older walls of lengths 8192, 2048, 512, 128, 32 (ratio 4),
erasing them into markers `1^6 0^(2*4^k - 2)`, before a new wall started. So the run has epochs.

### Halting

The machine halts if and only if the run reaches E>0 1 0 (Lean, `halts_iff_crit`). F is entered only by A1 = 1RF; A is entered by C1 = 1LA, which leaves a 1 right of the head, and by E0 = 1RA. So the only halt is E>0 1 0, 1 A>1 0, 1 1 F>0.
In 10^9 steps E reads a 0 exactly 73 times: 69 times followed by 0 0 0 (last at step 459,739), once by 0 0 1 (step 2,506), 3 times by 0 1 1 (last at step 241,338); never by a 1.

## Phase 3 results

`lean/HaltIff.lean` (hand-written, kernel): `halts_iff_crit`: HaltsFromBlank <-> the run reaches a configuration
`E>0 1 0`. The proof is the invariant `Safe` (while no such configuration has occurred, A on a 1 has a 1 on its right and F reads a 1),
kept by every step from a non-critical configuration (`safe_step`).
`c/crit.c` counts how often state E reads a 0 and what is right of it (numbers above).

## Status

Open. Lean (`lean/Blank.lean`): the halting configurations, no halt in 10^4 steps (kernel) and 10^7 steps
(`native_decide`). Lean (`lean/HaltIff.lean`, kernel): the machine halts iff the run reaches E>0 1 0. C: no halt in 10^9 steps. The pass map: trusted computation for 10^9 steps, not proved.

## Later

1. Prove the two sweeps in Lean with `bbtools.seqtm` (a list of blocks `1^(3k) 0` crossed rightwards becomes
   `1^3 0 (1^2 0)^(k-1)` blocks, and back), then the end-of-list rules, then the pass map by induction on the list.
2. Classify the passes that reach the wall and find the restart rule. Seen so far: the first entry of the list becomes an empty
   block, the whole wall is erased, the head restarts at the left end of the tape and the new structure later absorbs the old
   list (walls and markers of sizes 2*4^k appear on the way). By `halts_iff_crit` a halt needs E>0 1 0; in the machine
   1RB0LA_1RC---_0LD1RD_0RA0RE_0RF1RC_1LF0LA state D reads a 0 only in these restarts, so the proof has to show that a restart
   only ever shows D the words 0 0 0 0 and 0 1 1 1. Derive the restart from the machine; too few have been seen to fit a rule to data.
3. Look for a closed form of the counter (the frequencies halve with depth), which would give the exact growth law.
4. The whole-tape frame-map method of 1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC does not apply as it is, for the same reason as for 1RB0LA_1RC---_0LD1RD_0RA0RE_0RF1RC_1LF0LA: the list of blocks grows and every pass crosses all of it.

5. Port the pass relation of the sibling 1RB0LA_1RC---_0LD1RD_0RA0RE_0RF1RC_1LF0LA (its `lean/Sweeps.lean`, `PassTail.lean`, `PassRules.lean`,
   `PassRel.lean`: both sweeps and most of the pass map proved for every list, the recursion handled as a bounce inside one
   rightward sweep). The structure of the proof carries over; the unit runs and the fixed turns have to be found again for
   this machine's table (simulate each turn, state it with `app` words, prove it by `rfl`).

## Pages

- [`pages/holdouts/1RB1RF_0RC1RD_1LC1LA_0LE1RE_1RA0RB_---0LC/explainer.html`](../../pages/holdouts/1RB1RF_0RC1RD_1LC1LA_0LE1RE_1RA0RB_---0LC/explainer.html)
- [`pages/holdouts/1RB1RF_0RC1RD_1LC1LA_0LE1RE_1RA0RB_---0LC/proof-status.html`](../../pages/holdouts/1RB1RF_0RC1RD_1LC1LA_0LE1RE_1RA0RB_---0LC/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RF_0RC1RD_1LC1LA_0LE1RE_1RA0RB_---0LC/lean/check.sh
python3 holdouts/1RB1RF_0RC1RD_1LC1LA_0LE1RE_1RA0RB_---0LC/py/passmap.py 1RB1RF_0RC1RD_1LC1LA_0LE1RE_1RA0RB_---0LC 1000000000   # the pass map, ~1 min
gcc -O2 -o /tmp/crit holdouts/1RB1RF_0RC1RD_1LC1LA_0LE1RE_1RA0RB_---0LC/c/crit.c && /tmp/crit 1RB1RF_0RC1RD_1LC1LA_0LE1RE_1RA0RB_---0LC 1000000000 E   # how often E reads a 0 (add `show` for the tapes)
```
