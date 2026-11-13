# 1RB0RB_1LC0LF_1RD0LB_1RE1RC_0RA---_1LA1RE

bbchallenge id 95029. One of the six-state holdouts whose halting from blank tape is open (group G10). Family: **two-region bouncer with a Collatz-like reset**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RB |
| B | 1LC | 0LF |
| C | 1RD | 0LB |
| D | 1RE | 1RC |
| E | 0RA | --- |
| F | 1LA | 1RE |

## What it does

Write `Q(x, y) = 1^x 0 (10)^y A>` (A on the blank cell right of the tape). Between resets the machine is a bouncer:
one sweep takes two 1s and makes two `10` pairs, `Q(x+3, y) -> Q(x+1, y+2)`. When the 1s run out:

- one 1 left: `Q(1, y) -> Q(2y+8, 0)`, and the sweeps reach `Q(2, 2y+6)`;
- two 1s left: `Q(2, y)` starts a **reset**. (So every reset starts from some `Q(2, y)`; blank tape reaches
  `Q(6, 0)` after 11 steps, then `Q(2, 4)`.)

The reset from `Q(2, y)`: write `L(a, k) = C> 0 (10)^a 1 1 0 (10)^k ...` at the left end. `Q(2, y) -> L(2, y)`, and
then **ternary rounds** `L(a, k + 2a + 1) -> L(3a + 2, k)`: the middle block of pairs grows 2, 8, 26, 80, 242, 728,
... (`3^(r+1) - 1`), each round eating `2a + 1` pairs of the right block. Inside a round
`S(p, m, k) = 1^p F> 1 0 0 (10)^m 1 1 0 (10)^k` steps `S(p+2, m, k+2) -> S(p, m+3, k)`. When a round runs out of
right pairs, the leftover 1s turn into a gap of 0s, and the same kind of rounds start again inside the gap, with the
gap as the budget (nested rounds, several levels deep for large y). The reset ends at some `Q(x', y')`, irregular in
y:

    y = 4 -> Q(15,2)   38 -> Q(6,51)   55 -> Q(17,53)   144 -> Q(89,107)   396 -> Q(50,403)

Resets from blank tape (the y of each `Q(2, y)`; `c/nq.c`):
4, 38, 55, 144, 396, 451, 1190, 3388, 4980, 5776, 6174, 19656, 39352, ... (the last reset took 3.8·10^9 steps).

## Halting

From `Q(2, y)` the machine halts for y = 1461 (2,574,053 steps), 3158 and 5834, and for no other y < 3000
(`c/nq.c`, full runs). So it halts from blank tape iff the reset orbit 4, 38, 55, ... reaches such a y:
**open, Collatz-like**, and the halting set itself is not understood (it comes out of the nested rounds).

## What is proved (Lean, kernel)

`lean/Leaves.lean` (6 leaf rules by `bbtools.symtm.prove`, `py/gen_leaves.py`) and `lean/Top.lean` (by hand):

- the bouncer: `q_sweep`, `q_one`, and `q_to_two`: every `Q(x, y)` with x ≥ 1 reaches `Q(2, next2 x y)`;
- `blank_to_q`, `blank_to_two`: blank tape reaches `Q(6, 0)` and `Q(2, 4)`;
- `q_two`: `Q(2, y+2) -> L(2, y+2)`;
- `round`: one ternary round `L(a, k+2a+1) -> L(3a+2, k)` for all a ≥ 2, k and any tape to the right;
  `rounds`, `two_rounds`: any number of rounds from a reset.

`lean/Reset.lean` (5 rules in `lean/Ends.lean`, by `py/gen_ends.py`): **how the rounds run out**, for every y.
With `S(p, m, k)` the round step and `N(P, M) = 1^P 0 (10)^M 1^4 0 A>` (a *nested start*):

- `L(a, 1) → Q(2a−1, 3)`, `S(p, m, 0) → Q(p+1, m+2)`, `S(0, m, 1) → Q(2m+9, 0)`: the reset is over;
- `L(a, 0) → N(2a−1, 2)`, `S(p+2, m, 1) → N(p+1, m+4)`: a tank of four 1s right of the pairs; its reset runs the
  rounds again inside, with the pairs and 1s on its left as the budget (the nested rounds).
- `reset_end`: `Q(2, y)` reaches `(resetEnd y).cfg` for all y ≥ 2 (an explicit function); `reset_step`: if that is
  a Q, the next reset is `Q(2, resetMap y)`; `blank_to_nested`: blank tape → resets 4, 38 → `N(35, 26)`.

Of y = 2..3000, 1502 resets are over at once and 1497 nest; the halting y's 1461, 3158, 5834 all nest. Since every other phase is a run proved to reach its end, any halt
from blank tape happens in a nested phase. Not proved: the nested
phase after N(P, M), and therefore the reset map on the resets that nest. Also `lean/Rules.lean` (one-sweep rules
from `bbtools.cycles`) and the generated `lean/Blank.lean`.

## For later

- Prove the nested phase from N(P, M) (the end of the top-level rounds is done, `lean/Reset.lean`): the same rounds
  with the pairs and 1s on the left as the budget. A recursive description (rounds in a gap inside a
  gap ...) with symtm leaves for each level would turn the reset into a Lean function, as for
  1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA.
- Then look for the halting y's (1461, 3158, 5834) in terms of the rounds.

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RB_1LC0LF_1RD0LB_1RE1RC_0RA---_1LA1RE/lean/check.sh
python3 holdouts/1RB0RB_1LC0LF_1RD0LB_1RE1RC_0RA---_1LA1RE/py/gen_ends.py H95029 > holdouts/1RB0RB_1LC0LF_1RD0LB_1RE1RC_0RA---_1LA1RE/lean/Ends.lean
gcc -O2 -o hscan holdouts/1RB0RB_1LC0LF_1RD0LB_1RE1RC_0RA---_1LA1RE/c/hscan.c
./hscan 1RB0RB_1LC0LF_1RD0LB_1RE1RC_0RA---_1LA1RE 1 10 11 1400 1500 B 3     # prints 1461 HALT 2574057
```

## Pages

- [`pages/holdouts/1RB0RB_1LC0LF_1RD0LB_1RE1RC_0RA---_1LA1RE/explainer.html`](../../pages/holdouts/1RB0RB_1LC0LF_1RD0LB_1RE1RC_0RA---_1LA1RE/explainer.html)
- [`pages/holdouts/1RB0RB_1LC0LF_1RD0LB_1RE1RC_0RA---_1LA1RE/proof-status.html`](../../pages/holdouts/1RB0RB_1LC0LF_1RD0LB_1RE1RC_0RA---_1LA1RE/proof-status.html)

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB1RE_0RC---_1RD0RD_1LE0LF_1RA0LD_1LC1RB`](../1RB1RE_0RC---_1RD0RD_1LE0LF_1RA0LD_1LC1RB/README.md): rename A→C, B→D, C→E, D→A, E→B, F→F; it is this table started in state D
- [`1RB0RF_1LC0RA_1LD1LB_0LE---_1LA0LA_1RE1LD`](../1RB0RF_1LC0RA_1LD1LB_0LE---_1LA0LA_1RE1LD/README.md): rename A→E, B→A, C→B, D→C, E→D, F→F and exchange left and right; it is this table started in state B, in a mirror

<!-- end of related machines -->
