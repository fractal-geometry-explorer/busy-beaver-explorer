# 1RB0RD_1LC1LB_---1LD_1RA0RE_1RD0LF_1LE0LD

bbchallenge id 180739. One of the six-state holdouts whose halting from blank tape is open (group G13). Family: **array of (10)-counters behind a growing (10) run**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RD |
| B | 1LC | 1LB |
| C | --- | 1LD |
| D | 1RA | 0RE |
| E | 1RD | 0LF |
| F | 1LE | 0LD |

## What it does

Write a for the pair 1 0. Each time the head is at the left end in state E, the tape reads E>1 a^N 1^2 0 1^2 0 a^K 1^2 0 &hellip;: a long run of N pairs, two markers, a second long run of K pairs, and then many shorter runs of pairs, each followed by a marker 1^2 0 or 1 0^2. At step 2,157,249 N = 527 and K = 385; at step 19,526,315 N = 1,052 and K = 964.

So the tape looks like an array of counters, each a run of pairs, and the two kinds of markers look like a bit attached to each counter. The head sweeps the whole array; how one sweep changes the counters is not yet worked out.

### Halting

The machine halts when it reads a 0 in state C (C0 is the halting transition). C is entered from B on a 0 (B0 = 1LC), so a halt needs 0 B>0 reached moving left, which needs two adjacent 0s. Inside the word the only double 0s are in the markers 1 0^2.

## Phase 2 results

`lean/Rules.lean` proves three shift rules for every n (D and A over `(10)^n`, E over `(01)^n`).
`py/leftcounter.py` checks the left-end counter: at F-left samples `F>0 0 a^n X Y W` (a=10, P=110, Q=100), (X,Y)
cycles (P,P) (Q,P) (P,Q) (Q,Q) (P,aP) (Q,aP), with n going up by 7 per cycle; in 10^9 steps 981 transitions follow it
(164 cycles), and 4 at the start do not; the last n is 1151. The rest of the tape W changes too and has no map yet.

## Status

Open. Lean (`lean/Blank.lean`): the halting configurations, no halt in 10^4 steps (kernel) and 10^7 (`native_decide`). C: no halt in 10^9 steps. Lean (`lean/Rules.lean`, kernel): the shift rules `shiftD`, `shiftA` (over `(10)^n`, leaving `(01)^n`) and `shiftE` (over `(01)^n`, leaving `(10)^n`), for every n and any surrounding tapes. Trusted: the left-end six-step counter (`py/leftcounter.py`). The full map is not found.

## Later

1. Sample at E-left and at the right end; write each tape as a list of (pair count, marker) and find the sweep rule.
2. Check whether the two long runs N and K grow linearly in the number of sweeps and what feeds them.
3. Look at what happens when a counter between markers reaches 0 (the only place a double 0 could meet B).

## Pages

- [`pages/holdouts/1RB0RD_1LC1LB_---1LD_1RA0RE_1RD0LF_1LE0LD/explainer.html`](../../pages/holdouts/1RB0RD_1LC1LB_---1LD_1RA0RE_1RD0LF_1LE0LD/explainer.html)
- [`pages/holdouts/1RB0RD_1LC1LB_---1LD_1RA0RE_1RD0LF_1LE0LD/proof-status.html`](../../pages/holdouts/1RB0RD_1LC1LB_---1LD_1RA0RE_1RD0LF_1LE0LD/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RD_1LC1LB_---1LD_1RA0RE_1RD0LF_1LE0LD/lean/check.sh
python3 holdouts/1RB0RD_1LC1LB_---1LD_1RA0RE_1RD0LF_1LE0LD/py/leftcounter.py 1000000000
```
