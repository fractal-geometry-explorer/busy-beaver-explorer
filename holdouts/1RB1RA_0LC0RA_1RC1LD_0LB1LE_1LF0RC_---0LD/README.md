# 1RB1RA_0LC0RA_1RC1LD_0LB1LE_1LF0RC_---0LD

bbchallenge id 152765. One of the six-state holdouts whose halting from blank tape is open. Family: a
two-counter marker sweep, cryptid-like and not solved.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RA |
| B | 0LC | 0RA |
| C | 1RC | 1LD |
| D | 0LB | 1LE |
| E | 1LF | 0RC |
| F | --- | 0LD |

## Status

Open. Lean (`lean/Blank.lean`): the halting configurations (`step_none_iff`), no halt in 10,000 steps by
the kernel, in 10,000,000 by `native_decide`. Lean (`lean/Rules.lean`, kernel only): twelve sweep rules for
all n. C (`tools/c/triage.c`): no halt in 1,000,000,000 steps.

## Structure

Write a = `110`, b = `100`. The run is a sequence of rounds. Each round starts when the head, in state B,
extends the tape on the right of

    0^inf W b^k 1 0 a^N 1 1 1 B> 0^inf

with a short word W that starts with 1. `c/rounds.c` prints the round starts from blank tape: 54 of them in
1.6 x 10^10 steps, for example

| step | W | k | N |
|---|---|---|---|
| 83 | `10` | 0 | 0 |
| 8,845 | `10101110` | 0 | 27 |
| 32,577 | `10101110` | 0 | 60 |
| 8,725,889 | `10101110` | 0 | 1016 |
| 241,398,237 | `10101110` | 0 | 6001 |
| 1,427,728,057 | `10101110` | 0 | 16345 |
| 2,407,917,297 | `101001011000` | 1816 | 16346 |
| 3,789,086,613 | `10101` | 1 | 26972 |
| 7,282,953,315 | `101001011010` | 0 | 43155 |
| 16,225,118,173 | `101001011010` | 0 | 69047 |

Inside a round a marker `1 a 0` = `11100` sits in the run of a's and the head shuttles between it and the
left end. After the old b's are converted, the main phase repeats a period that carries 27 a's across the
marker and writes three b's at the left end (`py/gen_period.py`, a symbolic run for all k, x, y):

    D> 0 b 1 0 1 a b^k 1 0 a^(x+27) 1 a 0 a^y   ->   D> 0 b 1 0 1 a b^(k+3) 1 0 a^x 1 a 0 a^(y+27)

in 324k + 162x + 3629 steps. When fewer than 27 a's are left, the remainder and W decide the next W, k and N.
Usually k and N grow by about 10% a round; in a reset round the b's run out, k drops to 0, W becomes
`10101110` or a relative, and N grows by a factor of about 1.65. The left part W b^k acts like one counter
(about 9k plus a value read from W), N like a second.

Halting is F0. The head reaches it only when, in state D, it lands on a 1 with `00` to its left (D1 writes 1
and moves left in E, E0 moves left in F, F0 halts), for example on the leftmost 1 of the tape. No round from
blank tape does this, and neither do about 20,000 synthetic rounds (`c/round.c`, every word W seen in the run
with k <= 80 and N <= 600). The set of words W reachable from arbitrary (k, N) is not closed: thousands of new
words appear, so this is no closed-set argument.

## For later

This needs more than a day of work. Steps:

- Write the round map (W, k, N) -> (W', k', N') in closed form: phase 1 (converting the old b's), the
  27-period, and the remainder cases. The remainder N mod 27 and the residue word W seem to be what matters.
- Prove the period in Lean. The Lean file that `py/gen_period.py --lean` prints (about 940 KB) hits a kernel
  deterministic timeout, even when it is cut to the first 6 of the 27 a's. It needs smaller lemmas, for example
  one lemma per crossing of a single a, or a rule about the marker that does not unroll the 27 copies.
- With the map known: look for a Collatz-type heuristic for the orbit, or an invariant on W that rules out
  the halting pattern.

## Pages

- [`pages/holdouts/1RB1RA_0LC0RA_1RC1LD_0LB1LE_1LF0RC_---0LD/explainer.html`](../../pages/holdouts/1RB1RA_0LC0RA_1RC1LD_0LB1LE_1LF0RC_---0LD/explainer.html)
- [`pages/holdouts/1RB1RA_0LC0RA_1RC1LD_0LB1LE_1LF0RC_---0LD/proof-status.html`](../../pages/holdouts/1RB1RA_0LC0RA_1RC1LD_0LB1LE_1LF0RC_---0LD/proof-status.html)

## Check

```sh
python3 holdouts/1RB1RA_0LC0RA_1RC1LD_0LB1LE_1LF0RC_---0LD/py/gen_period.py
gcc -O2 -o rounds holdouts/1RB1RA_0LC0RA_1RC1LD_0LB1LE_1LF0RC_---0LD/c/rounds.c && timeout 300 ./rounds
. /etc/profile.d/lean.sh && holdouts/1RB1RA_0LC0RA_1RC1LD_0LB1LE_1LF0RC_---0LD/lean/check.sh
```
