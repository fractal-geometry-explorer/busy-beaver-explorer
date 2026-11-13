# 1RB1RC_1LC0LE_1RD1RC_1LB0RA_---0LF_1RD1LF

bbchallenge id 41157. One of the six-state holdouts whose halting from blank tape is open (group G07, family: **counter with a halving carry wave (blocks of 1s as digits)**).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RC |
| B | 1LC | 0LE |
| C | 1RD | 1RC |
| D | 1LB | 0RA |
| E | --- | 0LF |
| F | 1RD | 1LF |

## What it does

**Twin of [`1RB1RA_1LC0RC_1RE0LD_0RE0LF_1RA---_1RB1LF`](../1RB1RA_1LC0RC_1RE0LD_0RE0LF_1RA---_1RB1LF/README.md)**, whose README explains the behaviour in full: a counter whose
digits are blocks of 1s (each followed by one 0), with four fixed low digits `14 7 6 4`, and a carry wave that runs
left through the digits, halving each odd one it meets and stopping at the first even one. The two tables differ,
but the tapes at every cycle start are identical (here the head is in state A at the right end, there in state C, and
the step counts differ slightly: the first cycle start is at step 6,053 here, 6,517 there). Inside the cycle the two
machines move differently: here the wave runs in states A (zigzag) and B (between digits), and the run back to the
right end is state C walking over the digits; there a double 0 travels through them.

    S0(ds) = 0^inf 1^dn 0 ... 1^d0 0 1^14 0 1^7 0 1^6 0 1^4 0 A> 1 0^inf          (cycle start, 5,009 steps per cycle)
    wave on a digit with a cells:  a odd  -> leaves (a-1)/2 + 1, the next digit gets (a-1)/2, the wave moves on
                                   a even -> the digit becomes a/2 + 3, the next digit gets a/2, the wave stops
    at the left end of the tape the value 1 halts (E reads a 0)

## Status

**Reduced to an arithmetic iteration, proved in Lean (kernel):** `lean/Wave.lean`, theorem `halts_iff`:
`HaltsFromBlank <-> exists k, iter k = none`, with the same digit map `next` as the twin, from the same digits
`[26, 13, 9, 6]`. The pieces are this machine's own (`py/rules.py` writes `lean/Rules.lean`: the cycle, the wave
entering a digit, the zigzags and their ends, the run back across a digit in state C, its end, the halt); the
composition is the twin's with those pieces. No `sorry`, no extra axioms.

The map is exact against the direct run (`py/model.py check 5e7`: 137 cycle starts up to 5·10^7 steps, digits and
step counts). Iterated with `py/fast.py`: 29 visits of the left end of the tape in the first 4.6·10^24 cycles,
**9·10^52 steps**, no halt. Whether a wave ever brings `2^t - 1` to the left end is open (Collatz-like); heuristically
the chance is below 2^-80. Also in Lean: the halting configurations and 10^7 steps (`lean/Blank.lean`) and the shift
rules for blocks of 1s (`lean/Shifts.lean`).

## Next steps

As for the twin: structure in the values that reach the left end, or a longer run with a bounded memo.

## First look

Growth class **fixed/sqrt** (left: fixed, exponent 0.052; right: sqrt,
exponent 0.53). After 1,000,000,000 steps: 42,663 cells visited (17 left of the
start, 30,165 right), 42,644 ones.

- right, step 644,184,842: `1^893 0 1^896 0 1^1787 0 1^3574 0 1^11945 0 1^14970 0 1^3170 0 1^572 0 1^396 0 1^395 0 1^220 0 1^148 0 1^64 0 1^14 0 1^7 0 1^6 0 1^4 0 1 C>0`
- right, step 840,617,936: `1^893 0 1^896 0 1^1787 0 1^3574 0 1^21173 0 1^9231 0 1^1632 0 1^1406 0 1^682 0 1^396 0 1^220 0 1^148 0 1^64 0 1^14 0 1^7 0 1^6 0 1^4 0 1 C>0`

## Pages

- [`pages/holdouts/1RB1RC_1LC0LE_1RD1RC_1LB0RA_---0LF_1RD1LF/explainer.html`](../../pages/holdouts/1RB1RC_1LC0LE_1RD1RC_1LB0RA_---0LF_1RD1LF/explainer.html)
- [`pages/holdouts/1RB1RC_1LC0LE_1RD1RC_1LB0RA_---0LF_1RD1LF/proof-status.html`](../../pages/holdouts/1RB1RC_1LC0LE_1RD1RC_1LB0RA_---0LF_1RD1LF/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RC_1LC0LE_1RD1RC_1LB0RA_---0LF_1RD1LF/lean/check.sh   # about 2.5 minutes
python3 holdouts/1RB1RC_1LC0LE_1RD1RC_1LB0RA_---0LF_1RD1LF/py/model.py check 5e7
python3 holdouts/1RB1RC_1LC0LE_1RD1RC_1LB0RA_---0LF_1RD1LF/py/fast.py 25
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same tapes at another pace (observed, not proved).** Leave the states aside and compare only the tape and the place of the head. Then a large part of the first 10^7 configurations of this machine are configurations of the machines below, in the same order and up to the end of the run. The steps at which they occur differ, the tables are not renamings of each other, and equal tapes with different states may be continued differently, so this does not tie the halting questions together.

- [`1RB1RA_1LC0RC_1RE0LD_0RE0LF_1RA---_1RB1LF`](../1RB1RA_1LC0RC_1RE0LD_0RE0LF_1RA---_1RB1LF/README.md): 9,942,119 configurations, the last at step 9,945,848 here and step 10,000,000 there

<!-- end of related machines -->
