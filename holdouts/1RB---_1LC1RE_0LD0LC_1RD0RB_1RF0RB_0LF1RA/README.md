# 1RB---_1LC1RE_0LD0LC_1RD0RB_1RF0RB_0LF1RA

bbchallenge id 132322. One of the six-state holdouts whose halting from blank tape is open (group G11, family *separator counter*). It is a sibling of `1RB---_1RC0RD_1RD1RA_1LE1RB_0LF0LE_1RF0RD`: same event rule and halting pattern, different overflows.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | --- |
| B | 1LC | 1RE |
| C | 0LD | 0LC |
| D | 1RD | 0RB |
| E | 1RF | 0RB |
| F | 0LF | 1RA |

## What it does

**Events.** An event is E on blank at the right end; the tape is `1^x1 0 ... 0 1^N E>0`. The last block is a
binary counter with 3-cell digits; the left blocks are a bit string read from the separators (after the first
two 1s, cells in pairs (separator, 1); a separator 1 is a set bit; the first is the top bit). Each event adds
2^j, j = (N+2)/3, and N grows by 3, unless the addition carries out of the top bit. Checked on all 47 such events
of a 4e11-step run and on every string of at most 6 bits run directly (`1RB---_1RC0RD_1RD1RA_1LE1RB_0LF0LE_1RF0RD/py/bitmodel.py`, state E).

**The event rule is proved (Lean, kernel).** With the states renamed (B, C, D, E, F of `1RB---_1RC0RD_1RD1RA_1LE1RB_0LF0LE_1RF0RD` are
E, F, B, C, D here) the two tables agree except there C0 = 1RD, here F0 = 0LF. In the counting phase that
transition is used only on a counter digit: `E> 0 0 x` is E0 1RF, F0 0LF, F1 1RA, A0 1RB, then B on x, the same
effect as there in 5 steps instead of 3. So `lean/Count.lean` is that machine's proof with the states renamed and
two step counts changed: `count`, `iter`, `event_rule` (P(d, b1 :: lo ++ h) reaches P(d+1, b1 :: lo ++ inc h)
when lo has d bits and h has a 0), `event_to_P`, `blank_to_P` (P(0, bits `1100111` lowest first) at step 311).
See that machine's README for the configurations P. Consequence (of `blank_to_P` and `event_rule`; the deduction is not itself a Lean theorem): **the machine can only halt at an overflow.**

**Exact accelerated run.** `1RB---_1RC0RD_1RD1RA_1LE1RB_0LF0LE_1RF0RD/py/accel.py` follows the run from one P configuration to
the next with the proved rules (jumps whose endpoints are proved; the step counts are checked, not proved: the steps of a count are 32 + 8t + 8r for carry lengths t, r, summed in closed form;
this matches a direct run on every phase to 3·10^6 steps) and simulates only the overflows (`c/transient.c` there).
It reproduces the direct run's overflows (P at steps 1,308 and 1,491,493) and finds the third: at step
1,649,096,662,853 the 36-bit string `100000000000011011011000011010110001` (P form, d = 34) overflows; 1,347,301
steps later the run is at P(28, `00000000000000000000000000000011100111110110110`), step 1,649,098,010,154, without a
halt. The fourth overflow is near d = 46, about 10^15 steps.

**Overflows.** The 4e11-step run has 3 (steps 176, 1,173, 1,491,439). After them N is 1 or 7, sometimes with a
block of four 1s for one event; the last leaves 36 bits `000000000000011011011000011010110111` with j = 3. No
formula is known (the overflow map of `1RB---_1RC0RD_1RD1RA_1LE1RB_0LF0LE_1RF0RD` does not apply). All 240 overflowing phases
P(d, bs) with at most 6 bits, run directly (`1RB---_1RC0RD_1RD1RA_1LE1RB_0LF0LE_1RF0RD/py/overflows.py`): the next P has d = 0 in 219
cases (1 to 3 otherwise) and a string 4 to 17 bits longer (mostly 5 to 12), depending on more than the low bits of
R; the only 5 that halt are P(M-2, `10...01`), the phases ending in the all-ones pattern below.

**Halting.** By direct simulation of all strings of at most 6 bits, it halts only for the all-ones string with
j = M: `1^(2M+2) 0 1^(3M-2) E>0`, proved to halt in Lean for M = 4, 5, 6 (746, 1,514, 3,050 steps). The bits below
j never change inside a phase; at the last event of the run (step 206,159,921,357, j = 33) those 33 bits contain
0s, so the current phase cannot halt. It overflows near step 1.6e12.

**Next steps.** Find the overflow rule: at an overflow the head comes back one cell out of phase with the counter;
describe that phase as rules (as for the counts), or fit the small-case table above. Then iterate it.

## Status

- Lean (kernel): `Blank.lean`, `Rules.lean` (erase, fill, walk, pairs, shift), `Shapes.lean` (allones_4/5/6 halt),
  `Count.lean` (the event rule for every size, from which, with `blank_to_P`, halting only at an overflow follows).
- Trusted: no halt in 4e11 steps (`tmrun ... at E R`); the exact accelerated run to step 1.649·10^12 (third overflow).
- Open: the overflow rule, halting.

## Scripts

- `py/leanspec.json`: rules and halting shapes written to `lean/` by `python3 holdouts/1RB---_1RC0RD_1RD1RA_1LE1RB_0LF0LE_1RF0RD/py/leanfiles.py M NS py/leanspec.json lean/`.
- `python3 holdouts/1RB---_1RC0RD_1RD1RA_1LE1RB_0LF0LE_1RF0RD/py/accel.py 1RB---_1LC1RE_0LD0LC_1RD0RB_1RF0RB_0LF1RA E 3 --c=PATH` (PATH: `gcc -O2 -o PATH holdouts/1RB---_1RC0RD_1RD1RA_1LE1RB_0LF0LE_1RF0RD/c/transient.c`): the exact run to the third overflow, in a second.
- `python3 holdouts/1RB---_1RC0RD_1RD1RA_1LE1RB_0LF0LE_1RF0RD/py/pchain.py 1RB---_1LC1RE_0LD0LC_1RD0RB_1RF0RB_0LF1RA E 3e6`: P configurations of a direct run, checked against `event_rule`.
- Event rule (old check): `python3 holdouts/1RB---_1RC0RD_1RD1RA_1LE1RB_0LF0LE_1RF0RD/py/bitmodel.py exhaust 1RB---_1LC1RE_0LD0LC_1RD0RB_1RF0RB_0LF1RA E 6`, and `events 1RB---_1LC1RE_0LD0LC_1RD0RB_1RF0RB_0LF1RA E LOG` on a `tmrun 1RB---_1LC1RE_0LD0LC_1RD0RB_1RF0RB_0LF1RA 400000000000 at E R 400` log.

## Pages

- [`pages/holdouts/1RB---_1LC1RE_0LD0LC_1RD0RB_1RF0RB_0LF1RA/explainer.html`](../../pages/holdouts/1RB---_1LC1RE_0LD0LC_1RD0RB_1RF0RB_0LF1RA/explainer.html)
- [`pages/holdouts/1RB---_1LC1RE_0LD0LC_1RD0RB_1RF0RB_0LF1RA/proof-status.html`](../../pages/holdouts/1RB---_1LC1RE_0LD0LC_1RD0RB_1RF0RB_0LF1RA/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB---_1LC1RE_0LD0LC_1RD0RB_1RF0RB_0LF1RA/lean/check.sh
```
