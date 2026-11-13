# 1RB0LD_0RC---_0LD0RF_1LE1LD_0LA0RD_0RB1RA

bbchallenge id 166072. One of the six-state holdouts whose halting from blank tape is open. Family: **runs of 1100 rewritten end to end**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LD |
| B | 0RC | --- |
| C | 0LD | 0RF |
| D | 1LE | 1LD |
| E | 0LA | 0RD |
| F | 0RB | 1RA |

## Status

Open. Lean: only the generated files (halting configurations; no halt in 10^4 steps by the kernel, 10^7 by
`native_decide`). C: no halt in 10^9 steps.

## What it does

At left-end switches the tape is <code>0 0 0 (100)^6 1100 (100)^4 (1100)^398 1 (1100)^319 100 (1100)^2 0 1100</code> (step 998,319,040); at right-end switches <code>… (1100)^717 1 1100 0 0 0 (1100)^3</code> after a disordered stretch of 37 cells (step 999,616,144). The two runs at the left (409 + 308, then 398 + 319) add up to the one run at the right (716, then 717), to within one word.

Twin: `1RB0LD_0RC---_0LD0RF_1LE1LD_0LA0RD_0RB1RA` and `1RB0LF_1LC0RD_1LA1LC_---0RE_0RB1RA_1LC1LF` behave alike: all 1,423 side switches in the first 10^9 steps fall on the same sides in both, the widths at the n-th switch differ by at most 1, and the run lengths printed agree (409 and 308, 398 and 319, 716, 717).

Halting: B on a 1, entered from A on a 0 or F on a 0 (moving right): a halt is exactly `A>0 1` or `F>0 1`.

Growth: 1,423 side switches in 10^9 steps; after 5·10^8 they are ≈ 0.196·w² steps apart and add ≈ 2.0 cells each, so
width ~ t^(1/3) (fitted 0.326; 2,924 cells). `py/shape.py` and `py/switches.py` print all of this from a `tmrun ... records` log.

## Later

1. Find the rule that maps one side switch to the next (sizes of the runs), as was done for the hole-wandering
   machines of this group (e.g. `1RB0LA_0RC---_0RD0RF_1LD0LE_0LA1LE_0RA0LA`), and prove its pieces with `bbtools.symtm`.
2. Show that the halting pattern can never arise from the shapes seen.

## First look

Growth class **power/power** (left: power, exponent 0.324; right: power,
exponent 0.328). After 1,000,000,000 steps: 2,925 cells visited (1,793 left of the
start, 591 right), 1,451 ones.

- left, step 969,560,369: `D>0 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1^2 0^2 1 0^2 1 0^2 1 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 `
- left, step 985,856,541: `D>0 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 `
- right, step 983,055,140: `1 0^5 1 0^2 1 0^8 1 0^14 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2`
- right, step 999,616,144: `1 0^5 1 0^2 1 0^8 1 0^5 1^2 0^11 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2`

## Pages

- [`pages/holdouts/1RB0LD_0RC---_0LD0RF_1LE1LD_0LA0RD_0RB1RA/explainer.html`](../../pages/holdouts/1RB0LD_0RC---_0LD0RF_1LE1LD_0LA0RD_0RB1RA/explainer.html)
- [`pages/holdouts/1RB0LD_0RC---_0LD0RF_1LE1LD_0LA0RD_0RB1RA/proof-status.html`](../../pages/holdouts/1RB0LD_0RC---_0LD0RF_1LE1LD_0LA0RD_0RB1RA/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LD_0RC---_0LD0RF_1LE1LD_0LA0RD_0RB1RA/lean/check.sh
gcc -O2 -o /tmp/tmrun tools/c/tmrun.c && /tmp/tmrun 1RB0LD_0RC---_0LD0RF_1LE1LD_0LA0RD_0RB1RA 1000000000 records 100000 > /tmp/rec.txt
python3 holdouts/1RB0LD_0RC---_0LD0RF_1LE1LD_0LA0RD_0RB1RA/py/shape.py /tmp/rec.txt c=1100,b=100
python3 holdouts/1RB0LD_0RC---_0LD0RF_1LE1LD_0LA0RD_0RB1RA/py/switches.py /tmp/rec.txt c=1100,b=100
```
