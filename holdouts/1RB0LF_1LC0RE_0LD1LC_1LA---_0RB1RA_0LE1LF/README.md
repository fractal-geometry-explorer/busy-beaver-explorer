# 1RB0LF_1LC0RE_0LD1LC_1LA---_0RB1RA_0LE1LF

bbchallenge id 68184. One of the six-state holdouts whose halting from blank tape is open. Family: **runs of 11010 and 11000 rewritten end to end**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LF |
| B | 1LC | 0RE |
| C | 0LD | 1LC |
| D | 1LA | --- |
| E | 0RB | 1RA |
| F | 0LE | 1LF |

## Status

Open. Lean: only the generated files (halting configurations; no halt in 10^4 steps by the kernel, 10^7 by
`native_decide`). C: no halt in 10^9 steps.

## What it does

At left-end switches the tape is <code>0 (10)^23 (11010)^228 1 10 0 10 (11010)^398 10 10 11010 1 10 0 10 1 10</code> (step 997,741,579); at right-end switches <code>… (11000)^626 1 11000 0000 (11000)^2 1 10</code> after a disordered stretch of 49 cells (step 998,388,962). The two runs of <code>11010</code> at the left (224 + 402, then 228 + 398) add up to the run of <code>11000</code> at the right (626 both times).

Twin: `1RB0LF_1LC0RE_0LD1LC_1LA---_0RB1RA_0LE1LF` and `1RB0LF_1LC0RE_0LD1LC_1LA---_0RB1RA_1LC1LF` behave alike: the first 1,241 side switches (all of the first machine's in 10^9 steps) fall on the same sides with exactly the same widths; the second machine is faster and reaches 1,319 switches in 10^9 steps.

Halting: D on a 1, entered only from C on a 0 (writing 0, moving left): a halt is exactly `1 C>0`.

Growth: 1,241 side switches in 10^9 steps; after 5·10^8 they are ≈ 0.191·w² steps apart and add ≈ 2.6 cells each, so
width ~ t^(1/3) (fitted 0.325; 3,201 cells). `py/shape.py` and `py/switches.py` print all of this from a `tmrun ... records` log.

## Later

1. Find the rule that maps one side switch to the next (sizes of the runs), as was done for the hole-wandering
   machines of this group (e.g. `1RB0LA_0RC---_0RD0RF_1LD0LE_0LA1LE_0RA0LA`), and prove its pieces with `bbtools.symtm`.
2. Show that the halting pattern can never arise from the shapes seen.

## First look

Growth class **power/power** (left: power, exponent 0.323; right: power,
exponent 0.328). After 1,000,000,000 steps: 3,202 cells visited (2,095 left of the
start, 516 right), 1,704 ones.

- left, step 978,902,710: `F>0 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1^2 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 `
- left, step 997,741,574: `F>0 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 `
- right, step 974,788,677: `1 0^11 1 0^3 1 0^7 1 0^7 1^2 0^15 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^`
- right, step 993,628,595: `1 0^11 1 0^3 1 0^3 1 0^15 1 0^7 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 `

## Pages

- [`pages/holdouts/1RB0LF_1LC0RE_0LD1LC_1LA---_0RB1RA_0LE1LF/explainer.html`](../../pages/holdouts/1RB0LF_1LC0RE_0LD1LC_1LA---_0RB1RA_0LE1LF/explainer.html)
- [`pages/holdouts/1RB0LF_1LC0RE_0LD1LC_1LA---_0RB1RA_0LE1LF/proof-status.html`](../../pages/holdouts/1RB0LF_1LC0RE_0LD1LC_1LA---_0RB1RA_0LE1LF/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LF_1LC0RE_0LD1LC_1LA---_0RB1RA_0LE1LF/lean/check.sh
gcc -O2 -o /tmp/tmrun tools/c/tmrun.c && /tmp/tmrun 1RB0LF_1LC0RE_0LD1LC_1LA---_0RB1RA_0LE1LF 1000000000 records 100000 > /tmp/rec.txt
python3 holdouts/1RB0LF_1LC0RE_0LD1LC_1LA---_0RB1RA_0LE1LF/py/shape.py /tmp/rec.txt f=11010,d=11000,a=10
python3 holdouts/1RB0LF_1LC0RE_0LD1LC_1LA---_0RB1RA_0LE1LF/py/switches.py /tmp/rec.txt f=11010,d=11000,a=10
```
