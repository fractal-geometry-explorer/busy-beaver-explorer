# 1RB0LF_1LC0RE_0LD1LC_1LA---_0RB1RA_1LC1LF

bbchallenge id 124651. One of the six-state holdouts whose halting from blank tape is open. Family: **runs of 11010 and 11000 rewritten end to end**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LF |
| B | 1LC | 0RE |
| C | 0LD | 1LC |
| D | 1LA | --- |
| E | 0RB | 1RA |
| F | 1LC | 1LF |

## Status

Open. Lean: only the generated files (halting configurations; no halt in 10^4 steps by the kernel, 10^7 by
`native_decide`). C: no halt in 10^9 steps.

## What it does

At left-end switches the tape is <code>0 (10)^23 (11010)^306 1 10 0 10 (11010)^359 10 10 11010 1 10 0 10 1 10</code> (step 995,707,723); at right-end switches <code>… (11000)^665 1 11000 0000 (11000)^2 1 10</code> after a disordered stretch of 49 cells (step 996,668,901). The two runs of <code>11010</code> at the left (301 + 362, then 306 + 359) add up to the run of <code>11000</code> at the right (663 + 1 and 665).

Twin: `1RB0LF_1LC0RE_0LD1LC_1LA---_0RB1RA_0LE1LF` and `1RB0LF_1LC0RE_0LD1LC_1LA---_0RB1RA_1LC1LF` behave alike: the first 1,241 side switches (all of the first machine's in 10^9 steps) fall on the same sides with exactly the same widths; the second machine is faster and reaches 1,319 switches in 10^9 steps.

Halting: D on a 1, entered only from C on a 0 (writing 0, moving left): a halt is exactly `1 C>0`.

Growth: 1,319 side switches in 10^9 steps; after 5·10^8 they are ≈ 0.156·w² steps apart and add ≈ 2.5 cells each, so
width ~ t^(1/3) (fitted 0.325; 3,396 cells). `py/shape.py` and `py/switches.py` print all of this from a `tmrun ... records` log.

## Later

1. Find the rule that maps one side switch to the next (sizes of the runs), as was done for the hole-wandering
   machines of this group (e.g. `1RB0LA_0RC---_0RD0RF_1LD0LE_0LA1LE_0RA0LA`), and prove its pieces with `bbtools.symtm`.
2. Show that the halting pattern can never arise from the shapes seen.

## First look

Growth class **power/power** (left: power, exponent 0.324; right: power,
exponent 0.328). After 1,000,000,000 steps: 3,397 cells visited (2,223 left of the
start, 548 right), 1,981 ones.

- left, step 969,291,128: `F>0 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1^2 0 1 0 1 0 1 0 1^2 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 `
- left, step 986,809,686: `F>0 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 `
- right, step 970,074,419: `1 0^7 1 0^15 1 0^7 1^2 0^3 1 0^3 1^2 0^7 1 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0`
- right, step 987,740,239: `1 0^7 1 0^11 1 0^7 1 0^3 1 0^7 1^2 0^3 1 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3 1^2 0^3`

## Pages

- [`pages/holdouts/1RB0LF_1LC0RE_0LD1LC_1LA---_0RB1RA_1LC1LF/explainer.html`](../../pages/holdouts/1RB0LF_1LC0RE_0LD1LC_1LA---_0RB1RA_1LC1LF/explainer.html)
- [`pages/holdouts/1RB0LF_1LC0RE_0LD1LC_1LA---_0RB1RA_1LC1LF/proof-status.html`](../../pages/holdouts/1RB0LF_1LC0RE_0LD1LC_1LA---_0RB1RA_1LC1LF/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LF_1LC0RE_0LD1LC_1LA---_0RB1RA_1LC1LF/lean/check.sh
gcc -O2 -o /tmp/tmrun tools/c/tmrun.c && /tmp/tmrun 1RB0LF_1LC0RE_0LD1LC_1LA---_0RB1RA_1LC1LF 1000000000 records 100000 > /tmp/rec.txt
python3 holdouts/1RB0LF_1LC0RE_0LD1LC_1LA---_0RB1RA_1LC1LF/py/shape.py /tmp/rec.txt f=11010,d=11000,a=10
python3 holdouts/1RB0LF_1LC0RE_0LD1LC_1LA---_0RB1RA_1LC1LF/py/switches.py /tmp/rec.txt f=11010,d=11000,a=10
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same tapes at another pace (observed, not proved).** Leave the states aside and compare only the tape and the place of the head. Then a large part of the first 10^7 configurations of this machine are configurations of the machines below, in the same order and up to the end of the run. The steps at which they occur differ, the tables are not renamings of each other, and equal tapes with different states may be continued differently, so this does not tie the halting questions together.

- [`1RB0LF_1LC0RE_0LD1LC_1LA---_0RB1RA_0LE1LF`](../1RB0LF_1LC0RE_0LD1LC_1LA---_0RB1RA_0LE1LF/README.md): 8,345,589 configurations, the last at step 8,345,588 here and step 10,000,000 there

<!-- end of related machines -->
