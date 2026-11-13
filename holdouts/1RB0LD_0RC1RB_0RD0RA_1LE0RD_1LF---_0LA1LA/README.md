# 1RB0LD_0RC1RB_0RD0RA_1LE0RD_1LF---_0LA1LA

bbchallenge id 12891. One of the six-state holdouts whose halting from blank tape is open. Family: **two long blocks of 1s, regrown from one end**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LD |
| B | 0RC | 1RB |
| C | 0RD | 0RA |
| D | 1LE | 0RD |
| E | 1LF | --- |
| F | 0LA | 1LA |

## Status

Open. Lean: only the generated files (halting configurations; no halt in 10^4 steps by the kernel, 10^7 by
`native_decide`). C: no halt in 10^9 steps.

## What it does

At left-end switches the tape is `0 0 1^x 0 1^y 0 1 1` (1428/2925, 3993/327, 1374/2907 near 10^9); at right-end
switches `1^4 0^u 1^v 0 0 1 1 1 0` (3828/493, 4043/244). The sizes are erratic.

Halting: E on a 1, entered only from D on a 0 (writing 1, moving left): a halt is exactly `1 D>0`.

Growth: 474 side switches in 10^9 steps; after 5·10^8 they are ≈ 0.246·w² steps apart and add ≈ 8 cells each, so
width ~ t^(1/3) (fitted 0.327; 4,362 cells). `py/shape.py` and `py/switches.py` print all of this from a `tmrun ... records` log.

## Later

1. Find the rule that maps one side switch to the next (sizes of the runs), as was done for the hole-wandering
   machines of this group (e.g. `1RB0LA_0RC---_0RD0RF_1LD0LE_0LA1LE_0RA0LA`), and prove its pieces with `bbtools.symtm`.
2. Show that the halting pattern can never arise from the shapes seen.

## First look

Growth class **power/power** (left: power, exponent 0.34; right: power,
exponent 0.32). After 1,000,000,000 steps: 4,363 cells visited (1,385 left of the
start, 2,198 right), 4,240 ones.

- left, step 966,244,023: `D>0 0 1^4125 0 1^161 0 1^2`
- left, step 993,152,325: `D>0 0 1^1428 0 1^2925 0 1^2`
- right, step 957,843,818: `1^4 0^458 1^3814 0^2 1^3 B>0`
- right, step 980,513,054: `1^4 0^3828 1^493 0^2 1^3 B>0`

## Pages

- [`pages/holdouts/1RB0LD_0RC1RB_0RD0RA_1LE0RD_1LF---_0LA1LA/explainer.html`](../../pages/holdouts/1RB0LD_0RC1RB_0RD0RA_1LE0RD_1LF---_0LA1LA/explainer.html)
- [`pages/holdouts/1RB0LD_0RC1RB_0RD0RA_1LE0RD_1LF---_0LA1LA/proof-status.html`](../../pages/holdouts/1RB0LD_0RC1RB_0RD0RA_1LE0RD_1LF---_0LA1LA/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LD_0RC1RB_0RD0RA_1LE0RD_1LF---_0LA1LA/lean/check.sh
gcc -O2 -o /tmp/tmrun tools/c/tmrun.c && /tmp/tmrun 1RB0LD_0RC1RB_0RD0RA_1LE0RD_1LF---_0LA1LA 1000000000 records 100000 > /tmp/rec.txt
python3 holdouts/1RB0LD_0RC1RB_0RD0RA_1LE0RD_1LF---_0LA1LA/py/shape.py /tmp/rec.txt a=10
python3 holdouts/1RB0LD_0RC1RB_0RD0RA_1LE0RD_1LF---_0LA1LA/py/switches.py /tmp/rec.txt a=10
```
