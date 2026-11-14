# 1RB0LC_1LC0RE_1LD1LC_1LA1RD_1RF1RB_---0RB

bbchallenge id 110453. One of the six-state holdouts whose halting from blank tape is open. Family: **blocks of 1s split in halves and thirds**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LC |
| B | 1LC | 0RE |
| C | 1LD | 1LC |
| D | 1LA | 1RD |
| E | 1RF | 1RB |
| F | --- | 0RB |

## Status

Open. Lean: only the generated files (halting configurations; no halt in 10^4 steps by the kernel, 10^7 by
`native_decide`). C: no halt in 10^9 steps.

## What it does

At the left end the tape is two to four blocks of 1s split by single 0s, with lengths cut in halves and
thirds from one trip to the next (`0 1^1318 0 1^1975 0 1^655`, `0 1^661 0 1^2312 0 1^989`, `0 1^332 0 1^1489 0 1^1652 0 1^494`,
`0 1^2651 0 1^1323`). At the right end it is an alternating stretch then a solid block (`(10)^1333 1^1336 0`).

Halting: F on a 0, entered only from E on a 0 moving right: a halt is exactly `E>0 0` (equivalently `B>1 0 0`).

Growth: 1,401 side switches in 10^9 steps; after 5·10^8 they are ≈ 0.107·w² steps apart and add ≈ 2.9 cells each, so
width ~ t^(1/3) (fitted 0.335; 4,002 cells). `py/shape.py` and `py/switches.py` print all of this from a `tmrun ... records` log.

## Later

1. Find the rule that maps one side switch to the next (sizes of the runs), as was done for the hole-wandering
   machines of this group (e.g. `1RB0LA_0RC---_0RD0RF_1LD0LE_0LA1LE_0RA0LA`), and prove its pieces with `bbtools.symtm`.
2. Show that the halting pattern can never arise from the shapes seen.

## First look

Growth class **power/power** (left: power, exponent 0.336; right: power,
exponent 0.334). After 1,000,000,000 steps: 4,003 cells visited (2,433 left of the
start, 813 right), 2,945 ones.

- left, step 974,655,988: `C>0 1^332 0 1^1489 0 1^1652 0 1^493`
- left, step 993,844,057: `C>0 1^2662 0 1^1332`
- right, step 970,224,729: `1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 `
- right, step 988,521,386: `1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 `

## Pages

- [`pages/holdouts/1RB0LC_1LC0RE_1LD1LC_1LA1RD_1RF1RB_---0RB/explainer.html`](../../pages/holdouts/1RB0LC_1LC0RE_1LD1LC_1LA1RD_1RF1RB_---0RB/explainer.html)
- [`pages/holdouts/1RB0LC_1LC0RE_1LD1LC_1LA1RD_1RF1RB_---0RB/proof-status.html`](../../pages/holdouts/1RB0LC_1LC0RE_1LD1LC_1LA1RD_1RF1RB_---0RB/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LC_1LC0RE_1LD1LC_1LA1RD_1RF1RB_---0RB/lean/check.sh
gcc -O2 -o /tmp/tmrun tools/c/tmrun.c && /tmp/tmrun 1RB0LC_1LC0RE_1LD1LC_1LA1RD_1RF1RB_---0RB 1000000000 records 100000 > /tmp/rec.txt
python3 holdouts/1RB0LC_1LC0RE_1LD1LC_1LA1RD_1RF1RB_---0RB/py/shape.py /tmp/rec.txt a=10
python3 holdouts/1RB0LC_1LC0RE_1LD1LC_1LA1RD_1RF1RB_---0RB/py/switches.py /tmp/rec.txt a=10
```

## Accelerated run

Trusted computation: `python3 tools/py/bbtools/rleaccel.py 1RB0LC_1LC0RE_1LD1LC_1LA1RD_1RF1RB_---0RB 2 2048000000` runs 2,048,000,000 macro steps from blank tape without a halt, more than 2.52·10^23
machine steps (tape: 253,079,042 cells). The simulator codes the tape in runs, crosses a run in one step and jumps cycles whose
one-cycle rule it has first proved symbolically; it is tested cell for cell against direct runs
(`tools/tests/test_rleaccel.py`).
