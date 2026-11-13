# 1RB0LC_1RC0RF_1LA0LD_0LE0RA_0RB1LD_0LA---

bbchallenge id 101586. One of the six-state holdouts whose halting from blank tape is open. Family: **alternating stretch cut by marker 1s**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LC |
| B | 1RC | 0RF |
| C | 1LA | 0LD |
| D | 0LE | 0RA |
| E | 0RB | 1LD |
| F | 0LA | --- |

## Status

Open. Lean: only the generated files (halting configurations; no halt in 10^4 steps by the kernel, 10^7 by
`native_decide`). C: no halt in 10^9 steps.

## What it does

The tape is an alternating stretch `(10)^n` with one or two marker 1s cutting it into near-equal pieces:
`1 (10)^1776`, `1 (10)^890 1 (10)^888`, `1 (10)^665 1 (10)^662 1 (10)^441` at right-end switches near 10^9.

Halting: F on a 1, entered only from B on a 1 moving right: a halt is exactly `B>1 1`.

Growth: 1,477 side switches in 10^9 steps; after 5·10^8 they are ≈ 0.129·w² steps apart and add ≈ 2.4 cells each, so
width ~ t^(1/3) (fitted 0.337; 3,558 cells). `py/shape.py` and `py/switches.py` print all of this from a `tmrun ... records` log.

## Later

1. Find the rule that maps one side switch to the next (sizes of the runs), as was done for the hole-wandering
   machines of this group (e.g. `1RB0LA_0RC---_0RD0RF_1LD0LE_0LA1LE_0RA0LA`), and prove its pieces with `bbtools.symtm`.
2. Show that the halting pattern can never arise from the shapes seen.

## First look

Growth class **power/power** (left: power, exponent 0.336; right: power,
exponent 0.335). After 1,000,000,000 steps: 3,559 cells visited (1,271 left of the
start, 1,624 right), 1,781 ones.

- left, step 973,511,507: `A>0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 `
- left, step 991,833,867: `D>0 0^2 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 `
- right, step 966,382,261: `1^2 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 `
- right, step 985,702,735: `1^2 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 `

## Pages

- [`pages/holdouts/1RB0LC_1RC0RF_1LA0LD_0LE0RA_0RB1LD_0LA---/explainer.html`](../../pages/holdouts/1RB0LC_1RC0RF_1LA0LD_0LE0RA_0RB1LD_0LA---/explainer.html)
- [`pages/holdouts/1RB0LC_1RC0RF_1LA0LD_0LE0RA_0RB1LD_0LA---/proof-status.html`](../../pages/holdouts/1RB0LC_1RC0RF_1LA0LD_0LE0RA_0RB1LD_0LA---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LC_1RC0RF_1LA0LD_0LE0RA_0RB1LD_0LA---/lean/check.sh
gcc -O2 -o /tmp/tmrun tools/c/tmrun.c && /tmp/tmrun 1RB0LC_1RC0RF_1LA0LD_0LE0RA_0RB1LD_0LA--- 1000000000 records 100000 > /tmp/rec.txt
python3 holdouts/1RB0LC_1RC0RF_1LA0LD_0LE0RA_0RB1LD_0LA---/py/shape.py /tmp/rec.txt a=10
python3 holdouts/1RB0LC_1RC0RF_1LA0LD_0LE0RA_0RB1LD_0LA---/py/switches.py /tmp/rec.txt a=10
```

## Accelerated run

Trusted computation: `python3 tools/py/bbtools/rleaccel.py 1RB0LC_1RC0RF_1LA0LD_0LE0RA_0RB1LD_0LA--- 6 173000000` runs 173,000,000 macro steps from blank tape without a halt, more than 2.25·10^11
machine steps (tape: 21,666 cells). The simulator codes the tape in runs, crosses a run in one step and jumps cycles whose
one-cycle rule it has first proved symbolically; it is tested cell for cell against direct runs
(`tools/tests/test_rleaccel.py`).
