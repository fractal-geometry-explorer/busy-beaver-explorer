# 1RB1LD_1LC0RD_0LA0RB_0LE1LF_1RF0LC_0RB---

bbchallenge id 11545. One of the six-state holdouts whose halting from blank tape is open. Family: **irregular word with a slowly growing left prefix (structure not found)**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LD |
| B | 1LC | 0RD |
| C | 0LA | 0RB |
| D | 0LE | 1LF |
| E | 1RF | 0LC |
| F | 0RB | --- |

## What it does

Each time the head reaches a new cell at the left end it is in state C and the tape reads
`C>0 0^2 1 0 (1^2 0)^m V`, with V a word of the tokens `1 0`, `1^2 0` and `0^3 1`; two more cells follow within 12
steps. m goes up and down (it fell 14 times in 10^11 steps), and V changes along its whole length between extensions.
The last seven extensions came at 1.5, 3.2, 8.1, 23, 36, 43 and 65 billion steps (ratios 1.2 to 2.8), so this is not
a binary counter. The machine halts only in state F reading a 1.

## What is established

**Proved in Lean, kernel only** (`lean/Blank.lean`): the halting configurations (`step_none_iff`); no halt in 10,000
steps (`blank_runs_kernel`).

**Proved in Lean with `native_decide`**: no halt in 10^7 steps (`blank_runs_native`).

**Computed** (trusted C): no halt in 10^11 steps (`tools/c/tmrun.c`; 262 cells, 203 left and 59 right of the start,
115 ones). All 61 left extensions have the shape above.

**Heuristic**: the width grows like the logarithm of the step count, at irregular times.

**Open**: what V encodes, when the left end moves, and the question.

The closed-tape-language search (`bbtools.ctl`, K up to 6, and K = 8 on the mirrored machine) finds no closed set, so
the halt is not confined to an edge.

## For later

* Test whether the tokens `1 0`, `1^2 0`, `0^3 1` are digits of a number (a base-3 or Fibonacci-like reading)
  and the extensions are carries, by decoding V at each extension and looking for an arithmetic relation.
* Record the configurations each time the head returns to the left prefix, not only at new cells, to find a
  finer event with a regular rule.

## Layout

| path | what it is |
|---|---|
| `lean/Machine.lean`, `lean/Blank.lean` | the machine, the halting configurations and bounded runs (generated) |

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LD_1LC0RD_0LA0RB_0LE1LF_1RF0LC_0RB---/lean/check.sh
gcc -O2 -o tmrun tools/c/tmrun.c && ./tmrun 1RB1LD_1LC0RD_0LA0RB_0LE1LF_1RF0LC_0RB--- 100000000000 records 100000
```

## Pages

- [`pages/holdouts/1RB1LD_1LC0RD_0LA0RB_0LE1LF_1RF0LC_0RB---/explainer.html`](../../pages/holdouts/1RB1LD_1LC0RD_0LA0RB_0LE1LF_1RF0LC_0RB---/explainer.html)
- [`pages/holdouts/1RB1LD_1LC0RD_0LA0RB_0LE1LF_1RF0LC_0RB---/proof-status.html`](../../pages/holdouts/1RB1LD_1LC0RD_0LA0RB_0LE1LF_1RF0LC_0RB---/proof-status.html)
