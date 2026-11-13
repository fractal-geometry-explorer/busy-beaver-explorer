# 1RB1RA_1LC1LE_1RA1LD_0LB0LC_1LF0RE_1LB---

bbchallenge id 9074. One of the six-state holdouts whose halting from blank tape is open. Family: **counter in a unary block, sweeping a change through a word**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RA |
| B | 1LC | 1LE |
| C | 1RA | 1LD |
| D | 0LB | 0LC |
| E | 1LF | 0RE |
| F | 1LB | --- |

## What it does

At each overflow the tape reads `C>0 1 0 1^(4j+1) 0 W` with the head at the left end. Since the last restructure, at
step 1,354,998, j has grown by one per overflow, 30 times, to `1^125` at step 73,018,175,570, and the gap between
overflows has doubled (ratio 2.0000 at the last 15). W is a word of blocks `1`, `1^5`, `1^9` (54 to 56 blocks); each
overflow changes it only from some block on, and that block has moved right from 0 to 50 (0 to 6 blocks per overflow).
Earlier restructures, where the left block fell back to `1^5` and W was rewritten, came at steps 1,525, 4,520,
166,083 and 1,354,998. The machine halts only in state F reading a 1.

## What is established

**Proved in Lean, kernel only** (`lean/Blank.lean`): the halting configurations (`step_none_iff`); no halt in 10,000
steps (`blank_runs_kernel`).

**Proved in Lean with `native_decide`**: no halt in 10^7 steps (`blank_runs_native`).

**Computed** (trusted C): no halt in 10^11 steps (`tools/c/tmrun.c`; 313 cells, 162 ones). The 65 overflow moments,
the restructure times and the sweep above.

**Heuristic**: if an epoch ends when the sweep reaches the end of W, a restructure is due within two or three
overflows; reading W as a number N, N changes by roughly
3·4^(j-1) per overflow, but the rule fails from constructed tapes with arbitrary low digits.

**Open**: the per-overflow rule for W, the restructure rule, and the question.

A left-edge closed tape language built from the Python `bbtools.ctl` listing (mirrored machine) failed Lean's
`haltsLeftBlank` check, so no edge theorem is claimed; those files were removed.

## For later

* Run past 10^11 steps (about 3·10^11 should suffice) to see the next restructure and the word it writes.
* Decode the per-overflow change of W at the sweep point: it touches only a few blocks, so a local rule may exist even
  though the global arithmetic one fails.
* Retry an edge certificate with larger windows, checking each candidate in Lean (the Python listing of halting
  windows is not complete).

## Layout

| path | what it is |
|---|---|
| `lean/Machine.lean`, `lean/Blank.lean` | the machine, the halting configurations and bounded runs (generated) |

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RA_1LC1LE_1RA1LD_0LB0LC_1LF0RE_1LB---/lean/check.sh
gcc -O2 -o tmrun tools/c/tmrun.c && ./tmrun 1RB1RA_1LC1LE_1RA1LD_0LB0LC_1LF0RE_1LB--- 100000000000 records 100000
```

## Pages

- [`pages/holdouts/1RB1RA_1LC1LE_1RA1LD_0LB0LC_1LF0RE_1LB---/explainer.html`](../../pages/holdouts/1RB1RA_1LC1LE_1RA1LD_0LB0LC_1LF0RE_1LB---/explainer.html)
- [`pages/holdouts/1RB1RA_1LC1LE_1RA1LD_0LB0LC_1LF0RE_1LB---/proof-status.html`](../../pages/holdouts/1RB1RA_1LC1LE_1RA1LD_0LB0LC_1LF0RE_1LB---/proof-status.html)
