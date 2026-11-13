# 1RB1LE_1RC0RB_1LD1RC_1LA1LE_1LF0LA_1LC---

bbchallenge id 159749. One of the six-state holdouts whose halting from blank tape is open. Its pages are [`pages/holdouts/1RB1LE_1RC0RB_1LD1RC_1LA1LE_1LF0LA_1LC---/explainer.html`](../../pages/holdouts/1RB1LE_1RC0RB_1LD1RC_1LA1LE_1LF0LA_1LC---/explainer.html) and [`pages/holdouts/1RB1LE_1RC0RB_1LD1RC_1LA1LE_1LF0LA_1LC---/proof-status.html`](../../pages/holdouts/1RB1LE_1RC0RB_1LD1RC_1LA1LE_1LF0LA_1LC---/proof-status.html), built from [`status.json`](status.json).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LE |
| B | 1RC | 0RB |
| C | 1LD | 1RC |
| D | 1LA | 1LE |
| E | 1LF | 0LA |
| F | 1LC | --- |

Family: **Up/down two counters with resets (G12 family 3b)**, with [`1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LB`](../1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LB), [`1RB1LC_0RC0RB_1LD0LA_1LE---_1LF1RA_1LA1LC`](../1RB1LC_0RC0RB_1LD0LA_1LE---_1LF1RA_1LA1LC), [`1RB1LD_1RC0RB_1LA1RC_1LE0LA_1LF---_1LC---`](../1RB1LD_1RC0RB_1LA1RC_1LE0LA_1LF---_1LC---), [`1RB1LE_1RC0RB_1RD1LF_1LA0LC_1LD0LA_---0RE`](../1RB1LE_1RC0RB_1RD1LF_1LA0LC_1LD0LA_---0RE). The family's scripts are in [`../1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LB/py`](../1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LB/py) and [`../1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LB/c`](../1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LB/c).

## What it does

Tick configuration `F U 00 F>H V` with top word F = `1` or `1000x` (ticks proved, `lean/Rules.lean`). At V = 0 the tape is clean and the macro state is (H, n, N); `py/rebuild.py` computes the rebuild exactly and adds the next phase's V' ticks by arithmetic; `lean/Rebuild.lean` proves three short rebuild classes for every n. Macro run: 5 rebuilds, ~10^1548 steps, no halt.

## For later

Describe the long rebuild (δ as a function of the digits read) and reduce halting to a condition on δ, as was done for [`1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LB`](../1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LB).

## What is established

**Proved in Lean, kernel only** (`step_none_iff`, `lean/Blank.lean`): The halting configurations. The machine stops exactly when it reads the symbol of a halting transition (F1); the generated statement covers every configuration.

**Proved in Lean, kernel only** (`blank_runs_kernel`, `lean/Blank.lean`): No halt in the first 10,000 steps. The list simulator of the shared library, proved to agree with the machine's semantics, runs 10,000 steps from blank tape without a halt, evaluated by Lean's kernel.

**Proved in Lean, kernel only** (`lean/Rules.lean` (4 theorems)): The tick rules of the two counters. For each of the headers `0110101`, `0110111` the run uses, two theorems: with V odd, `L 00000 (00001)^j 00 F>0110101 01 R` becomes `L 00001 (00000)^j 00 F>0110101 11 R` in 10 * j + 26 steps; with V having i + 1 trailing zeros, `L 00000 (00001)^j 00 F>0110101 (11)^(i+1) 01 R` becomes `L 00001 (00000)^j 00 F>0110101 (01)^(i+1) 11 R` in 4 * i + 10 * j + 30 steps. That is U + 1 and V − 1 for every number j of carries and i + 1 of borrows and every tape L, R beyond (proved along the symbolic run of `tools/py/bbtools/symtm.py`).

**Proved in Lean, kernel only** (`lean/Rebuild.lean` (3 theorems, written by `holdouts/1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LB/py/gen_rebuild_rules.py`)): 3 rebuild rules. For 3 residue classes of the up-counter N modulo 2^j (j in [3, 5], headers `0110111`) the rebuild after V = 0 is proved for every length n of V and every tape L left of the digits it reads: `L d_j-1..d_0 00 F> H (11)^(n+k) 1 0^inf` becomes `L 00 F> H' w (01)^(n+e) 1 0^inf`, that is: the up-counter loses its lowest j digits (N becomes N >> j) and the new down-counter is 2^(n+k+c) − δ with c and δ fixed by the class. For example, header `0110111` and N = 4 (mod 2^3): new header `0110101`, 8 more digits, δ = 349. The classes were found by sampling; each theorem is then proved along the symbolic run of `tools/py/bbtools/symtm.py`.

**Proved in Lean with `native_decide`** (`blank_runs_native`, `lean/Blank.lean`): No halt in the first 10^7 steps. The same run, evaluated by compiled code.

**Computed (trusted C/Python, tested)** (`holdouts/triage.json`): No halt in the first 10^9 steps. The C simulator `tools/c/triage.c` runs 10^9 steps without a halt; at the end 238 cells have been visited and 92 of them hold a 1.

**Computed (trusted C/Python, tested)** (`holdouts/1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LB/py/rebuild.py` (`validate`)): The macro map and its simulator. At each moment V reaches 0 the tape is the clean configuration `0^inf F U 00 F> H (11)^n 1 0^inf` (F the counter's top word), so the state is (H, n, N) with N the up-counter read as one number. `py/rebuild.py` writes that tape, runs the rebuild (tick runs of its sub-phases jumped by the proved tick rules, the rest cell by cell in C) to the next clean tick configuration (H', n', N', V'), and then adds the V' ticks of the phase by arithmetic: next state (H', n', N' + V'), steps by the closed formula of the tick costs. Tested: its first 3 states and step counts, up to about 10^59 steps, equal those of `py/counters.py` (itself tested against `tools/c/tmrun.c`).

**Computed (trusted C/Python, tested)** (`holdouts/1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LB/py/rebuild_stats.py 1RB1LE_1RC0R... run`): No halt in the first 10^1548 steps (macro run). The macro run from blank tape goes through 5 rebuilds without a halt; at the end V has 5,139 digits and the step count is about 10^1548.

**Observed only / heuristic** (`py/rebuild_stats.py 1RB1LE_1RC0R... run`): What the rebuild map looks like in the run. Only 5 rebuilds fit in the 90-second run (header/top word: `0110101/1` 1, `0110111/1` 2, `0110111/1000` 2). The two with top word `1` before the last read all of N but its top two digits and left N' = 2; the last one (new header `0110101`, j = 1315 of 1851 digits) left 536 digits. Too few rebuilds to call any of this a rule; no closed description of δ is known.

**Open**: Does it halt from blank tape? Not known. The macro map on (H, n, N) is computed exactly; its rebuilds have not been described for all N, so neither a non-halting invariant nor a halting run is known. The stopping walk found for `1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LB` (round 3) does not describe this machine's rebuilds: of the 584 rebuilds with N < 2^9 (both headers, n − len(N) + 1 in {0, 1}) on which the walk stops below the top digit, none gives the predicted (header, n', N').

## Reproduce

```sh
. /etc/profile.d/lean.sh      # after scripts/setup-lean.sh
holdouts/1RB1LE_1RC0RB_1LD1RC_1LA1LE_1LF0LA_1LC---/lean/check.sh          # Machine, Blank, Rules (ticks), Rebuild (rebuild rules)
python3 holdouts/1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LB/py/rebuild.py 1RB1LE_1RC0RB_1LD1RC_1LA1LE_1LF0LA_1LC--- validate 120          # macro run = counters.py run, state by state
python3 holdouts/1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LB/py/rebuild_stats.py 1RB1LE_1RC0RB_1LD1RC_1LA1LE_1LF0LA_1LC--- run 1500        # the macro run, one line per rebuild
python3 holdouts/1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LB/py/rebuild_stats.py 1RB1LE_1RC0RB_1LD1RC_1LA1LE_1LF0LA_1LC--- halting 12      # which rebuilds halt, N < 2^12
python3 holdouts/1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LB/py/gen_rebuild_rules.py 1RB1LE_1RC0RB_1LD1RC_1LA1LE_1LF0LA_1LC--- H159749 5 > holdouts/1RB1LE_1RC0RB_1LD1RC_1LA1LE_1LF0LA_1LC---/lean/Rebuild.lean
```
