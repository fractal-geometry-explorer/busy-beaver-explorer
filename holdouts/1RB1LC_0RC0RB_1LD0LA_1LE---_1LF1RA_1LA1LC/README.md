# 1RB1LC_0RC0RB_1LD0LA_1LE---_1LF1RA_1LA1LC

bbchallenge id 15053. One of the six-state holdouts whose halting from blank tape is open. Its pages are [`pages/holdouts/1RB1LC_0RC0RB_1LD0LA_1LE---_1LF1RA_1LA1LC/explainer.html`](../../pages/holdouts/1RB1LC_0RC0RB_1LD0LA_1LE---_1LF1RA_1LA1LC/explainer.html) and [`pages/holdouts/1RB1LC_0RC0RB_1LD0LA_1LE---_1LF1RA_1LA1LC/proof-status.html`](../../pages/holdouts/1RB1LC_0RC0RB_1LD0LA_1LE---_1LF1RA_1LA1LC/proof-status.html), built from [`status.json`](status.json).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LC |
| B | 0RC | 0RB |
| C | 1LD | 0LA |
| D | 1LE | --- |
| E | 1LF | 1RA |
| F | 1LA | 1LC |

Family: **Up/down two counters with resets (G12 family 3b)**, with [`1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LB`](../1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LB), [`1RB1LD_1RC0RB_1LA1RC_1LE0LA_1LF---_1LC---`](../1RB1LD_1RC0RB_1LA1RC_1LE0LA_1LF---_1LC---), [`1RB1LE_1RC0RB_1LD1RC_1LA1LE_1LF0LA_1LC---`](../1RB1LE_1RC0RB_1LD1RC_1LA1LE_1LF0LA_1LC---), [`1RB1LE_1RC0RB_1RD1LF_1LA0LC_1LD0LA_---0RE`](../1RB1LE_1RC0RB_1RD1LF_1LA0LC_1LD0LA_---0RE). The family's scripts are in [`../1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LB/py`](../1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LB/py) and [`../1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LB/c`](../1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LB/c).

## What it does

Tick configuration `F U 00 D>H V` with top word F = `1` or `1000x` (ticks proved, `lean/Rules.lean`). At V = 0 the tape is clean and the macro state is (H, n, N); the rebuild is computed exactly (`rebuild.py` of the family, or the faster `py/fastrebuild.py`), and the next phase's V' ticks are added by arithmetic. The rebuilds come in four kinds by header and top word: A (`0110101`/`1`) complements the counter (δ = 2^L − U); C (`0110111`/`1`) reads the j digits of a walk over pairs and then complements the rest; B (`0110111`/`1000x`) and D (`0110101`/`1000x`) read every digit and leave N' = 2. The same walk decides the halts: a B rebuild, or a D rebuild with n = L + 1 and L even, halts exactly when the walk does not stop below the top of the counter (checked for L ≤ 9). Macro run: 9 rebuilds, ~10^9624 steps, no halt.

## For later

Write the constant c of the C rebuilds as a formula (it depends only on the digits the walk reads) and describe δ of B and D the same way; then the macro map is closed and halting is the question whether a B or D counter ever has no 1 in the upper place of a pair, the invariant busycoq PR 58 proves in Rocq.

## What is established

**Proved in Lean, kernel only** (`step_none_iff`, `lean/Blank.lean`): The halting configurations. The machine stops exactly when it reads the symbol of a halting transition (D1); the generated statement covers every configuration.

**Proved in Lean, kernel only** (`blank_runs_kernel`, `lean/Blank.lean`): No halt in the first 10,000 steps. The list simulator of the shared library, proved to agree with the machine's semantics, runs 10,000 steps from blank tape without a halt, evaluated by Lean's kernel.

**Proved in Lean, kernel only** (`lean/Rules.lean` (4 theorems)): The tick rules of the two counters. For each of the headers `0110101`, `0110111` the run uses, two theorems: with V odd, `L 00000 (00001)^j 00 D>0110101 01 R` becomes `L 00001 (00000)^j 00 D>0110101 11 R` in 10 * j + 38 steps; with V having i + 1 trailing zeros, `L 00000 (00001)^j 00 D>0110101 (11)^(i+1) 01 R` becomes `L 00001 (00000)^j 00 D>0110101 (01)^(i+1) 11 R` in 8 * i + 10 * j + 46 steps. That is U + 1 and V − 1 for every number j of carries and i + 1 of borrows and every tape L, R beyond (proved along the symbolic run of `tools/py/bbtools/symtm.py`).

**Proved in Lean with `native_decide`** (`blank_runs_native`, `lean/Blank.lean`): No halt in the first 10^7 steps. The same run, evaluated by compiled code.

**Computed (trusted C/Python, tested)** (`holdouts/triage.json`): No halt in the first 10^9 steps. The C simulator `tools/c/triage.c` runs 10^9 steps without a halt; at the end 178 cells have been visited and 50 of them hold a 1.

**Computed (trusted C/Python, tested)** (`holdouts/1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LB/py/rebuild.py` (`validate`)): The macro map and its simulator. At each moment V reaches 0 the tape is the clean configuration `0^inf F U 00 D> H (11)^n 1 0^inf` (F the counter's top word), so the state is (H, n, N) with N the up-counter read as one number. `py/rebuild.py` writes that tape, runs the rebuild (tick runs of its sub-phases jumped by the proved tick rules, the rest cell by cell in C) to the next clean tick configuration (H', n', N', V'), and then adds the V' ticks of the phase by arithmetic: next state (H', n', N' + V'), steps by the closed formula of the tick costs. Tested: its first 4 states and step counts, up to about 10^54 steps, equal those of `py/counters.py` (itself tested against `tools/c/tmrun.c`).

**Computed (trusted C/Python, tested)** (`py/fastrebuild.py speed 7`, `c/stops.c`): A faster exact rebuild. `py/fastrebuild.py` runs the same exact rebuild as `rebuild.py` (tick runs jumped by the proved tick rules, the rest cell by cell), but its C loop stops only where state D reads 0 between the gap and one of the two headers, instead of at each of the millions of 0s it reads in state D, and it decodes and rewrites the counters with byte slices. Rebuild 6 from blank tape (V of 2,176 digits) took more than 25 minutes and takes 4 s. Tested: the first 7 macro states from blank tape (to about 10^991 steps) equal those of the family's own code, state by state.

**Computed (trusted C/Python, tested)** (`py/fastrebuild.py run`): No halt in the first 10^9624 steps (macro run). The macro run from blank tape goes through 9 rebuilds without a halt; at the end V has 31,967 digits and the step count is about 10^9624. The run uses the faster exact rebuild below (rebuild 8 takes 18 s).

**Computed (trusted C/Python, tested)** (`py/fastrebuild.py kinds 10`): Four kinds of rebuild, two of them in closed form. Write the counter as its top word (`1` or `1000x`) and L digits U. **A** (header `0110101`, top `1`) reads every digit: new header `0110111`, top `10000`, all L digits 0, V gains 1 digit, and δ = 2^L − U, so V' = 2^n+1 − 2^L + U. **C** (header `0110111`, top `1`) reads the j digits of a walk from the bottom: a first pair 01 or 10 stops it (j = 2); otherwise add 1 to U if its lowest pair is 11 and stop at the first pair whose upper digit is 1 (j = 2k). Then the new header is `0110101`, the top `10000` over L − j zero digits, V gains 5j/2 + 1 digits and δ = c + 2^L−j − (U >> j), with c depending only on the j digits read (U >> j > 0). **B** (header `0110111`, top `1000x`) and **D** (header `0110101`, top `1000x`) read every digit and leave N' = 2. Checked against the exact rebuild: A and C for every U < 2^10 with n − L in {0, 1, 3}; in the run, A twice and C three times (walks of 34, 444 and 8,182 digits), all as stated.

**Computed (trusted C/Python, tested)** (`py/fastrebuild.py halting 9`): Where the rebuilds halt: the walk runs off the top. For every U < 2^L, L = 3 .. 9, both values of x and n − L in {0, 1, 2, 3} (112 cases): B halts exactly for the U whose walk (the one of C) does not stop below the top of U (the all-ones U aside), when x = 0 or L is even, and never when x = 1 and L is odd; D never halts when n − L ≥ 2, and with n − L = 1 halts exactly where B does when L is even and never when L is odd. A never halts (every U < 2^10), nor did C for any U < 2^14 with n = L + 1. (D with n − L = 0 has other halting sets; no D rebuild of the run has n = L.) So the run halts only at a B or D rebuild whose counter has no 1 in the upper place of any pair, after the walk's carry. That is the invariant of the outside proof: busycoq PR 58's walls carry `marked 1 bs`, a 1 at an odd position of the digits.

**Observed only / heuristic** (`py/fastrebuild.py run`): The walks in the run. The kinds follow each other as A, B, C, D, then A or C again (D went to A once and to C once). The two B rebuilds of the run stopped their walk after 12 of 23 and 444 of 619 digits; the D rebuild with n − L = 1 (L = 3,286, even) after 16. A halt needs a walk that runs off the top, which for random digits has probability about 2^−L/2, and L grows about threefold per rebuild. A heuristic only, now superseded by the outside proof.

**Open**: Does it halt from blank tape? Not decided by this repository (the outside Rocq proof of busycoq PR 58 decides it). The kinds A and C are in closed form apart from the constant c of C, and the halting rebuilds are described for small counters; what is missing here is c as a formula, the maps of B and D, and a proof of any of it in Lean.

## Reproduce

```sh
. /etc/profile.d/lean.sh      # after scripts/setup-lean.sh
holdouts/1RB1LC_0RC0RB_1LD0LA_1LE---_1LF1RA_1LA1LC/lean/check.sh          # Machine, Blank, Rules (ticks)
python3 holdouts/1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LB/py/rebuild.py 1RB1LC_0RC0RB_1LD0LA_1LE---_1LF1RA_1LA1LC validate 120          # macro run = counters.py run, state by state
python3 holdouts/1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LB/py/rebuild_stats.py 1RB1LC_0RC0RB_1LD0LA_1LE---_1LF1RA_1LA1LC halting 12      # which rebuilds halt, N < 2^12
python3 holdouts/1RB1LC_0RC0RB_1LD0LA_1LE---_1LF1RA_1LA1LC/py/fastrebuild.py speed 7     # the faster rebuild = the family's, state by state (30 min, most of it the old code)
python3 holdouts/1RB1LC_0RC0RB_1LD0LA_1LE---_1LF1RA_1LA1LC/py/fastrebuild.py run 600     # the macro run, one line per rebuild
python3 holdouts/1RB1LC_0RC0RB_1LD0LA_1LE---_1LF1RA_1LA1LC/py/fastrebuild.py kinds 10    # the formulas of A and C, every U < 2^10
python3 holdouts/1RB1LC_0RC0RB_1LD0LA_1LE---_1LF1RA_1LA1LC/py/fastrebuild.py halting 9   # halting B and D rebuilds = the walk off the top, L <= 9
```
