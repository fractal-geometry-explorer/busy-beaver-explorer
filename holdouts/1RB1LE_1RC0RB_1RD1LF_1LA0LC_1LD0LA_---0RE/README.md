# 1RB1LE_1RC0RB_1RD1LF_1LA0LC_1LD0LA_---0RE

bbchallenge id 14216. One of the six-state holdouts whose halting from blank tape is open. Its pages are [`pages/holdouts/1RB1LE_1RC0RB_1RD1LF_1LA0LC_1LD0LA_---0RE/explainer.html`](../../pages/holdouts/1RB1LE_1RC0RB_1RD1LF_1LA0LC_1LD0LA_---0RE/explainer.html) and [`pages/holdouts/1RB1LE_1RC0RB_1RD1LF_1LA0LC_1LD0LA_---0RE/proof-status.html`](../../pages/holdouts/1RB1LE_1RC0RB_1RD1LF_1LA0LC_1LD0LA_---0RE/proof-status.html), built from [`status.json`](status.json).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LE |
| B | 1RC | 0RB |
| C | 1RD | 1LF |
| D | 1LA | 0LC |
| E | 1LD | 0LA |
| F | --- | 0RE |

Family: **Up/down two counters with resets (G12 family 3b)**, with [`1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LB`](../1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LB), [`1RB1LC_0RC0RB_1LD0LA_1LE---_1LF1RA_1LA1LC`](../1RB1LC_0RC0RB_1LD0LA_1LE---_1LF1RA_1LA1LC), [`1RB1LD_1RC0RB_1LA1RC_1LE0LA_1LF---_1LC---`](../1RB1LD_1RC0RB_1LA1RC_1LE0LA_1LF---_1LC---), [`1RB1LE_1RC0RB_1LD1RC_1LA1LE_1LF0LA_1LC---`](../1RB1LE_1RC0RB_1LD1RC_1LA1LE_1LF0LA_1LC---). The family's scripts are in [`../1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LB/py`](../1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LB/py) and [`../1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LB/c`](../1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LB/c).

## What it does

Tick configuration `U 0 D>H V`, U in 3-cell digits (`000` = 0, `100` = 1), V in pairs (ticks proved, `lean/Rules.lean`; whole phases, `lean/Phase.lean`). At V = 0 the tape is clean and the macro state is (H, n, N) with H = `0110101 a 1 b 1`. a = 0: copy, N -> N + 2^(n+1), n -> n + 1, a := 1. a = 1: eat s digits (s even, by the walk in `py/map.py`), n -> n' = n + 3s/2 + 1, N -> 2^n' + (N >> s) − δ, new flags either way. Macro run: 293 rebuilds, ~10^465 steps, no halt.

## For later

1. Write δ and the new flags of an eat step as functions of the digits read (the scratch data `/home/user/g12/work3/r5s/m4d_12_*.pkl` and `m4map.py` have them for N < 2^12), then prove copy and eat in Lean on top of `lean/Phase.lean` as for the sibling [`1RB1LD_1RC0RB_1LA1RC_1LE0LA_1LF---_1LC---`](../1RB1LD_1RC0RB_1LA1RC_1LE0LA_1LF---_1LC---).
2. Non-halting needs an invariant of the block stack; see the sibling's README for what was tried and why the wall invariant of busycoq PRs #57/#58 does not carry over.
3. busycoq `Eqv_v3.v` TM411 ties this machine to `1RB1LE_1RC0RB_1RD0LF_1LA0LC_1LD0LA_---1RB`: a proof for either settles both.

## What is established

**Proved in Lean, kernel only** (`step_none_iff`, `lean/Blank.lean`): The halting configurations. The machine stops exactly when it reads the symbol of a halting transition (F0); the generated statement covers every configuration.

**Proved in Lean, kernel only** (`blank_runs_kernel`, `lean/Blank.lean`): No halt in the first 10,000 steps. The list simulator of the shared library, proved to agree with the machine's semantics, runs 10,000 steps from blank tape without a halt, evaluated by Lean's kernel.

**Proved in Lean, kernel only** (`lean/Rules.lean` (8 theorems)): The tick rules of the two counters. For each of the headers `01101010101`, `01101010111`, `01101011101`, `01101011111` the run uses, two theorems: with V odd, `L 000 (100)^j 0 D>01101010101 01 R` becomes `L 100 (000)^j 0 D>01101010101 11 R` in 6 * j + 146 steps; with V having i + 1 trailing zeros, `L 000 (100)^j 0 D>01101010101 (11)^(i+1) 01 R` becomes `L 100 (000)^j 0 D>01101010101 (01)^(i+1) 11 R` in 16 * i + 6 * j + 162 steps. That is U + 1 and V − 1 for every number j of carries and i + 1 of borrows and every tape L, R beyond (proved along the symbolic run of `tools/py/bbtools/symtm.py`).

**Proved in Lean, kernel only** (`tick`, `phase`, `phase_to_zero`, `lean/Phase.lean` (written by `holdouts/1RB1LC_0RC0RB_1LD0LA_1LE---_1LF1RA_1LA1LC/py/gen_phase.py`)): A whole run of ticks, for any counters. Three statements about the tick configuration (up-counter U, gap, header, down-counter V, anything beyond), for counters given as arbitrary lists of binary digits rather than one pattern at a time. `tick`: if U is not all ones and V is not zero, the machine reaches the same configuration with U + 1 and V − 1. `phase`: for every k up to the value of V for which U + k still fits in U's digits, it reaches the configuration with U + k and V − k, the widths unchanged, without reading anything beyond the two counters. `phase_to_zero`: in particular, if U + V fits, V is counted down to 0 and U has gained exactly V. This is the step 'then add the V ticks by arithmetic' of the macro map, now a theorem; the macro simulator itself is still trusted code.

**Proved in Lean with `native_decide`** (`blank_runs_native`, `lean/Blank.lean`): No halt in the first 10^7 steps. The same run, evaluated by compiled code.

**Computed (trusted C/Python, tested)** (`holdouts/triage.json`): No halt in the first 10^9 steps. The C simulator `tools/c/triage.c` runs 10^9 steps without a halt; at the end 130 cells have been visited and 61 of them hold a 1.

**Computed (trusted C/Python, tested)** (`holdouts/1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LB/py/rebuild.py` (`validate`)): The macro map and its simulator. At each moment V reaches 0 the tape is the clean configuration `0^inf F U 0 D> H (11)^n 1 0^inf` (F the counter's top word), so the state is (H, n, N) with N the up-counter read as one number. `py/rebuild.py` writes that tape, runs the rebuild (tick runs of its sub-phases jumped by the proved tick rules, the rest cell by cell in C) to the next clean tick configuration (H', n', N', V'), and then adds the V' ticks of the phase by arithmetic: next state (H', n', N' + V'), steps by the closed formula of the tick costs. Tested: its first 397 states and step counts, up to about 10^630 steps, equal those of `py/counters.py` (itself tested against `tools/c/tmrun.c`).

**Computed (trusted C/Python, tested)** (`holdouts/1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LB/py/rebuild_stats.py 1RB1LE_1RC0R... run`): No halt in the first 10^465 steps (macro run). The macro run from blank tape goes through 293 rebuilds without a halt; at the end V has 1,536 digits and the step count is about 10^465.

**Computed (trusted C/Python, tested)** (`py/map.py check 100 40`, `py/map.py small 9`): The shape of the macro map: copy steps and eat steps. At a V = 0 moment the header is `0110101 a 1 b 1` with two flags a, b. Fitted to computed rebuilds and then checked, not proved: if a = 0 the rebuild is a 'copy': the counter is kept and gets one more 1 on top (new counter N + 2^n+1, n grows by 1), and a becomes 1. If a = 1 it is an 'eat': an even number s of low digits of N is removed, n grows by 3s/2 + 1 and the new counter is 2^n' + (N >> s) − δ with 0 < δ < 2^3s+8; the flags may come out either way. The number s is given by the same kind of walk as for the sibling `1RB1LD_1RC0RB_1LA1RC_1LE0LA_1LF---_1LC---`: with b = 0 an even N gives s = 2 and an odd N starts the walk in state Q; with b = 1 an odd N gives s = 2 and an even N starts it in state R; Q passes pairs 11, switches to R on 00 and stops on 01 or 10; R passes pairs ending in 0 and stops on a pair ending in 1. Checked against the exact rebuild: 100 random 40-digit counters with all four headers and three values of n (600 copies, 600 eats), and every 9-digit counter (1,530 copies, 1,344 eats; the all-ones counter is left out of the copy rule; 192 eats have a walk that reaches the top three digits, one of which halts); no exception. δ as a function of the digits read was not written down.

**Observed only / heuristic** (`py/rebuild_stats.py 1RB1LE_1RC0R... run`): What the rebuild map looks like in the run. The 293 rebuilds of a 90-second macro run end in all four headers; 96 are copies and the others eat s = 2, 4, 6, ... digits (about half of them 2). So this machine behaves like its sibling `1RB1LD_1RC0RB_1LA1RC_1LE0LA_1LF---_1LC---` with an extra copy step: a counter that gains long blocks on top and loses a few digits at the bottom by a walk that would have to cross the whole counter for anything unusual (such as a halt) to happen. The same chance argument suggests it never halts; it is a heuristic.

**Open**: Does it halt from blank tape?. Not known. The two siblings `1RB1LC_0RC0RB_1LD0LA_1LE---_1LF1RA_1LA1LC` and `1RB1LE_1RC0RB_1LD1RC_1LA1LE_1LF0LA_1LC---` have non-halting proofs in Coq in open pull requests of ccz181078/busycoq (#58 and #57; read on 12 November, not rebuilt here: Coq is not installed in this container). Their method, in plain terms: call a 'wall' the tape at a moment when V is 0. The proof gives a property of walls (enough spare room, and a marker: a 1 digit at a prescribed kind of position in the counter) and shows that every wall with the property runs to another wall with the property. It works there because the rebuild of those machines converts the whole counter in one go and loses only a bounded amount each time, so the marker can be followed from wall to wall. For this machine no such property was found (round 6): only the copy step converts the whole counter; the eat steps remove a few low digits by the walk and leave the rest, as in `1RB1LD_1RC0RB_1LA1RC_1LE0LA_1LF---_1LC---`, and no quantity is known that every step keeps and that stops the walk before the top. No rebuild rule is proved in Lean for this machine. A known reduction, not rebuilt here: busycoq's `Eqv_v3.v` (entry TM411) proves in Coq that this machine halts if and only if `1RB1LE_1RC0RB_1RD0LF_1LA0LC_1LD0LA_---1RB` halts.

## Reproduce

```sh
. /etc/profile.d/lean.sh      # after scripts/setup-lean.sh
holdouts/1RB1LE_1RC0RB_1RD1LF_1LA0LC_1LD0LA_---0RE/lean/check.sh          # Machine, Blank, Rules (ticks), Phase
python3 holdouts/1RB1LE_1RC0RB_1RD1LF_1LA0LC_1LD0LA_---0RE/py/map.py check 100 40       # copy/eat shape of the macro map, random 40-digit counters (90 s)
python3 holdouts/1RB1LE_1RC0RB_1RD1LF_1LA0LC_1LD0LA_---0RE/py/map.py small 9            # the same for every 9-digit counter
python3 holdouts/1RB1LC_0RC0RB_1LD0LA_1LE---_1LF1RA_1LA1LC/py/gen_phase.py 1RB1LE_1RC0RB_1RD1LF_1LA0LC_1LD0LA_---0RE > holdouts/1RB1LE_1RC0RB_1RD1LF_1LA0LC_1LD0LA_---0RE/lean/Phase.lean
python3 holdouts/1RB1LE_1RC0RB_1RD1LF_1LA0LC_1LD0LA_---0RE/py/map.py check 100 40       # copy/eat shape of the macro map, random 40-digit counters (90 s)
python3 holdouts/1RB1LE_1RC0RB_1RD1LF_1LA0LC_1LD0LA_---0RE/py/map.py small 9            # the same for every 9-digit counter
python3 holdouts/1RB1LC_0RC0RB_1LD0LA_1LE---_1LF1RA_1LA1LC/py/gen_phase.py 1RB1LE_1RC0RB_1RD1LF_1LA0LC_1LD0LA_---0RE > holdouts/1RB1LE_1RC0RB_1RD1LF_1LA0LC_1LD0LA_---0RE/lean/Phase.lean
python3 holdouts/1RB1LE_1RC0RB_1RD1LF_1LA0LC_1LD0LA_---0RE/py/map.py check 100 40       # copy/eat shape of the macro map, random 40-digit counters (90 s)
python3 holdouts/1RB1LE_1RC0RB_1RD1LF_1LA0LC_1LD0LA_---0RE/py/map.py small 9            # the same for every 9-digit counter
python3 holdouts/1RB1LC_0RC0RB_1LD0LA_1LE---_1LF1RA_1LA1LC/py/gen_phase.py 1RB1LE_1RC0RB_1RD1LF_1LA0LC_1LD0LA_---0RE > holdouts/1RB1LE_1RC0RB_1RD1LF_1LA0LC_1LD0LA_---0RE/lean/Phase.lean
python3 holdouts/1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LB/py/rebuild.py 1RB1LE_1RC0RB_1RD1LF_1LA0LC_1LD0LA_---0RE validate 120          # macro run = counters.py run, state by state
python3 holdouts/1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LB/py/rebuild_stats.py 1RB1LE_1RC0RB_1RD1LF_1LA0LC_1LD0LA_---0RE run 1500        # the macro run, one line per rebuild
python3 holdouts/1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LB/py/rebuild_stats.py 1RB1LE_1RC0RB_1RD1LF_1LA0LC_1LD0LA_---0RE halting 12      # which rebuilds halt, N < 2^12
```
