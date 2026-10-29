# Shared tools

Machine-agnostic tooling for studying a two-symbol Turing machine, pulled out of the code written for the holdout in
[`../bb6-holdout`](../bb6-holdout) (which keeps its own copies and is unchanged). Each machine's folder uses these
as they are and keeps only what is about its own machine.

| path | what it is | came from |
|---|---|---|
| `lean/TM/Basic.lean` | the semantics of any machine (`δ` a parameter): stream tapes, `step`, `steps`, `steps_seq`, `steps_halt`, `Halts`, and the shift-rule lemmas `cross_r`, `cross_l` | `bb6-holdout/lean/BB6/Basic.lean`, `Cycles.lean` |
| `lean/TM/Fin.lean` | a list simulator proved to agree with `steps` (`FCfg.steps_eq`), so bounded runs from blank tape become `decide +kernel` or `native_decide` goals (`blank_runs`, `blank_reaches`, `blank_halts`) | new |
| `lean/check.sh` | compile the library, then a machine's files, with plain `lean` (no Lake) | `bb6-holdout/lean/check.sh` |
| `py/bbtools/leangen.py` | the Lean definition of a machine, generated from its text form | new |
| `py/bbtools/symtm.py` | symbolic simulation with repeats and unknown context, shift rules found automatically, and **Lean proofs written from the trace** (`prove`) | `bb6-holdout/rec/symtm.py`, `lean/gen_rules.py` |
| `py/bbtools/machine.py` | parser of the standard format and the reference simulator | the many per-machine simulators |
| `py/bbtools/explore.py` | records, end-of-tape events and block lists of a run, for finding macro structure | new |
| `py/bbtools/invariants.py` | exhaustive search for conserved a·ones + b·pos + W[state] (mod m) | the holdout's mod-3 invariant, found by hand there |
| `c/tm.h`, `c/tmrun.c` | fast direct simulator (records, events, snapshots) | `bb6-holdout/stepper`, `blankrun` |
| `c/parts.h`, `c/run_parts.sh`, `py/merge_parts.py` | a search split into parts: output protocol, resumable parallel runner, checked merge (refuses missing or unfinished parts) | `bb6-holdout/dfs/run_parts.sh`, `merge.py` |
| `c/windowscan.c` | an example part program: every K-cell word in a state, run T steps | new |
| `pages/build_status.py` | a proof-status page from JSON, every claim tagged kernel / native / trusted / heuristic / open | the design of `pages/proof-status.html` |
| `tests/test_tools.py` | tests of all of the above (C against Python, known champions, symbolic against concrete, generated Lean compiled) | new |

The other machine's C exhaustive search itself (`bb6-holdout/csearch/nrefdfs2*.c`) runs that machine's mark model and
is not generic; what carries over is its harness: split into parts, run them in parallel, merge and check.

## Use

```sh
bash scripts/setup-lean.sh && . /etc/profile.d/lean.sh      # Lean 4.34.0, core only
tools/lean/check.sh                                         # library and its tests
python3 tools/tests/test_tools.py                           # everything, Lean included when installed

cd tools/py
python3 -m bbtools.leangen MACHINE Namespace > Machine.lean
python3 -m bbtools.invariants MACHINE
python3 -m bbtools.explore records MACHINE 100000
python3 -c 'from bbtools.symtm import prove; print(prove("MACHINE", "rule", "L A> 1^n R", "L 1^n A> R")[0])'

gcc -O2 -o tmrun tools/c/tmrun.c && ./tmrun MACHINE 1000000000 at F L
tools/c/run_parts.sh 64 4 out ./windowscan MACHINE A 24 1000 && python3 tools/py/merge_parts.py out/part_*.txt
```

Conventions: step counts are bbchallenge's (the halting transition counts); `steps n c = some c'` in Lean is n
ordinary transitions. A trust level is part of every result: Lean kernel, `native_decide`, trusted computation,
heuristic.
