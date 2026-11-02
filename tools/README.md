# Shared tools

Machine-agnostic tooling for studying a two-symbol Turing machine, pulled out of the code written for the holdout in
[`../bb6-holdout`](../bb6-holdout) (which keeps its own copies and is unchanged). Each machine's folder uses these
as they are and keeps only what is about its own machine.

| path | what it is | came from |
|---|---|---|
| `lean/TM/Basic.lean` | the semantics of any machine (`δ` a parameter): stream tapes, `step`, `steps`, `steps_seq`, `steps_halt`, `Halts`, and the shift-rule lemmas `cross_r`, `cross_l` | `bb6-holdout/lean/BB6/Basic.lean`, `Cycles.lean` |
| `lean/TM/Fin.lean` | a list simulator proved to agree with `steps` (`FCfg.steps_eq`), so bounded runs from blank tape become `decide +kernel` or `native_decide` goals (`blank_runs`, `blank_reaches`, `blank_halts`) | new |
| `lean/TM/CTL.lean` | closed tape languages: an automaton on each side of the head and a set of abstract configurations, a closure test run by `decide`, and its soundness: every configuration of the run is covered (`reach`), so a set with no halt proves the machine never halts (`not_halts`) and one whose halts have blank tape after the head confines halting to the right edge (`halt_tail_blank`, `no_double_zero`) | new |
| `lean/check.sh` | compile the library, then a machine's files, with plain `lean` (no Lake) | `bb6-holdout/lean/check.sh` |
| `py/bbtools/leangen.py` | the Lean definition of a machine, generated from its text form | new |
| `py/bbtools/symtm.py` | symbolic simulation with repeats and unknown context, shift rules found automatically, and **Lean proofs written from the trace** (`prove`) | `bb6-holdout/rec/symtm.py`, `lean/gen_rules.py` |
| `py/bbtools/machine.py` | parser of the standard format and the reference simulator | the many per-machine simulators |
| `py/bbtools/explore.py` | records, end-of-tape events and block lists of a run, for finding macro structure | new |
| `py/bbtools/invariants.py` | exhaustive search for conserved a·ones + b·pos + W[state] (mod m) | the holdout's mod-3 invariant, found by hand there |
| `py/bbtools/ctl.py` | finds the closed tape language from windows of K cells (`search`), runs the same closure test as Lean (`check`), lists the halts it allows, and writes it as a Lean file (`lean_file`) | new |
| `c/tm.h`, `c/tmrun.c` | fast direct simulator (records, events, snapshots) | `bb6-holdout/stepper`, `blankrun` |
| `py/bbtools/explore.py` `tokens`, `turns` | the tape read as words (`a=10,b=110`, longest first, run-length coded) at the moments the head extends the tape, and the head's turns | new (for `bb6-1RB1RF_1LC0LB`) |
| `c/tokrun.c` | the same word view in C, for billions of steps | new |
| `c/parts.h`, `c/run_parts.sh`, `py/merge_parts.py` | a search split into parts: output protocol, resumable parallel runner, checked merge (refuses missing or unfinished parts) | `bb6-holdout/dfs/run_parts.sh`, `merge.py` |
| `c/windowscan.c` | an example part program: every K-cell word in a state, run T steps | new |
| `pages/build_status.py` | a proof-status page from JSON, every claim tagged kernel / native / trusted / heuristic / open | the design of `pages/proof-status.html` |
| `pages/explainer_status.py` | writes the status panel of an explainer page (a JSON block) from a machine's `status.json`; `check` tells a test whether the page is current | `bb6-1RB1RA_1RC1LB_1LD0RA_1LB0LE/py/explainer_status.py` (which keeps its copy) |
| `tests/test_tools.py` | tests of all of the above (C against Python, known champions, symbolic against concrete, generated Lean compiled) | new |

The other machine's C exhaustive search itself (`bb6-holdout/csearch/nrefdfs2*.c`) runs that machine's mark model and
is not generic; what carries over is its harness: split into parts, run them in parallel, merge and check.

## Adding a machine

`bb6-1RB1RA_1LC1LD/` is the smallest complete example; `bb6-1RB1RF_1LC0LB/` is a fresh one. For a new machine `M`:

1. `python3 -m bbtools.leangen M Namespace` (from `tools/py`) writes `lean/Machine.lean`; add `lean/Blank.lean` with
   `blank_runs` goals and a `lean/check.sh` that calls `tools/lean/check.sh . Machine.lean Blank.lean ...`.
2. Put the machine's own scripts in `py/` (import `bbtools` from `../../tools/py`) and tests in `tests/` that compare
   the generated files and the page with what the tools write now.
3. Write `status.json` and build `pages/<short name>/proof-status.html` with `pages/build_status.py`; link it from
   `pages/index.html`.
4. Add the machine's Lean check and tests to `.github/workflows/tests.yml`.

## Use

```sh
bash scripts/setup-lean.sh && . /etc/profile.d/lean.sh      # Lean 4.34.0, core only
tools/lean/check.sh                                         # library and its tests
python3 tools/tests/test_tools.py                           # everything, Lean included when installed

cd tools/py
python3 -m bbtools.leangen MACHINE Namespace > Machine.lean
python3 -m bbtools.invariants MACHINE
python3 -m bbtools.ctl MACHINE 3                              # where can it halt?  then: ... 3 lean Namespace > F.lean
python3 -m bbtools.explore records MACHINE 100000
python3 -m bbtools.explore tokens MACHINE 3000000 a=10,b=110 L 40     # the tape as words at the left end
python3 -m bbtools.explore turns MACHINE 1681 2200                    # every turn of the head
python3 -c 'from bbtools.symtm import prove; print(prove("MACHINE", "rule", "L A> 1^n R", "L 1^n A> R")[0])'

gcc -O2 -o tmrun tools/c/tmrun.c && ./tmrun MACHINE 1000000000 at F L
gcc -O2 -o tokrun tools/c/tokrun.c && ./tokrun MACHINE 10000000000 a=10,b=110 L 1000
tools/c/run_parts.sh 64 4 out ./windowscan MACHINE A 24 1000 && python3 tools/py/merge_parts.py out/part_*.txt
```

Conventions: step counts are bbchallenge's (the halting transition counts); `steps n c = some c'` in Lean is n
ordinary transitions. A trust level is part of every result: Lean kernel, `native_decide`, trusted computation,
heuristic.
