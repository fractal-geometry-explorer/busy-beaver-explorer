# Invariant solvers on the counter programs that Lean already proves

Technique A of `holdouts/recent-proofs/technique-survey-nov26.md`: take the integer maps that Lean proves faithful
to a machine, read them as counter programs, and ask a solver for an inductive invariant that excludes the halting
case. Results: `holdouts/recent-proofs/followup/horn-solvers.md`.

| file | what it is |
|---|---|
| `maps.py` | the counter programs, transcribed by hand from `holdouts/<machine>/lean/*.lean` (the Lean file is named in a comment or in the note). An entry is the number of variables, the start, and guarded affine rules whose target is the next tuple or `'halt'`. Entries named `check:...` are controls: the halting cases go to a sink and only the map's `stuck`/`small` cases are bad, so the invariant asked for is one Lean already proves by hand |
| `spacer.py NAME SECONDS` | the program as constrained Horn clauses, solved by Z3's Spacer. `unsat` prints the invariant found |
| `absint.py NAME SECONDS` | a template search: each variable (and optional differences, `EXTRA`) is abstracted to "its exact value if below T in absolute value, else its sign and its residue mod M"; the reachable abstract states are enumerated with Z3, for M up to 36 and T up to 32. If none meets a bad guard their disjunction is an inductive invariant |
| `stack_model.py orbit\|free SECONDS` | the counter-stack model of 1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC (`py/stackmodel.py`, `lean/Model.lean` there) as Horn clauses over a list datatype: `orbit` asks whether the orbit from K(2), N = 48 can fail, `free` whether any wall reachable from the wall 1 under free parities can |

Needs `pip install z3-solver` (tested with 4.x / 5.4.1). A solver's answer is a candidate only: an invariant is to be
checked in Lean (`omega` on each rule) before it counts.
