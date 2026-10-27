# The BB(6) holdout 1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LD1RE

Research materials on one of the six-state Turing machines whose halting status is open. **The question is not
settled here.** What this folder contains is a structural description of how the machine runs, the parts of it that
are proved (several of them in Lean 4), the computations behind the rest, and the programs that check them.

The full research log is [`notes/LAB_NOTES.md`](notes/LAB_NOTES.md). The summary page is
[`../pages/closing-gap-rule-map.html`](../pages/closing-gap-rule-map.html) (open it in a browser), including the table
"What is established, and how firmly"; [`../pages/mark-rule-stepper.html`](../pages/mark-rule-stepper.html) steps the
mark rules interactively.

## What is established

**Proved in Lean 4** (`lean/`, core library only, no Mathlib; no `sorry`):

- *The mark rules.* The tape is stripes `1010…` plus a few marks (gap `000`, marker `11`, wall `00`, block `111`);
  21 rules say how the machine moves them, each a theorem about `steps n` for every stripe length and any
  surrounding tape. Generated from the Python prover's traces (`rec/proofs.py`, `lean/gen_rules.py`).
- *The round theorem.* From the tape of any well-formed mark state, the machine reaches exactly the next round start
  that the mark model computes, or halts exactly where the model says it halts (`round_run`, `rounds_run`); from blank
  tape it follows the model for as many rounds as the model covers (`blank_rounds`).
- *Two loop results as theorems about the machine* (`lean/thm/`). The split trees are data checked by a proved
  function evaluated with `native_decide`, so these two also trust Lean's compiler, not only its kernel:
  - `exit_no_halt`: every loop state (walls at a, b, c, width E; a odd, b even, c odd, E even; every gap ≥ 390) runs
    to another round start without halting;
  - `endgame_no_close`: for every even R ≤ 4096 outside {2, 4, 8, 16, 24, 32, 48, 64, 176}, every phase-0 pass
    start (walls at a, b, E − R − 1, width E; every gap ≥ 448) runs to a round start without halting and without an
    end meeting at distance ≤ 2.

  - `loop_no_close` (`thm/LoopTheorem.lean`): the same as `endgame_no_close` for **every** even R ≥ 2 outside the
    closing set, at any width. For R ≥ 4097 one tree with R as a free coordinate (`loop_pass`, `thm/LoopPass.lean`)
    follows the run to where it leaves the loop or reaches another phase-0 pass start with gaps ≥ 448 and R′ = R/16,
    L₁′ = L₁/64 (the pass map), or R′ = R/2 on one short branch; strong induction on R through those pass starts
    ends in the endgame trees. So within the stretch the trees certify, a run through the loop closes only from a pass
    start whose R is in the closing set; after the stretch ends, a run can come back to phase-0 pass starts and close
    later (an example from R = 22, and the loop tree's R/2 "half pass", are in the notes, October 27). (The bound
    log₂W ≤ σ + 6.38 also needs the L₁ classes of the closing R, which are not in Lean, and a way across half passes.)

  The number of rounds in all three is existential (the round where the run breaks off, cleans the tape, completes a pass
  or leaves phase 0, chosen per class by an untrusted program), and nothing is claimed for R in the closing set.
- *End to end from blank tape* (`lean/thm/EndToEnd.lean`, `lean/END_TO_END.md`; also `native_decide`):
  `blank_halt_structure` says that if the machine halts from blank tape, it first reaches a clean tape of even width
  W ≥ 2³² with W/2 in one of the cut classes of a 36-digit clean-tape tree (1,660,016 residue classes, measure
  2.4 × 10⁻⁵) and halts from there; the mark model run from that clean tape reaches a close at the right end or an
  interior contact; and every pass start (R outside the closing set) the run passes is followed by the loop's
  close-free stretch, the halt coming only after it. `never_halts_of_cut_classes` is the same read backwards: the
  question is reduced to the clean tapes of width ≥ 2³² in the cut classes. The pieces: the model's run from blank
  tape to the clean tape of width 2³² (`thm/Prefix.lean`, 1.2 × 10⁹ rounds), and the clean-tape tree
  (`BB6/CleanTree.lean`, `thm/CleanTheorem.lean`): from every clean tape of width ≥ 2³² outside the cut classes, the
  machine reaches a wider clean tape without halting.

**Proved by certificates with independent checkers** (`cert/`): the exact end of the loop (40,991 classes; 83,699
for starts in either phase), the short exit from the loop (358 classes), and the route tree to 36 and 40 digits.
Every endgame, any-phase and exit leaf also checks through the Lean-verified symbolic model (`lean/CheckEndgame.lean`,
`lean/CheckExit.lean`).

**Exhaustive computation** (`csearch/nrefdfs2.c`, `dfs/`): every clean tape below 2^61 reaches the next clean tape
without a halt: 36.9 billion settled classes and 121 billion direct runs, about 1.8 × 10^52 machine steps
(`dfs/merged60.txt`).

**Measured and heuristic** statements (how runs enter the loop, the odds of a halt beyond the exhaustive range) are
marked as such in the notes and on the summary page; they are not proofs.

**A correction found by the formalization.** The simulator used by the Python checkers and the C explorers mishandles
one end-of-tape sequence (the "trailing wall": a shift reaching a block in the last three cells, then a later shift
reaching the wall it leaves). Instrumented reruns (`audit/`) of the certificate checkers, the exhaustive check to 46
digits, the route trees and the plateau exits reproduce their results exactly and never reach that sequence; the
deeper exhaustive runs were made with the uninstrumented program. See "The trailing wall" in the notes. **Fixed
(October 27):** the checkers, the C engines current work uses (`nrefdfs2`, `lined`, `rtree3d`, `rtree3e`, `gx3`) and
the stepper now write the canonical form, as the proved model does, and `simtest/` checks every one of them against
the proved model on random tapes. With the fixed programs the certificates (exit, endgame, any-phase, 36-digit route tree) check with unchanged output, and the
exhaustive check to 54 digits reproduces `dfs/merged54.txt` exactly, with the corrected case never occurring. The other
programs in `csearch/` are kept as they were run.

## How to check

**Lean** (built and checked with Lean 4.34.0; no Lake project, only a `lean` binary and its library):

```sh
cd lean
LEAN=/path/to/lean LEANLIB=/path/to/lib/lean ./check.sh        # all 24 files, about a minute; prints the axioms
# the two theorems (13 and 40 minutes of native_decide evaluation):
LEAN_PATH=$LEANLIB:$PWD/out $LEAN thm/ExitTheorem.lean -o out/ExitTheorem.olean
LEAN_PATH=$LEANLIB:$PWD/out $LEAN thm/ExitHalt.lean                                  # after ExitTheorem: a halt needs a contact after the exit
LEAN_PATH=$LEANLIB:$PWD/out $LEAN thm/EndgameTheorem.lean -o out/EndgameTheorem.olean
LEAN_PATH=$LEANLIB:$PWD/out $LEAN thm/EndgameHalt.lean                               # after EndgameTheorem
# the loop's end for every width (under a minute, then the induction; needs EndgameTheorem.olean):
LEAN_PATH=$LEANLIB:$PWD/out $LEAN thm/LoopPass.lean -o out/LoopPass.olean
LEAN_PATH=$LEANLIB:$PWD/out $LEAN thm/LoopTheorem.lean -o out/LoopTheorem.olean
LEAN_PATH=$LEANLIB:$PWD/out $LEAN thm/LoopAxioms.lean
# end to end (all the theorem files above, the prefix and the clean-tape tree, as native code; about 15 minutes):
LEAN=/path/to/lean LEANLIB=/path/to/lib/lean ./check_end.sh
```

`thm/gen_exit.py` and `thm/gen_endgame.py` regenerate the theorem files from the trees (`thm/exit_tree.txt`,
`thm/endgame_trees.txt`), which the untrusted builders `ExploreExit.lean` and `ExploreNC.lean` produce.

**Certificates** (Python 3, exact rational arithmetic):

```sh
cd cert
gunzip -k *.gz
python3 check_endgame.py endgame_leaves.txt
CHECK_NOPHASE=1 python3 check_endgame.py endgame_anyphase_leaves.txt
python3 check_exit.py exit_leaves.txt
python3 check_tree.py tree36_leaves.txt          # hours
```

## Layout

| folder | contents |
|---|---|
| `notes/` | the research log |
| `lean/` | the Lean development (`BB6/`), the certificate runners, the tree builders, and `thm/` with the two theorems |
| `cert/` | certificate files (compressed), the independent checkers, and their outputs |
| `csearch/` | the C explorers (exhaustive check, route trees, plateau exits, and earlier experiments) |
| `dfs/` | merged results of the exhaustive check to 54, 56, 58 and 60 digits, and the driver |
| `simtest/` | the differential test of the simulators (Python, C, stepper) against the proved model and the bare machine |
| `audit/` | instrumented copies of the checkers and explorers used for the trailing-wall audit, with their outputs |
| `rec/` | the Python symbolic prover of the mark rules, and the Python research scripts (simulators, invariant searches, halt-odds estimates, end-of-loop studies) |
| `conc/` | Python studies of the routes into the loop, the extra-wall loops and their exits |
| `lines/` | Python studies of the lines of clean tapes (records, reach, frontier) |
| `rt3/` | drivers and pin-form scripts for the 64-digit route tree |
| `runs/` | the 64-digit route-tree summary, the exact plateau exits, and the pattern maps |
| `stepper/` | the mark-rule engine of the stepper page (`engine.js`) and the Node scripts run on it |
| `m2/` | the first JavaScript explorations of the machine (event and round extraction) |
| `lock/` | locks for the extra-wall loops (October 27): P and Q pass maps as Lean theorems, the quadratic never-zero countdown of Q, locks for every periodic word, and why mixtures have none (`lock/LOCK_NOTES.md`) |
| `sib/` | a simulator for any six-state machine from blank tape |

The notes are a working log kept as the research went. Paths in them such as `../csearch/gx3.c` are relative to
`notes/`. They also refer to intermediate files (sampled runs, large explorer outputs, the per-part outputs of the
exhaustive check) that are not included here; every one of them is regenerated by the program the notes name.

The research scripts are kept as they were run, not cleaned up: each expects to be run from its own folder, and some
need a compiled explorer from `csearch/` or an output file that is not included.

This work was done by the repository owner with Claude, Anthropic's AI model.
