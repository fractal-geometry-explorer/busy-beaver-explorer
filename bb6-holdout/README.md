# The BB(6) holdout 1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LD1RE

Research materials on one of the six-state Turing machines whose halting status is open. **The question is not
settled here.** What this folder contains is a structural description of how the machine runs, the parts of it that
are proved (several of them in Lean 4), the computations behind the rest, and the programs that check them.

The full research log is [`notes/LAB_NOTES.md`](notes/LAB_NOTES.md); [`notes/rule-map.html`](notes/rule-map.html) is
the summary page (open it in a browser), including the table "What is established, and how firmly".

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

  The number of rounds in both is existential (the round where the run breaks off, cleans the tape, completes a pass
  or leaves phase 0, chosen per class by an untrusted program), and nothing is claimed for R in the closing set.

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
deeper exhaustive runs were made with the uninstrumented program. See "The trailing wall" in the notes.

## How to check

**Lean** (built and checked with Lean 4.34.0; no Lake project, only a `lean` binary and its library):

```sh
cd lean
LEAN=/path/to/lean LEANLIB=/path/to/lib/lean ./check.sh        # all 21 files, about a minute; prints the axioms
# the two theorems (13 and 40 minutes of native_decide evaluation):
LEAN_PATH=$LEANLIB:$PWD/out $LEAN thm/ExitTheorem.lean -o out/ExitTheorem.olean
LEAN_PATH=$LEANLIB:$PWD/out $LEAN thm/EndgameTheorem.lean -o out/EndgameTheorem.olean
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
| `notes/` | the research log and the summary page |
| `lean/` | the Lean development (`BB6/`), the certificate runners, the tree builders, and `thm/` with the two theorems |
| `rec/` | the Python symbolic prover of the mark rules |
| `cert/` | certificate files (compressed), the independent checkers, and their outputs |
| `csearch/` | the C explorers (exhaustive check, route trees, plateau exits, and earlier experiments) |
| `dfs/` | merged results of the exhaustive check to 54, 56, 58 and 60 digits, and the driver |
| `audit/` | instrumented copies of the checkers and explorers used for the trailing-wall audit, with their outputs |
| `runs/` | the 64-digit route-tree summary and the exact plateau exits |

The notes are a working log kept as the research went; they refer to intermediate files (sampled runs, large
explorer outputs) that are not all included here.

This work was done by the repository owner with Claude, Anthropic's AI model.
