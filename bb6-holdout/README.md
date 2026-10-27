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
- *The loop and its exit as theorems about the machine* (`lean/thm/`). The split trees are checked by a proved
  function, evaluated by Lean's kernel alone (`decide +kernel`, the check cut into subtree theorems). Each tree's
  leaves end at a stated event (`lean/BB6/Ends.lean`) that never holds after zero rounds:
  - `exit_stretch`: every loop state (walls at a, b, c, width E; a odd, b even, c odd, E even; every gap ≥ 390) runs
    without halting and with every end meeting at distance ≥ 3 until a clean tape, a break of the end-meeting chain,
    or a loop state again after a full pass (358 classes: 298 breaks, 58 clean tapes, 2 passes);
  - `endgame_stretch`: for every even R ≥ 2, every phase-0 pass start (walls at a, b, E − R − 1, width E; every gap
    ≥ 448) either has R in the closing set {2, 4, 8, 16, 24, 32, 48, 64, 176} and its left countdown L₁ in R's class
    (for these R in turn: L₁ ≡ 0 mod 2, 0 mod 2, 0 mod 8, 0 mod 32, 32 mod 64, 0 mod 64, 0 mod 128, 0 mod 128,
    0 mod 128; and L₁ ≡ 3 mod 7 always), or runs without halting and without a close until it leaves phase 0 or its
    end meetings leave the chain, at a round start that is not three walls, or it lands on three walls again by one
    of the loop's three steps, each with its exact map, checked at every such leaf: a full pass (R′ = R/16,
    L₁′ = L₁/64, W′ = E + 24), a half pass from E ≡ 2 mod 4 (R′ = R/2, W′ = E + 6) or a break of the chain at round 7
    (R′ = (4E + 4R − b + 110)/32, W′ = E + 24). One tree with R as a coordinate covers every R ≥ 178; each smaller R
    has its own tree;
  - the loop's chain (`LoopChain`, `loop_chain_halt` in `thm/LoopTheorem.lean` and `thm/LoopHalt.lean`): if the
    machine halts from a pass start with gaps ≥ 448, its run follows these steps through every landing whose gaps are
    again ≥ 448, at any width (by induction on the halting time, since a round-7 break can raise R; a half pass comes
    only as the first step, since every landing has W′ ≡ 0 mod 4). So within the loop a run closes only from a pass
    start whose R is in the closing set and whose L₁ is in R's class; otherwise it runs close-free until it leaves the
    chain (a round start that is not three walls, or a landing with a gap below 448, which from a width ≥ 2¹³ happens
    only after a half pass from a middle wall within 896 of the end: `landing_wide`, `loop_halt_leaves`). After that a
    run can come back to phase-0 pass starts and close later (see the notes, October 27).
  - **The σ bound** (`LoopChain.sigma`, `loop_halt_sigma`, `blank_halt_sigma`): a pass divides R³ and L₁² by the same
    factor, and the closing classes have R³/L₁² ≤ 176³/256², so a close through the loop needs R³/L₁² ≤ 176³/256² at
    the start of the chain's last run of full passes: log₂W ≤ σ + 6.38, with σ = 3 log₂(W/R) + 2 log₂(|L₁|/W) there.
    At a round-7 landing that needs E < 2²⁴, so from a pass start of width ≥ 2²⁴ a close through the loop is p full
    passes after at most one half pass (`LoopChain.close_wide`, `blank_halt_wide`). The bound is attained
    (R = 2,816, L₁ = −16,384: one pass to R = 176, L₁ = −256, then a close).
  - **Past the chain's end** (`BB6/PassTree.lean`, `thm/PassHalt.lean`): pass-start trees, built by an explorer proved
    to build only checked trees, follow the run on to the next landing (close-free, a step of the chain) or a wider
    one-marker clean tape, at every depth with nothing evaluated (`pass_next`). By induction on the halting time, a
    halt from a pass start of width ≥ 2¹³ follows the chain to a last pass start that is in a closing class, or in a
    cut class of its tree at every depth, or from which the run goes on to a wider clean tape and halts from there
    (`pass_halt_chain`). Some cut classes are real halts: 1/8 of the pass starts with R = 6 leave the loop at round 2
    and close at distance 0 in round 7, and the machine halts there (from walls 743, 1,802, 3,319, width 3,326, after
    11,362,209 steps; for the whole class in Lean, `pass_r6_halt`).
  - **Every close at the right end is a halt** (`BB6/CloseHalt.lean`, `thm/PassHaltClasses.lean`): a close with the
    end marker at distance 0 that the model reaches is a halt 54 steps later (`reach_close_halt`). Every close leaf of
    the pass-start trees halts; with R = 6's eighth they are eight classes by residues of b and W (all of R = 2, 3/8 of
    R = 4, 1/32 to 1/256 of R = 8, 16, 32 and 48), proved to halt (`pass_class_halt`), as is every pass start whose
    loop chain reaches one (`chain_class_halt`). In 600,000 random pass starts the model's run ends at a clean tape
    or at that close, and every close passes through one of the classes.

  The number of rounds in all three is existential (chosen per class by an untrusted program), but each stretch ends at
  its stated event. The first versions (`exit_no_halt`, `endgame_no_close`, `loop_no_close`, `loop_pass`) said only
  that the run reaches some round start without halting or closing, which zero rounds satisfy; see the notes,
  October 27, "The stretches must say where they end".
- *End to end from blank tape* (`lean/thm/EndToEnd.lean`, `lean/END_TO_END.md`): `blank_halt_clean` says that if the
  machine halts from blank tape, it first reaches a clean tape of even width W ≥ 2³² that the clean-tape tree leaves
  open at **every** depth, and halts from there, the mark model run from that clean tape reaching a close at the right
  end or an interior contact; `blank_halt_loop` adds that every pass start with gaps ≥ 448 the run passes is
  followed by the loop's close-free stretch, the halt coming only after it (after a pass start in a close class, or
  after the run leaves the loop). `never_halts_of_cut_classes` is the first read backwards: the question is reduced
  to the clean tapes of width ≥ 2³² left open at every depth (at 36 digits they lie in 1,660,024 residue classes of
  W/2 of measure 2.4 × 10⁻⁵, at 40 digits in 9,188,898 of measure 8.4 × 10⁻⁶: exactly the open classes of the
  exhaustive check, the smallest members of classes at the cone's edge being run directly). The pieces: the model's run from
  blank tape to the clean tape of width 2³² (`thm/Prefix.lean`, 1.2 × 10⁹ rounds by `native_decide`, the only
  evaluation `blank_halt_clean` rests on), and the clean-tape tree (`BB6/CleanTree.lean`, `BB6/RouteExplore.lean`,
  `thm/CleanTheorem.lean`): at every depth, from every clean tape of width ≥ 2³² outside the cut classes, the machine
  reaches a wider clean tape without halting. The tree is built by an explorer proved to build only trees that pass
  the check, so this part uses the standard axioms only.
  `blank_halt_clean_direct` (`lean/thm/EndToEndDirect.lean`) raises the bound to 2⁴¹: the clean tapes of width in
  [2³², 2⁴¹) in the cut classes (26,508,327 of them) are run one by one in Lean, each to a wider clean tape
  (`thm/CleanDirect.lean`, `native_decide`), and above 2⁴¹ the tree with the cone W ≥ 2⁴¹ leaves open the same
  classes. `blank_halt_exit` adds the exit stretch, to its exit event,
  after every loop state the run passes. `blank_halt_structure_kernel` is all of this from width 2²⁰ instead of 2³²,
  with **no `native_decide`** (the standard axioms only): `blank_prefix_kernel` (`thm/PrefixKernel.lean`) checks the
  run from blank tape to the clean tape of width 2²⁰ (294,033 rounds) with Lean's kernel, and the clean-tape tree over
  the widths ≥ 2²⁰ takes over from there. Its cut classes are the same (1,660,024 at 36 digits).
  With the loop entries and the pass-start trees (`lean/thm/CleanEntryHalt.lean`, `lean/thm/PassEntryHalt.lean`),
  `blank_halt_pass` follows the whole run: a halt from blank tape needs a clean tape of width ≥ 2⁴¹ in a cut class of
  the clean-tape tree with loop entries at every depth (1,255,963 classes at 36 digits, measure 1.83 × 10⁻⁵), or a pass
  start wider than 2⁴¹ in a cut class of its pass-start tree at every depth, reached from a loop entry that cannot close
  along the loop's chain. Some pass starts in those classes halt (1/8 of those with R = 6, `pass_r6_halt`). But the
  plain clean-tape tree follows the run on through every entry, so the run reaches such a pass start only after a clean
  tape that the plain tree leaves open at every depth (`blank_halt_open`; at 36 digits one of the 404,061 of its
  1,660,024 cut classes that meet a loop entry). And its loop chain ends at none with a right end below 178, where
  every known halt from a pass start closes: `blank_halt_small` (`lean/thm/SmallEndHalt.lean`) puts the pass start a
  halt needs in the tree for R ≥ 178,
  since past a loop entry that passes a small-end check (every entry at 36 digits does) the loop's chain ends at R ≥ 178
  (full passes keep R³/L₁², and a round-7 break from a width ≥ 2³⁷ lands above 177³/9). So the question is whether the
  run reaches one of the open clean tapes, and from those, one of the open pass starts with R ≥ 178:
  `blank_halt_open_small` (`lean/thm/OpenSmallHalt.lean`) states the two together, and `never_halts_of_open` says that a
  negative answer to both would show the machine never halts.
- *The route tree* (`lean/thm/RouteTheorem.lean`, `lean/ROUTE_TREE.md`): `route_tree_clean`, the certificate's
  two-marker route tree as a theorem about the machine, at every depth and cone constant, with the standard axioms
  only (the same explorer); at 36 and 40 digits its cut classes are the Python certificate's (measure 5.9 × 10⁻⁶ and
  1.5 × 10⁻⁶, evaluated by `native_decide`).

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
exhaustive check to 60 digits reproduces `dfs/merged60.txt` exactly (`dfs/merged60_fixed.txt`), with the corrected case never occurring. The other
programs in `csearch/` are kept as they were run.

## How to check

**Lean** (built and checked with Lean 4.34.0; no Lake project, only a `lean` binary and its library):

```sh
cd lean
LEAN=/path/to/lean LEANLIB=/path/to/lib/lean ./check.sh        # all 25 files, about a minute; prints the axioms
# the theorem files: the exit and endgame trees and the run to width 2^20 evaluated by the kernel (their modules in
# parallel, about 4.5 minutes with 4 cores), the prefix, the direct runs below 2^41 and the clean-tape trees' measures
# with native_decide as native code, the halts after each stretch, and the end-to-end theorems (about 22 minutes with
# 4 cores):
LEAN=/path/to/lean LEANLIB=/path/to/lib/lean ./check_end.sh
# the route tree at every depth (seconds) and its measure at 36 digits (4 minutes; DEPTH=40 adds 40 digits, 16 more):
LEAN=/path/to/lean LEANLIB=/path/to/lib/lean ./check_route.sh --fast
```

`thm/gen_exit.py` and `thm/gen_endgame.py` regenerate the theorem files from the trees
(`python3 thm/gen_exit.py thm/exit_tree.txt thm`, `python3 thm/gen_endgame.py thm/endgame_sym.txt
thm/endgame_small.txt thm`), which the untrusted builder `ExploreNC.lean` produces (`ExploreNC exit 390`,
`ExploreNC sym 178 448`, `ExploreNC 176 448 ""`).

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
| `lean/` | the Lean development (`BB6/`), the certificate runners, the tree builders, and `thm/` with the theorem files |
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
| `lock/` | locks for the extra-wall loops (October 27): P and Q pass maps as Lean theorems, the quadratic never-zero countdown of Q, locks for every periodic word, why mixtures have none, and why no such lock can settle the open cases, whose runs almost never reach the loop (`lock/LOCK_NOTES.md`) |
| `sib/` | a simulator for any six-state machine from blank tape |

The notes are a working log kept as the research went. Paths in them such as `../csearch/gx3.c` are relative to
`notes/`. They also refer to intermediate files (sampled runs, large explorer outputs, the per-part outputs of the
exhaustive check) that are not included here; every one of them is regenerated by the program the notes name.

The research scripts are kept as they were run, not cleaned up: each expects to be run from its own folder, and some
need a compiled explorer from `csearch/` or an output file that is not included.

This work was done by the repository owner with Claude, Anthropic's AI model.
