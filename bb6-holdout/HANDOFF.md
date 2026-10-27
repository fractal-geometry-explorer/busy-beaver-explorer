# Handoff: continuing this work in a new session

This folder was assembled at the end of a long session (October 2026) and moved to a new repository. It is
self-contained except for the large intermediate outputs mentioned in `README.md`.

## State at handoff

- **Lean** (`lean/`): 21 files check with `./check.sh` (Lean 4.34.0, core only, no Lake). The exit and endgame
  theorems are in `lean/thm/` (evaluated with `native_decide`: 13 and 40 minutes). The previous session built Lean
  from source because release downloads were blocked; if the new environment can download releases, install 4.34.0.
- **Certificates** (`cert/`): all three Python checkers report CERTIFICATE VALID; the outputs are saved next to them.
- **Exhaustive check** (`dfs/`): merged results to 54, 56, 58 and 60 digits. The 60-digit run (`merged60.txt`) is
  the final one: no clean tape below 2^61 reaches a halt (36,929,911,789 settled classes, 120,940,310,955 direct runs,
  no problems; largest jump 345, longest chain 17).
- **Repositories**: this folder was first pushed to `busy-beaver-explorer/busy-beaver-explorer` (branch
  `bb6-holdout`, PR #1, which stops at the 58-digit result). The current copy is in
  `fractal-geometry-explorer/busy-beaver-explorer`.
- **Pages** (`../pages/`): the summary page (`closing-gap-rule-map.html`), the mark-rule stepper, and the two pages on
  the BB(6) champion. The live copies were claude.ai artifacts in the previous session. The summary page is generated:
  edit `pages/src/closing-gap-rule-map/` (the table "What is established" is `established.py`) and rebuild, rather
  than editing the HTML.
- **Research scripts**: the Python, JavaScript and C programs behind the notes are in this folder as they were run
  (see the layout table in `README.md`); their large outputs are not.

## Working here

- Lean: install Lean 4.34.0 and run `cd bb6-holdout/lean && ./check.sh`.
- Summary page: `cd pages/src/closing-gap-rule-map && python3 build_m2.py` rewrites `pages/closing-gap-rule-map.html`.

## Next steps (as proposed at handoff)

1. **Done (October 27):** `endgame_stretch` (with the L₁ classes of the closing R) and the loop's chain in
   `lean/thm/EndgameTheorem.lean`, `LoopTheorem.lean` and `LoopHalt.lean`; see the lean README. The stretches end at
   stated events (`lean/BB6/Ends.lean`): the first versions (`endgame_no_close`, `loop_no_close`, `loop_pass`,
   `exit_no_halt`) held with zero rounds. The end event carries the loop's three steps with their exact maps on
   (E, R, L₁), checked at every leaf of the endgame trees that comes back to three walls: a full pass (R′ = R/16,
   L₁′ = L₁/64), a half pass (R′ = R/2, only as the first step) and a break of the chain at round 7.
   `loop_chain_halt` follows a halting run through every landing with gaps ≥ 448 (`LoopChain`), and the σ bound is a
   theorem: a close through the loop needs R³/L₁² ≤ 176³/256², i.e. log₂W ≤ σ + 6.38, at the start of the chain's
   last run of full passes (`LoopChain.sigma`, `loop_halt_sigma`, `blank_halt_sigma`); from a width ≥ 2²⁴ the chain to
   a close has no round-7 break (`LoopChain.close_wide`, `blank_halt_wide`). Past the chain's end, pass-start trees
   (`lean/BB6/PassTree.lean`, `lean/thm/PassHalt.lean`, built by a proved explorer) follow the run to the next close-free
   landing or a wider clean tape at every depth: `pass_halt_chain` gives, from a halting pass start of width ≥ 2¹³, the
   chain to a last pass start that is in a closing class, cut at every depth, or followed by a wider clean tape the run
   halts from. Some cut classes are real halts (1/8 of the pass starts with R = 6). The original note:
   **The loop's end for every width as one Lean theorem.** Prove the pass map (R → R/16, L → L/64) with R free
   using the symbolic runner (`BB6/SymRound`, `BB6/SymSplit`), then induct over passes, combined with
   `endgame_no_close` for R ≤ 4096: "a run through the loop closes only from R ∈ {2, 4, 8, 16, 24, 32, 48, 64, 176}
   at its last pass start, hence log₂W ≤ σ + 6.38".
2. **Done in part (October 27):** `halt_needs_contact` and `halt_after_rounds` (`lean/BB6/HaltClose.lean`,
   `HaltStretch.lean`), and the end-to-end statement `blank_halt_structure` (`lean/thm/EndToEnd.lean`,
   `lean/END_TO_END.md`): a halt from blank tape needs a clean tape of width ≥ 2³² that is in a cut class of the
   clean-tape tree at every depth (at 36 digits: measure 2.4 × 10⁻⁵), then a stuck contact. With the members of the
   cut classes below 2⁴¹ run one by one (`blank_halt_clean_direct`), the clean tape is at least 2⁴¹ wide. What
   remains is those clean tapes themselves. The loop and exit items of `blank_halt_structure` name where their
   stretches end, and the loop item carries the σ bound (item 1).
   The original note:
   **"A halt needs a close", formally**: from a well-formed state the model is uncovered only at contacts; show which
   contacts are reachable, so that "no close" over a stretch becomes "no halt" for whole runs.
3. **Remove the compiler trust** from the two theorems (kernel evaluation, or compact per-tree certificates).
   Done for the route tree and the clean-tape tree (October 27): they are built by an explorer proved to build only
   trees that pass the check (`lean/BB6/RouteExplore.lean`), so their theorems hold at every depth with the standard
   axioms only; only the measures of their cut classes are evaluated. The exit, loop and endgame trees are checked by
   Lean's kernel (`decide +kernel`, October 27). What still uses `native_decide` is the blank-tape prefix to 2³² (10⁹
   rounds, out of the kernel's reach) and the direct runs below 2⁴¹. **Done for the end-to-end statement from 2²⁰
   (October 27):** the run to 2²⁰ is kernel-checked (`blank_prefix_kernel`, 294,033 rounds, 2 minutes on 4 cores),
   and with the clean-tape tree over the widths ≥ 2²⁰ it gives `blank_halt_structure_kernel` (`lean/thm/EndToEnd.lean`)
   with the standard axioms only; with the cone's edge handled by drops (the smallest member of a class run directly),
   its cut classes are the same as from 2³² and 2⁴¹: the exhaustive check's open classes, 1,660,024 at 36 digits.
4. **The route-tree certificate in Lean** (the "ways into the loop have ceilings" results). Done (October 27) for the
   tree itself: `route_tree_clean` at every depth and cone constant (`lean/ROUTE_TREE.md`), with the certificate's
   cut classes at 36 and 40 digits. The ceilings are not in Lean.
5. **Research**: of the three open questions (routes deeper than the tree, halts carried by the extra-wall loop
   alone, marks touching), the most promising is a lock for the extra-wall loops analogous to the plain loop's
   never-zero countdown.

## Practical notes

- Native compilation of the tree builders: `lean FILE.lean -c FILE.c` for every module, compile with
  `gcc -O2 -fwrapv -I$LEAN_PREFIX/include`, link with `$LEANLIB/libInit.a $LEANLIB/libleanrt.a -luv -lpthread -ldl
  -lm -lstdc++`. The tree builders are 10–100 times faster native than under `lean --run`.
- `dfs/run_parts.sh K nparts splitlvl outdir` runs the exhaustive check in parts, two at a time; set `BIN` to the
  compiled `csearch/nrefdfs2.c`. `dfs/merge.py` merges the parts.
- The trailing-wall slip described in the notes is fixed (October 27) in the Python checkers, the C engines
  `nrefdfs2`, `lined`, `rtree3d`, `rtree3e`, `gx3` and the stepper: they write the canonical form as `roundZ` does, and
  the C engines print how often they do (`trailing-wall canonical forms written: N` on stderr). The other programs in
  `csearch/` still have the slip; port the fix (a few lines in `shift_from`) before using one. After changing a
  simulator, run `simtest/check.sh`, which compares all of them with the proved model and the bare machine.
  `Model.lean` (the list model in Lean, the port of the old simulator) still has it.
