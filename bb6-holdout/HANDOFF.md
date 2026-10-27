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
   halts from. Where the cone's edge leaves a round undecided, the explorer cleaves the class at the bound (`cleave`),
   so the cut classes (2.0% of a start class at 20 splits, 3.8% for R ≥ 178) are nearly all where the depth ran out.
   Some cut classes are real halts: every pass start with R = 6, b ≡ 2 (mod 8), W ≡ 2 (mod 4) and gaps ≥ 448 halts
   (`pass_r6_halt`, `lean/thm/PassHaltR6.lean`). And every close at the right end with the end marker at distance 0
   that the model reaches is a halt (`reach_close_halt`, `lean/BB6/CloseHalt.lean`): every close leaf of the
   pass-start trees halts, and with R = 6's eighth they make eight halting classes by residues of b and W (all of
   R = 2, 3/8 of R = 4, 1/32 to 1/256 of R = 8, 16, 32 and 48; `pass_class_halt`, `chain_class_halt`,
   `lean/thm/PassHaltClasses.lean`). In 600,000 random pass starts the model's run ends at a clean tape or that
   close, and every close passes through a class. Past the loop chain's end the run can enter the loop again and
   close, also from R ≥ 178 (`lean/thm/PassOpenHalt.lean`, item 2). The original note:
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
   stretches end, and the loop item carries the σ bound (item 1). With the loop entries (`blank_halt_clean_entry`,
   `lean/thm/CleanEntryHalt.lean`), the clean-tape tree also stops at the pass starts from which no member of the
   class can close through the loop, which leaves 1,255,963 of the 1,660,024 cut classes at 36 digits, none of whose
   runs meets three walls; a halt then needs such a clean tape, or such an entry from which the loop's chain ends
   without a close where the run leaves three walls. With the pass-start trees (`pass_halt_chain`) as what a halt from
   an entry needs, `blank_halt_pass` (`lean/thm/PassEntryHalt.lean`) follows the whole run: a halt from blank tape
   needs such a clean tape, or a pass start wider than 2⁴¹ in a cut class of its pass-start tree at every depth. Some
   of those pass starts halt (1/8 of those with R = 6, `pass_r6_halt`). But the plain clean-tape tree follows the run on
   through every entry, so the run reaches such a pass start only after a clean tape that the plain tree leaves open at
   every depth (`blank_halt_open`): at 36 digits one of the 404,061 cut classes that meet a loop entry in the tree with
   entries. And its loop chain ends at none with R < 178 (`blank_halt_small`, `lean/thm/SmallEndHalt.lean`): past a
   loop entry that passes the small-end check (`lean/BB6/SmallEnd.lean`; all 28,660 at 36 digits do) the loop's chain
   ends at R ≥ 178,
   so the pass start a halt needs is in the tree for R ≥ 178 (`passTreeSym`), whose cuts at the depths measured are all
   depth cuts, none at a round decided as a halt. What remains is which of the open clean tapes the run reaches, and
   from those, which of the open pass starts with R ≥ 178; `blank_halt_open_small` (`lean/thm/OpenSmallHalt.lean`)
   states the two together, and `never_halts_of_open` turns them into the two questions left. Some of those open pass
   starts with R ≥ 178 halt, at every width (`sym_open_halt`, `lean/thm/PassOpenHalt.lean`: a family with R = 178
   whose run leaves the loop, enters it again through an end meeting at 254 and closes; `open_halt_families`: eight
   such families, from an exhaustive scan of the widths 2,048 to 3,072 and a scan of where full passes land), and the
   loop's chain can land on one after a full pass (`full_pass_open_halt`), so the second question is whether the run
   reaches one.
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
   cut classes at 36 and 40 digits. The ceilings themselves are not in Lean, and not needed for the entries the tree
   reaches: a second tree (`routeTreeE`, `lean/BB6/RouteEntry.lean`) stops a path at the first pass start from which
   no point of its class closes through the loop at any width, decided on the class, which leaves a quarter of the cut
   classes at 36 digits and a fifth at 40; from such an entry a halt needs the loop's chain to end without a close
   (`blank_halt_route`, `lean/thm/RouteEntryHalt.lean`). Left: the run after the loop's end, and the cut classes,
   nearly all of them routes that meet no three-wall round start within the tree's depth.
5. **Research**: of the three open questions (routes deeper than the tree, halts carried by the extra-wall loop
   alone, marks touching), the most promising is a lock for the extra-wall loops analogous to the plain loop's
   never-zero countdown. **Done as far as it goes (October 27, `lock/LOCK_NOTES.md`):** Q and every periodic word have
   never-zero quadratic locks, mixtures have none (hand-built mixed tapes halt), and the open cases of
   `blank_halt_pass` almost never reach the extra-wall loop (0.09% of the clean-tape tree's cut classes at 36 digits,
   under 1% of the pass-start trees' undecided cut measure at 20 splits), so no such lock can settle them. What keeps
   them open is long runs of two- and three-mark rounds, about one digit per round. **Those runs, taken apart (October
   27, night, `lock/LOCK_NOTES.md` section 7):** they are words in about 14,000 exact return pieces (from one two-marker
   state to the next). Each piece repeated is bounded (every reset has a never-zero countdown; the eight largest pieces
   and their countdowns are theorems, `lock/lean_maps/GmmMaps.lean`), but no countdown is shared and chains of returns
   multiply 1.66-fold per digit, so no lock or integrality argument settles a class. The two-marker states up to width
   262,143 that halt are (4, 9), (4, 13) and (12, 17); the October 20 scan had missed the first and the last, and the
   machine reaches none of them.

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
