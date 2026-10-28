# Handoff: continuing this work in a new session

This folder was assembled at the end of a long session (October 2026) and moved to a new repository. It is
self-contained except for the large intermediate outputs mentioned in `README.md`.

## State at handoff

- **Lean** (`lean/`): 21 files check with `./check.sh` (Lean 4.34.0, core only, no Lake). The exit and endgame
  theorems are in `lean/thm/` (evaluated with `native_decide`: 13 and 40 minutes). The previous session built Lean
  from source because release downloads were blocked; if the new environment can download releases, install 4.34.0.
- **Certificates** (`cert/`): all three Python checkers report CERTIFICATE VALID; the outputs are saved next to them.
- **Exhaustive check** (`dfs/`): merged results to 54, 56, 58, 60 and 64 digits. The 64-digit run (`merged64.txt`,
  with the 128-bit engine `csearch/nrefdfs2w.c`) is the final one: no clean tape below 2^65 reaches a halt
  (204,860,486,855 settled classes, 661,842,319,825 direct runs, no problems; largest jump 375, longest chain 19), and
  its levels 1 to 60 equal the 60-digit run's (`merged60.txt`, `merged60_fixed.txt`) line for line.
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
   close, also from R ≥ 178 (`lean/thm/PassOpenHalt.lean`, item 2). On October 28 the closing classes were narrowed: an
   end meeting at distance 2 is not a close, so a close needs R in {2, 4, 8, 16, 32, 48} and L₁ in R's class of
   `closeClassC`, which gives R³/L₁² ≤ 4 (log₂W ≤ σ + 2), and from a width ≥ 2²⁰ a chain to a close with no
   round-7 break (`loop_halt_sigma_close`, `loop_halt_wide_close`, `lean/thm/LoopClose.lean`). The original note:
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
   loop's chain can land on one after a full pass (`full_pass_open_halt`); the same route gives one family at each
   scale of the third gap tried (`reentry_open_halt`: W − b = 2^(j+2) − 378, j = 10 to 30, R = 178), so the second
   question is whether the run reaches one. It reaches none of these 29 families (`blank_halt_not_family`,
   `lean/thm/WideHalt.lean`): with W ≤ 32R checked at the loop entries (`lean/BB6/WideEntry.lean`; all 28,660 at 36
   digits pass), the chain's last pass start has W ≤ 64R + 6 or 15W ≤ 64(W − b), and a family, with R and W − b fixed,
   has that shape only below width 32(W − b + 2R) + 6: the eight below 58,502, the 21 below 2³⁵, while the run's pass
   starts are wider than 2⁴¹. The chain's last pass start even has 15W ≤ 64(W − b) (`blank_halt_open_far`,
   `lean/thm/FarHalt.lean`), and with that none of the eight routes by which the 72 halting classes of a census
   (R = 178 to 198, W − b ≤ 8,192) close can start from it past 2⁴¹ (untrusted, `runs/reentry.py sigma`). A census at
   R = 200 to 262 finds more routes, among them classes at R = 230 that close with no pass start after the first,
   which R′³/L₁′² does not reach. But the chain's last pass start also has R ≥ 769 (`blank_halt_open_big`,
   `lean/thm/BigEndHalt.lean`: the small-end check raised to 769 at the loop entries, which all pass, and a round-7
   break past 2⁴¹ ends at no right end up to 768), so every halting class with R below 769 is out of reach, whatever its
   route, among them the R = 182 families of `reentry6_open_halt` and all those of the census at R = 486. What is left
   of the second question is the pass starts with R ≥ 769 and that shape (`never_halts_of_big`). The census has two
   lanes of halting classes there that recur at every R ≡ 486 (mod 512 or 1,024) and every scale Q + 636 = 2^j
   (`lanes_delta_eps.txt` in the halting-classes project files); their re-entry into the loop is deep enough that
   R′³/L₁′² does not exclude them below about 2⁴⁷. But an untrusted count of every pass start up to width 2⁶³ of the
   chains from the loop entries of the 36- and 40-digit trees (`runs/chain_lanes.py`: 193,242 classes of one coordinate
   from 169,631 entries, at most five steps from the entry) meets none of the census lanes through R = 1,004 and at
   eight R near 5,000, δ and ε included. Deeper trees find more entries (in the blank-tape run's sample, 3 in 26,961
   first entries lie in no 40-digit class, `runs/entry_member.py`), and the cut classes keep their number at every
   depth. For most census routes the entry does not matter: R′³/L₁′² at the route's re-entry is too large at every pass
   start of the lane with R ≥ 769, the far shape and width ≥ 2⁴¹ (`runs/lane_sigma.py`, untrusted). The six routes it
   leaves against a close, on two lanes (Q + 636: δ, ε, and ε′ and ζ from the census near R = 5,000; Q + 316: two routes
   at R = 5,350), escape it only below width 2^43.7 (2^54.1 against any end below 178; from a width of 2²⁴ a close at
   the chain's end is p full passes, `LoopChain.close_wide`, so its right end R′/16^p is in the closing set and its L₁,
   L₁′/64^p, in that end's class, which on a lane value allows at most 4 at 2^j and 13.5 at 3 · 2^j; with that L₁ itself
   only ε and ε′ are left, `runs/close_l1.py`), and at those lane values the halting side finds no pass start with the
   far shape on any of them (`routes/README.md` and `routes/far_shape.txt` in its project files, untrusted: each class's
   step in R is taken from three R and checked at three far R). So, untrusted, none of those routes reaches a halt from
   the chain's last pass start, from any entry. (A route after the half pass from R = 812 was among them until the
   halting side found that its last listed start, in round 15, is inside a full pass; the filter now takes such a path
   at the pass's next phase-0 start, where that route is out.) γ's lane Q + 5,116 carries 21 more paths
   (`routes/lanes_q5116_forms.txt`, `routes/lanes_q5116_new17_forms.txt`), which the filter leaves up to width 2^53.7,
   and the next lane of its family, Q + 10,236, 20 more (`routes/lanes_q10236_forms.txt`), up to 2^55.7. On two of them
   there are pass starts with R ≥ 769, the far shape and width above 2⁴¹ that halt, at Q + 5,116 = 3 · 2³⁹
   (`lane769_far_wide` in `lean/thm/LaneHalt.lean`, kernel-checked), so at the proved bound the shape alone does not
   rule the halt out there. With the exhaustive check to 64 digits (every clean tape below width 2⁶⁶ reaches a wider
   one; untrusted) in `blank_halt_open_of` in place of `stepsBelow_direct` (the clean tapes up to 2⁴¹), the pass start
   is wider than 2⁶⁶, and then the filter alone rules out every route and path found against a close, and all but 26
   paths against any end below 178 (six of γ's, at 2⁶⁶ and 3 · 2⁶⁴, and the 20 on Q + 10,236, at 2⁶⁴ to 2⁶⁸; b is even
   at a phase-0 start, so an end r allows only r³/16, not 177³/9), and all but 8 of those: 18 need only the lines of
   pass starts (r, L₁) = (96, −4) and (128, −4), and every pass start with R ≡ 0 (mod 4), R ≥ 8 and L₁ ≡ 4 (mod 8)
   reaches a clean tape after five rounds (`pass_clean_l4`, `lean/thm/PassClean.lean`, kernel-checked), so at the ends
   that are multiples of 4 from 8 up |L₁| ≥ 10; the 8 left, the round-39 paths on Q + 10,236 at 2⁶⁴, need (128, −18),
   (128, 10) or (128, 24), lines on which the halting side's explorer finds only clean leaves and depth cuts
   (`routes/small_ends.txt`, untrusted), and none of which the 8 can reach: full passes divide L₁ by exactly 64, so the
   end's L₁ is L₁′/2⁵⁴, and on their pass starts at 2⁶⁴ that lies in intervals such as [−14.2, −13.3] with no
   value ≡ 10 (mod 14) (`runs/end_l1.py`, untrusted, the forms taken at every R as in `lane_sigma.py`); the chains from
   the 36- and 40-digit entries meet none of those (`runs/chain_lanes.py`, to width 2⁷⁴), and from every one of their
   pass starts on a census lane or on a lane of the family Q + 5 · 2^k − 4 = 2^j or 3 · 2^j, at any k, to width 2²⁵⁶
   (116 of them) the run goes on to a clean tape (the mark model from its entry; the first two also by the halting
   side's census at each exact start). But the family goes on for every k ≡ 2 or 3 (mod 4), with (k − 6)/4 or (k − 7)/4
   passes of a loop on four marks before the re-entry (the route-completeness side, `routes/loop4/README.md`), each pass
   leaving R′³/L₁′² 12 bits weaker (on the paths followed at k = 14, 15, 19, 23 and 27), so at 2⁶⁶ the filter leaves
   those at k = 14 and 15 against any end below 178, by the end's own L₁ too (all 24 paths of the census at k = 14 and
   its 18 at k = 15; on the 89 lines (r, ℓ) those ends need the halting side's line explorer finds only clean leaves and
   depth cuts, `routes/small_ends.txt`, untrusted), and two at k = 15 and all from k = 19 on against a close as well, by
   its own L₁ too, and no floor closes the family: that needs an argument over the 4-wall loop (its invariant
   r³/Λ²) or the far shape. What is needed is a proof (the routes' forms in Lean, and the exhaustive check or the
   far-shape search) and, on the halting side, every halting class at every R: the censuses had missed ζ, the route at
   R ≡ 1,702 and γ's paths until run at every R of a class.
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
   **Deeper trees do not close them either (October 27, `lean/END_TO_END.md`, "Deeper trees"):** at 40 and 44 digits
   the clean-tape tree with loop entries leaves 6,582,732 and 33,928,389 classes (measure 6.0 × 10⁻⁶ and 1.93 × 10⁻⁶,
   `native_decide`), but below almost every class cut at b digits a deeper tree still cuts, so the number of open
   classes at b digits stays put: each holds a 2-adic value of W/2 that no depth settles, and only an argument that
   uses that W is an integer could close it.
   **Nor does integrality, short of a question of the Collatz kind (October 27, `integ/INTEGRALITY.md`):** a class holds
   not one such value but a Cantor set of them (below every class cut at 24 digits but 2, the tree of depth 36 still
   cuts 42 to 304 classes, `integ/SpineCount.lean`, `native_decide`), single two-marker segments branch too, and the
   only odd-modulus invariant is the known count of 1s mod 3, so no never-zero countdown can close a class: it would
   vanish at infinitely many 2-adic points. The tree follows a width for about as many digits as it has; whether every
   width then settles is the open question.

## Practical notes

- Native compilation of the tree builders: `lean FILE.lean -c FILE.c` for every module, compile with
  `gcc -O2 -fwrapv -I$LEAN_PREFIX/include`, link with `$LEANLIB/libInit.a $LEANLIB/libleanrt.a -luv -lpthread -ldl
  -lm -lstdc++`. The tree builders are 10–100 times faster native than under `lean --run`.
- `dfs/run_parts.sh K nparts splitlvl outdir` runs the exhaustive check in parts, two at a time; set `BIN` to the
  compiled `csearch/nrefdfs2.c`, or past 60 digits `csearch/nrefdfs2w.c` (the 64-bit engine overflows there; the
  64-digit run was 1536 parts at split level 33, about 420 CPU hours). `dfs/merge.py` merges the parts.
- The trailing-wall slip described in the notes is fixed (October 27) in the Python checkers, the C engines
  `nrefdfs2`, `lined`, `rtree3d`, `rtree3e`, `gx3` and the stepper: they write the canonical form as `roundZ` does, and
  the C engines print how often they do (`trailing-wall canonical forms written: N` on stderr). The other programs in
  `csearch/` still have the slip; port the fix (a few lines in `shift_from`) before using one. After changing a
  simulator, run `simtest/check.sh`, which compares all of them with the proved model and the bare machine.
  `Model.lean` (the list model in Lean, the port of the old simulator) still has it.
