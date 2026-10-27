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

1. **The loop's end for every width as one Lean theorem.** Prove the pass map (R → R/16, L → L/64) with R free
   using the symbolic runner (`BB6/SymRound`, `BB6/SymSplit`), then induct over passes, combined with
   `endgame_no_close` for R ≤ 4096: "a run through the loop closes only from R ∈ {2, 4, 8, 16, 24, 32, 48, 64, 176}
   at its last pass start, hence log₂W ≤ σ + 6.38".
2. **"A halt needs a close", formally**: from a well-formed state the model is uncovered only at contacts; show which
   contacts are reachable, so that "no close" over a stretch becomes "no halt" for whole runs.
3. **Remove the compiler trust** from the two theorems (kernel evaluation, or compact per-tree certificates).
4. **The route-tree certificate in Lean** (the "ways into the loop have ceilings" results).
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
