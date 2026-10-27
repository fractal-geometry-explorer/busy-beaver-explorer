# The route tree in Lean

The route-tree certificate (`../cert/check_tree.py`, `tree36_leaves.txt`) checked the 36-digit route tree over
two-marker states with an independent Python simulator. This folder now has the same tree as a Lean theorem about the
machine, built on the proved round model (`BB6/Round.lean`, `roundZ`) and its symbolic mirror (`BB6/SymRound.lean`).

## The statement

`thm/RouteTheorem.lean`:

```lean
theorem route_tree_clean (m E : Nat) (hm : m % 2 = 0) (hE : E % 2 = 1) (h1 : 8000000 ≤ m) (h2 : m + 8000000 ≤ E) :
    ∃ n k ms' W', roundsZ 1000 n [⟨.M, m⟩, ⟨.M, E - 2⟩] E = .newRound ms' W' ∧
      steps k (roundStart [⟨.M, m⟩, ⟨.M, E - 2⟩] E) = some (roundStart ms' W') ∧
      (routeTree.cutMem [(m : Int) / 2, ((E : Int) - 1) / 2] = true ∨ (0 < n ∧ cleanTape ms' W'))

theorem route_tree_cut_mass : routeTree.cutMass 36 = 407087 ∧ routeTree.leaves = (407087, 539120)
```

In words: from every two-marker state G 1, M m, M E − 2 (width E, m even, E odd) whose two gaps m and E − m are at
least 8,000,000 cells, the machine runs a whole number of rounds of the mark model without halting and reaches a round
start, and either at least one round was run and that round start is a **clean tape** (`cleanTape`: the gap at 1, at
most one marker, the end marker at W − 2; that is, a two-marker state again, or the bare one-marker tape), or the start
lies in one of the tree's **cut** classes. `cutMem` follows the point (m/2, (E − 1)/2) down the tree, so the starts
without a claim are named exactly; they are 407,087 classes of total measure 407,087 / 2^36 ≈ 5.92 × 10⁻⁶ of the start
class (a class at depth d has measure 2^−d). For the cut classes the theorem still says something: the machine runs
without halting through every round the tree followed before cutting.

Leaf counts and the cut measure are the same as the Python certificate's (`../cert/check_tree36.out`: 946,207 leaves,
539,120 clean and 407,087 cut, cut measure 5.9239 × 10⁻⁶). The Lean tree was built independently from the proved
model, not read from `tree36_leaves.txt`.

## How it is proved

* `BB6/RouteTree.lean` (proved, no `sorry`, standard axioms only): route trees `RTree` with five kinds of node:
  `adv n` (run n rounds, each decided on the class; the rounds sit on the tree's edges, so no round is replayed per
  leaf), `split i` (yᵢ = 2zᵢ + ε, as in `SymSplit`), `shear i s` (yᵢ = zᵢ + s·zⱼ, a bijection of ℤ², so a split on a
  binary digit of any linear form in (m, E) halves the class exactly as the Python certificate's lattice cosets do),
  `clean` (the state reached is a clean tape, checked symbolically: `symClean`) and `cut` (no claim). `RTree.ok` is the
  check and `RTree.sound` its soundness theorem for the machine: through `symRoundsZ_sound`, `rounds_run` and
  `steps_seq_any`, at every point of the root class inside the cone. Coverage is by construction (every point of a
  class lies in one child of each split, and a shear is invertible), so no partition or prefix-code check is needed.
* `ExploreRT.lean` (untrusted): builds the tree. It runs rounds; when a round is undecided it finds the first meeting
  whose distance d is not decided mod 2 or mod 4 and splits on that digit (a shear first when both coordinates enter
  it); it stops at the first clean tape after at least one round, or cuts a path once it has made 36 splits. It never
  met a halt, an `uncovered` configuration, or an undecided order test.
* `thm/gen_route.py` writes `thm/RouteTheorem.lean` from the serialized tree (`thm/route_tree36.txt.gz`, 4.0 million
  tokens), with the decoder, `route_tree_ok` (`RTree.ok … = true` by `native_decide`), the leaf counts and cut measure
  (by `native_decide`), and the corollary in plain terms.

The cone threshold is one constant for both gaps, Γ = 8,000,000. The Python checker reports that its cone decisions
are exact once every gap exceeds 7,340,032 cells; the proved model makes a few extra decisions, and 8,000,000 suffices
for all of them at 36 digits. Deeper trees need a larger Γ (the threshold grows with the number of end meetings).

## What is trusted

As for `exit_no_halt` and `endgame_no_close`: Lean's kernel, plus Lean's compiler through `native_decide`
(`#print axioms route_tree_clean` lists `route_tree_ok._native.native_decide.ax_1_1` besides the three standard
axioms). With `--fast`, `check_route.sh` also compiles the BB6 modules to C with `lean -c`, builds them with `leanc`
(clang) into a shared library and loads it with `--load-dynlib`, so that `native_decide` calls native code for the
proved check instead of Lean's interpreter; this adds the C compiler to the trusted base and changes nothing else.

## Running time (Lean 4.34.0 release build, one core)

| step | time |
|---|---|
| `BB6/RouteTree.lean` | a few seconds |
| building the 36-digit tree (`ExploreRT`, native, `cbuild_rt.sh`) | 8 minutes |
| `thm/RouteTheorem.lean`, interpreted `native_decide` | RT36_INTERP |
| `thm/RouteTheorem.lean`, `--fast` (native code via `--load-dynlib`) | 2 min 53 s |
| the same at 32 digits (226,532 leaves): interpreted / `--fast` | 4 min 48 s / 38 s |
| the same at 24 digits (12,752 leaves): interpreted / `--fast` | 15 s / 2.3 s |

The Python checker takes hours on the same tree.

## What is not in Lean

* **The σ ceilings** of the loop entries met along the paths (the "ways into the loop have ceilings" numbers: largest
  ceiling 35.906 at 36 digits). The Python checker computes them by sampling the leading terms at 1,025 ratios m/E in
  floating point, so they are numerical estimates even there; a Lean version needs a statement of the ceiling as an
  inequality between polynomials in (m, E) on each class and a proof of it. The phase-0 pass starts themselves are
  available: they are states on the tree's paths, as affine forms in the class coordinates.
* **Deeper trees.** The 40-digit tree (about 4 million leaves) should go the same way with a larger Γ (the Python
  checker needs 29,360,128 there); the 46-, 62- and 64-digit trees (up to about 10⁹ leaves) are out of
  reach of a tree written out in full.
* **Small gaps.** The theorem needs both gaps at least 8,000,000. Two-marker states with a smaller gap are not covered
  here (the exhaustive check covers every clean tape below 2^61).

## How to check

```sh
LEAN=/path/to/lean LEANLIB=/path/to/lib/lean ./check.sh          # the existing development
LEAN=/path/to/lean LEANLIB=/path/to/lib/lean ./check_route.sh --fast
# rebuild the tree (optional):
LEAN=/path/to/lean LEANLIB=/path/to/lib/lean ./cbuild_rt.sh && ./cbuild/ExploreRT 36 8000000 thm/route_tree36.txt
```
