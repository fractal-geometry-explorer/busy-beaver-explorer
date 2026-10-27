# The route tree in Lean

The route-tree certificate (`../cert/check_tree.py`, `tree36_leaves.txt`) checked the 36-digit route tree over
two-marker states with an independent Python simulator. This folder has the same tree as a Lean theorem about the
machine, built on the proved round model (`BB6/Round.lean`, `roundZ`) and its symbolic mirror (`BB6/SymRound.lean`),
and now at every depth: the tree is built inside the proof by an explorer proved to produce only trees that pass the
check, so the theorem evaluates nothing.

## The statement

`thm/RouteTheorem.lean`:

```lean
theorem route_tree_clean (Γ d m E : Nat) (hΓ : 8 ≤ Γ) (hm : m % 2 = 0) (hE : E % 2 = 1) (h1 : Γ ≤ m)
    (h2 : m + Γ ≤ E) :
    ∃ n k ms' W', roundsZ 1000 n [⟨.M, m⟩, ⟨.M, E - 2⟩] E = .newRound ms' W' ∧
      steps k (roundStart [⟨.M, m⟩, ⟨.M, E - 2⟩] E) = some (roundStart ms' W') ∧
      ((routeTree Γ d).cutMem [(m : Int) / 2, ((E : Int) - 1) / 2] = true ∨ (0 < n ∧ cleanTape ms' W'))
```

`thm/RouteMass.lean` and `thm/RouteMass40.lean`:

```lean
theorem route_tree_cut_mass : (routeTree 8000000 36).cutMass 36 = 407087 ∧
    (routeTree 8000000 36).leaves = (407087, 539120)
theorem route_tree_cut_mass40 : (routeTree 32000000 40).cutMass 40 = 1682946 ∧
    (routeTree 32000000 40).leaves = (1682946, 2266244)
```

In words: for every cone constant Γ ≥ 8 and every depth d, from every two-marker state G 1, M m, M E − 2 (width E,
m even, E odd) whose two gaps m and E − m are at least Γ cells, the machine runs a whole number of rounds of the mark
model without halting and reaches a round start, and either at least one round was run and that round start is a
**clean tape** (`cleanTape`: the gap at 1, at most one marker, the end marker at W − 2; that is, a two-marker state
again, or the bare one-marker tape), or the start lies in one of the **cut** classes of `routeTree Γ d`. `cutMem`
follows the point (m/2, (E − 1)/2) down the tree, so the starts without a claim are named exactly; a class at depth d
has measure 2^−d of the start class. For the cut classes the theorem still says something: the machine runs without
halting through every round the tree followed before cutting.

`#print axioms route_tree_clean` lists only the three standard axioms: the theorem trusts Lean's kernel and nothing
else. How much it leaves open depends on Γ and d, and that is evaluated separately: at 36 digits with Γ = 8,000,000,
407,087 cut classes (all at depth 36) of total measure 407,087 / 2^36 ≈ 5.92 × 10⁻⁶; at 40 digits with
Γ = 32,000,000, 1,682,946 (all at depth 40) of measure 1.53 × 10⁻⁶. These are the Python certificate's numbers
(`../cert/check_tree36.out`: 946,207 leaves, 539,120 clean and 407,087 cut; `check_tree40*.out`: 3,949,190 leaves,
2,266,244 clean and 1,682,946 cut).

## How it is proved

* `BB6/RouteTree.lean` (proved, no `sorry`, standard axioms only): route trees `RTree` with five kinds of node:
  `adv n` (run n rounds, each decided on the class), `split i` (yᵢ = 2zᵢ + ε, as in `SymSplit`), `shear i s`
  (yᵢ = zᵢ + s·zⱼ, a bijection of ℤ², so a split on a binary digit of any linear form in (m, E) halves the class
  exactly as the Python certificate's lattice cosets do), `clean` (the state reached is a clean tape, checked
  symbolically: `symClean`) and `cut` (no claim). `RTree.ok` is the check and `RTree.sound` its soundness theorem for
  the machine: through `symRoundsZ_sound`, `rounds_run` and `steps_seq_any`, at every point of the root class inside
  the cone. Coverage is by construction (every point of a class lies in one child of each split, and a shear is
  invertible), so no partition or prefix-code check is needed.
* `BB6/RouteExplore.lean` (proved, standard axioms only): `RTree.explore` builds the tree from the start class. It runs
  rounds one at a time; when a round is undecided it finds the first meeting whose distance is not decided mod 2 or
  mod 4 and splits on that digit (a shear first when both coordinates enter it); it stops a path at the first clean
  tape after at least one round, and cuts it after d splits, or where a round halts, is not covered or cannot be
  decided by a residue split (an undecided order test). `explore_ok`: **every tree it builds passes `RTree.ok`**, by
  induction on the exploration, so `RTree.sound` applies to `routeTree Γ d` for every Γ and d without evaluating it.
  `exploreMass` computes the cut measure and the leaf counts of the same exploration without building the tree, and
  `exploreMass_eq` says that they are those of `routeTree Γ d`.
* `thm/RouteMass.lean`, `thm/RouteMass40.lean`: `exploreMass` evaluated with `native_decide`.
* `RouteStats.lean` (untrusted driver, `lean --run`): runs the explorer, prints the leaf counts, the cut measure, the
  longest path and the cut leaves above full depth, and can write the tree out; nothing it writes is read by a proof.

Before the explorer was proved, an untrusted program (`ExploreRT.lean`) built the tree, it was written out (4 million
tokens at 36 digits, 50 MB at 40) and `RTree.ok` was evaluated on it with `native_decide`, so the theorem trusted the
compiler and stopped at the depth whose tree could be written out.

The cone constant: the Python checker reports that its cone decisions are exact once every gap exceeds 7,340,032 cells
at 36 digits (29,360,128 at 40); the proved model makes a few extra decisions, and 8,000,000 (36 digits) and
32,000,000 (40 digits) suffice for all of them: no class is cut early. The theorem holds for every Γ ≥ 8; a smaller Γ
only cuts more classes, where an order test is not decided on the cone.

## What is trusted

`route_tree_clean`: Lean's kernel (`propext`, `Classical.choice`, `Quot.sound`). The measures (`route_mass_36`,
`route_mass_40`): Lean's compiler as well, through `native_decide`; with `--fast`, `check_route.sh` compiles the BB6
modules to C with `lean -c`, builds them with `leanc` (clang) into a shared library and loads it with
`--load-dynlib`, so that `native_decide` calls native code instead of Lean's interpreter, which adds the C compiler to
the trusted base. No theorem about the machine uses the measures.

## Running time (Lean 4.34.0 release build, one core, native code via `--fast`)

| step | time |
|---|---|
| `BB6/RouteTree.lean`, `BB6/RouteExplore.lean`, `thm/RouteTheorem.lean` | seconds |
| `thm/RouteMass.lean` (36 digits, 946,207 leaves) | 3 min 48 s |
| `thm/RouteMass40.lean` (40 digits, 3,949,190 leaves) | 15 min 52 s |

The Python checker takes hours on the same trees.

## What is not in Lean

* **The σ ceilings** of the loop entries met along the paths (the "ways into the loop have ceilings" numbers: largest
  ceiling 35.906 at 36 digits). The Python checker computes them by sampling the leading terms at 1,025 ratios m/E in
  floating point, so they are numerical estimates even there; a Lean version needs a statement of the ceiling as an
  inequality between polynomials in (m, E) on each class and a proof of it. The phase-0 pass starts themselves are
  available: they are states on the tree's paths, as affine forms in the class coordinates.
* **The measure of deeper trees.** The theorem holds at every depth; only the measure of the cut classes needs
  evaluation, and that grows with the leaf count (about 1.43-fold per digit): the 46-, 62- and 64-digit trees (up to
  about 10⁹ leaves) are out of reach of one evaluation.
* **Small gaps.** The theorem needs both gaps at least Γ. Two-marker states with a smaller gap are covered only with a
  smaller Γ, where more classes are cut (the exhaustive check covers every clean tape below 2^61).

## How to check

```sh
LEAN=/path/to/lean LEANLIB=/path/to/lib/lean ./check.sh                    # the existing development
LEAN=/path/to/lean LEANLIB=/path/to/lib/lean ./check_route.sh --fast       # the theorem and the 36-digit measure
LEAN=/path/to/lean LEANLIB=/path/to/lib/lean DEPTH=40 ./check_route.sh --fast   # also the 40-digit measure
# statistics and the tree itself (optional; after check_route.sh --fast):
LEAN_PATH=/path/to/lib/lean:out lean --load-dynlib=cbuild/so/libBB6.so --run RouteStats.lean route 8000000 36 tree.txt
```
