# The route tree in Lean

The route-tree certificate (`../cert/check_tree.py`, `tree36_leaves.txt`) checked the 36-digit route tree over
two-marker states with an independent Python simulator. This folder has the same tree as a Lean theorem about the
machine, built on the proved round model (`BB6/Round.lean`, `roundZ`) and its symbolic mirror (`BB6/SymRound.lean`),
and now at every depth: the tree is built inside the proof by an explorer proved to produce only trees that pass the
check, so the theorem evaluates nothing. A second tree stops at the loop's entries instead of following the loop's
passes, and proves that the loop cannot close from any of them (below, "Loop entries that cannot close").

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

## Loop entries that cannot close

`thm/RouteEntryTheorem.lean` and `thm/RouteEntryHalt.lean`:

```lean
theorem route_tree_entry (Γ d m E : Nat) (hΓ : 8 ≤ Γ) (hm : m % 2 = 0) (hE : E % 2 = 1) (h1 : Γ ≤ m)
    (h2 : m + Γ ≤ E) :
    ∃ n k ms' W', roundsZ 1000 n [⟨.M, m⟩, ⟨.M, E - 2⟩] E = .newRound ms' W' ∧
      steps k (roundStart [⟨.M, m⟩, ⟨.M, E - 2⟩] E) = some (roundStart ms' W') ∧
      ((routeTreeE Γ d).cutMem [(m : Int) / 2, ((E : Int) - 1) / 2] = true ∨ (0 < n ∧ cleanTape ms' W') ∨
        EntryNoClose ms' W')

theorem route_halt (Γ d m E : Nat) (hΓ : 8 ≤ Γ) (hm : m % 2 = 0) (hE : E % 2 = 1) (h1 : Γ ≤ m) (h2 : m + Γ ≤ E)
    (T : Nat) (hT : steps T (roundStart [⟨.M, m⟩, ⟨.M, E - 2⟩] E) = none) :
    (routeTreeE Γ d).cutMem [(m : Int) / 2, ((E : Int) - 1) / 2] = true ∨
    ∃ n k ms' W', roundsZ 1000 n [⟨.M, m⟩, ⟨.M, E - 2⟩] E = .newRound ms' W' ∧
      steps k (roundStart [⟨.M, m⟩, ⟨.M, E - 2⟩] E) = some (roundStart ms' W') ∧
      steps (T - k) (roundStart ms' W') = none ∧
      ((0 < n ∧ cleanTape ms' W') ∨
        ∃ R ks ms₁ W₁ R₁, PassStart448 ms' W' R ∧ 2 ^ 24 ≤ W' ∧ LoopChain ms' W' R ks ms₁ W₁ R₁ ∧
          ∃ n₂ ms'' W'', roundsZ 1000 n₂ ms₁ W₁ = .newRound ms'' W'' ∧ (∀ d ∈ meetsRounds 1000 n₂ ms₁ W₁, 3 ≤ d) ∧
            LoopEnd W₁ R₁ (passL1 ms₁ W₁) n₂ (meetsRounds 1000 n₂ ms₁ W₁) ms'' W'' ∧
            ∃ t, Reach ⟨[], 1, ms'', W''⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t))
```

`thm/RouteEntryMass.lean`, `thm/RouteEntryMass40.lean`:

```lean
theorem route_tree_entry_cut_mass : (routeTreeE 67108864 36).cutMass 36 = 101855 ∧
    (routeTreeE 67108864 36).leaves = (101855, 177001) ∧ (routeTreeE 67108864 36).entries = 5981 ∧
    (routeTreeE 67108864 36).entryMass 36 = 577459574
theorem route_tree_entry_cut_mass40 : (routeTreeE 67108864 40).cutMass 40 = 357237 ∧
    (routeTreeE 67108864 40).leaves = (357237, 599641) ∧ (routeTreeE 67108864 40).entries = 21123 ∧
    (routeTreeE 67108864 40).entryMass 40 = 9239395719
```

A run that reaches a phase-0 pass start goes into the loop, and `routeTree` follows it through the loop's passes,
splitting on the digits of the right end R that each full pass divides by 16, until its depth runs out: most of its
cut classes are such runs. `routeTreeE Γ d` is the same exploration, except that it stops a path at the first round
start that passes the **entry check** (`entryOK`, `BB6/RouteEntry.lean`), decided on the whole class: a phase-0 pass
start (three walls a, b, c, width W, a odd, b even, W even, R = W − c − 1 even and at least 2) with every gap at least
448, width at least 2²⁴ and, when W ≡ 2 (mod 4), the middle wall at least 896 below the width (so that a half pass at
the start lands again on a pass start with every gap at least 448), from which no member of the class closes through
the loop (`EntryNoClose`). Where the
check fails the path goes on as in `routeTree`, so the cut classes of `routeTreeE Γ d` are among those of
`routeTree Γ d`.

What the check proves. After p full passes a close needs R = 16^p·r with r in the closing set
{2, 4, 8, 16, 24, 32, 48, 64, 176} and L₁ = 64^p·ℓ with ℓ in r's class, and every left countdown is ≡ 3 (mod 7)
(`NoCloseAt`). On the class, R and L₁ are affine in the class coordinates. The check first bounds L₁ by R on the cone,
α·R + α₀ ≤ L₁ ≤ β·R + β₀ (decided by `ltDec`; α, β, α₀, β₀ are computed from the ratio L₁/R along the cone's two edges
and its value at the corner, `exclCert`, and only checked), so at a close ℓ lies in a window of width about
(β − α)·r/4^p. For p at least P (4^P above |α|·176 + |α₀| and |β|·176 + |β₀|) only ℓ = 0 is left, which is not
≡ 3 (mod 7). For each smaller p and each r of the closing set, every ℓ of the window in r's class and ≡ 3 (mod 7)
fixes the point of the class by Cramer's rule (R = 16^p·r, L₁ = 64^p·ℓ), and the check verifies that it is not an
integer point of the cone (`solveOut`; on a class of one coordinate, as in the clean-tape tree, R = 16^p·r fixes the
point directly, `solveOut1`). A run from a pass start of width W ≡ 2 (mod 4) can also start the loop with a
half pass (2R′ = R, 2L₁′ = L₁ + 35W − 147R − 60) and then make full passes; the check runs again on those forms,
unless W ≡ 0 (mod 4) on the class. `exclOK_sound` and `entryOK_sound` prove all this.

With the loop's chain (`LoopChain.close_wide`, `thm/LoopTheorem.lean`: from a pass start of width at least 2²⁴, a
close through the loop is p full passes, after at most one half pass at the start), the chain from such an entry
reaches no closing class (`EntryNoClose.no_close`), and with `loop_halt_leaves` (`thm/LoopHalt.lean`: with the
middle-wall condition every landing is again a pass start with every gap at least 448) `entry_halt` follows: from such
an entry a halt needs the loop's chain to end without a close, where the run leaves phase 0 or the halving chain at a
round start that is not three walls, and a stuck configuration after that. `route_halt` puts the two together for a
halting run from a two-marker state, and `blank_halt_route` states it for every two-marker state that a halting run
from blank tape passes. The clean-tape tree stops at the same entries (`cleanTreeGE`, `END_TO_END.md`).

At 36 digits with Γ = 2²⁶ (every pass start in the cone then has width at least 2²⁷, so the width test never fails):
the plain tree cuts the same 407,087 classes as with Γ = 8,000,000, and with the loop entries 101,855 are left
(measure 1.48 × 10⁻⁶, a quarter); 5,981 entry leaves settle 0.84 % of the start class. At 40 digits: 357,237 cut
classes instead of 1,682,946 (measure 3.25 × 10⁻⁷), 21,123 entries. Every pass start that the tree meets passes the
check except 94 at 36 digits (measure 401 / 2^36, of which 280 / 2^36 is cut further down), where a gap of 448 is not
decided on the whole class; none of the other cut classes' runs reaches three walls. The tree with entries is also
faster to build: 66 s at 36 digits and 230 s at 40, against 233 s and 16 min for the plain tree.

## How it is proved

* `BB6/RouteTree.lean` (proved, no `sorry`, standard axioms only): route trees `RTree` with five kinds of node:
  `adv n` (run n rounds, each decided on the class), `split i` (yᵢ = 2zᵢ + ε, as in `SymSplit`), `shear i s`
  (yᵢ = zᵢ + s·zⱼ, a bijection of ℤ², so a split on a binary digit of any linear form in (m, E) halves the class
  exactly as the Python certificate's lattice cosets do), `clean` (the state reached is a clean tape, checked
  symbolically: `symClean`) and `cut` (no claim). `RTree.ok` is the check and `RTree.sound` its soundness theorem for
  the machine: through `symRoundsZ_sound`, `rounds_run` and `steps_seq_any`, at every point of the root class inside
  the cone. Coverage is by construction (every point of a class lies in one child of each split, and a shear is
  invertible), so no partition or prefix-code check is needed. (A sixth kind, `drop z`, which runs the smallest member
  of a class directly, is used only by the clean-tape trees, `END_TO_END.md`; `RTree.ok` rejects it.)
* `BB6/RouteExplore.lean` (proved, standard axioms only): `RTree.explore` builds the tree from the start class. It runs
  rounds one at a time; when a round is undecided it finds the first meeting whose distance is not decided mod 2 or
  mod 4 and splits on that digit (a shear first when both coordinates enter it); it stops a path at the first clean
  tape after at least one round, and cuts it after d splits, or where a round halts, is not covered or cannot be
  decided by a residue split (an undecided order test). `explore_ok`: **every tree it builds passes `RTree.ok`**, by
  induction on the exploration, so `RTree.sound` applies to `routeTree Γ d` for every Γ and d without evaluating it.
  `exploreMass` computes the cut measure and the leaf counts of the same exploration without building the tree, and
  `exploreMass_eq` says that they are those of `routeTree Γ d`.
* `thm/RouteMass.lean`, `thm/RouteMass40.lean`: `exploreMass` evaluated with `native_decide`.
* `BB6/RouteEntry.lean` (proved, standard axioms only): the entry check `entryOK` and its soundness `entryOK_sound`
  (above). `BB6/EntryTree.lean` (proved): route trees with a seventh kind of node, `entry`, checked by a given test
  (`RTree.okE`, sound by `RTree.soundE`), the explorer `RTree.exploreE`, which stops a path at the first round start
  that passes it, with `exploreE_okE` (every tree it builds passes `RTree.okE`), and `exploreMassE` with
  `exploreMassE_eq` (the measures and leaf counts without the tree).
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

`route_tree_clean`, `route_tree_entry`, `entry_halt`, `route_halt` and `blank_halt_route`: Lean's kernel (`propext`,
`Classical.choice`, `Quot.sound`). The measures (`route_mass_36`, `route_mass_40`, `route_entry_mass_36`,
`route_entry_mass_40`): Lean's compiler as well, through `native_decide`; with `--fast`, `check_route.sh` compiles the BB6
modules to C with `lean -c`, builds them with `leanc` (clang) into a shared library and loads it with
`--load-dynlib`, so that `native_decide` calls native code instead of Lean's interpreter, which adds the C compiler to
the trusted base. No theorem about the machine uses the measures.

## Running time (Lean 4.34.0 release build, one core, native code via `--fast`)

| step | time |
|---|---|
| `BB6/RouteTree.lean`, `BB6/RouteExplore.lean`, `thm/RouteTheorem.lean` | seconds |
| `thm/RouteMass.lean` (36 digits, 946,207 leaves) | 3 min 48 s |
| `thm/RouteMass40.lean` (40 digits, 3,949,190 leaves) | 15 min 52 s |
| `thm/RouteEntryMass.lean` (36 digits, with loop entries: 284,837 leaves) | 1 min 0 s |
| `thm/RouteEntryMass40.lean` (40 digits, with loop entries: 978,001 leaves) | 3 min 44 s |

The Python checker takes hours on the same trees.

## What is not in Lean

* **The σ ceilings** of the loop entries met along the paths (the "ways into the loop have ceilings" numbers: largest
  ceiling 35.906 at 36 digits; the Python checker computes them in floating point). They are not needed for the
  entries the tree with loop entries settles: from those the loop cannot close at any width. What is left are the 94
  pass starts at 36 digits whose gaps are not all decided to be at least 448 (measure 401 / 2^36).
* **What happens after the loop.** From an entry, a halt needs the loop's chain to end where the run leaves three
  walls, and a stuck configuration after that; the run after the loop's end is not followed here. The pass-start trees
  follow it (`pass_halt_chain`), and `blank_halt_pass` joins them to the clean-tape tree's loop entries
  (`END_TO_END.md`).
* **The measure of deeper trees.** The theorem holds at every depth; only the measure of the cut classes needs
  evaluation, and that grows with the leaf count (about 1.43-fold per digit): the 46-, 62- and 64-digit trees (up to
  about 10⁹ leaves) are out of reach of one evaluation.
* **Small gaps.** The theorem needs both gaps at least Γ. Two-marker states with a smaller gap are covered only with a
  smaller Γ, where more classes are cut (the exhaustive check covers every clean tape below 2^65).

## How to check

```sh
LEAN=/path/to/lean LEANLIB=/path/to/lib/lean ./check.sh                    # the existing development
LEAN=/path/to/lean LEANLIB=/path/to/lib/lean ./check_route.sh --fast       # the theorems and the 36-digit measures
LEAN=/path/to/lean LEANLIB=/path/to/lib/lean DEPTH=40 ./check_route.sh --fast   # also the 40-digit measures
LEAN=/path/to/lean LEANLIB=/path/to/lib/lean ./check_end.sh                # also route_halt, blank_halt_route
# statistics and the tree itself (optional; after check_route.sh --fast):
LEAN_PATH=/path/to/lib/lean:out lean --load-dynlib=cbuild/so/libBB6.so --run RouteStats.lean route 8000000 36 tree.txt
LEAN_PATH=/path/to/lib/lean:out lean --load-dynlib=cbuild/so/libBB6.so --run RouteStats.lean entry 67108864 36
```
