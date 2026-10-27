# End to end: what a halt from blank tape needs

`thm/EndToEnd.lean` puts the Lean results together into one statement about the machine
`1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LD1RE` started on blank tape. It does not settle the question. It says exactly
where a halt would have to come from: a clean tape of width at least 2³² that the clean-tape tree leaves open at
**every** depth. At 36 digits the classes it leaves open have measure 2.4 × 10⁻⁵, at 40 digits 8.4 × 10⁻⁶. With the
clean tapes below 2⁴¹ in those classes run one by one (`thm/EndToEndDirect.lean`, 26,509,316 runs), the clean tape a
halt needs is at least 2⁴¹ wide. The same statement from width 2²⁰ (`blank_halt_structure_kernel`) is checked by
Lean's kernel alone, with no `native_decide`; the tree it uses, over the widths ≥ 2²⁰, leaves classes of measure
2.9 × 10⁻⁵ open at 36 digits.

## The statement

```lean
theorem blank_halt_clean (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    ∃ W k, prefixWidth ≤ W ∧ W % 2 = 0 ∧ (∀ d, (cleanTree d).cutMem [(W : Int) / 2, 0] = true) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W - 2⟩] W) ∧
      steps (T - k) (roundStart [⟨.M, W - 2⟩] W) = none ∧
      ∃ t, Reach ⟨[], 1, [⟨.M, W - 2⟩], W⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)

theorem blank_halt_loop (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    ∀ (R : Nat) (ms : List Mark) (W k : Nat), PassStart448 ms W R →
      steps k ⟨blank, blank, .A⟩ = some (roundStart ms W) →
      ∃ n₁ ms₁ W₁ R₁, roundsZ 1000 n₁ ms W = .newRound ms₁ W₁ ∧ (∀ d ∈ meetsRounds 1000 n₁ ms W, 3 ≤ d) ∧
        PassStart448 ms₁ W₁ R₁ ∧ R₁ ≤ R ∧
        ((InCloseClass ms₁ W₁ R₁ ∧ ∃ t, Reach ⟨[], 1, ms₁, W₁⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) ∨
          ∃ n₂ ms' W', roundsZ 1000 n₂ ms₁ W₁ = .newRound ms' W' ∧ (∀ d ∈ meetsRounds 1000 n₂ ms₁ W₁, 3 ≤ d) ∧
            LoopEnd 1000 R₁ n₂ (meetsRounds 1000 n₂ ms₁ W₁) ms' W' ∧
            ∃ t, Reach ⟨[], 1, ms', W'⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t))

theorem blank_halt_exit (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    ∀ a b c E k, …loop state, gaps ≥ 390… →
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] E) →
      ∃ n ms' W', roundsZ 1000 n … = .newRound ms' W' ∧ (∀ d ∈ meetsRounds 1000 n …, 3 ≤ d) ∧
        ExitEvent n (meetsRounds 1000 n …) ms' W' ∧
        ∃ t, Reach ⟨[], 1, ms', W'⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)

theorem blank_halt_structure (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) : … -- the three together

theorem never_halts_of_cut_classes
    (h : ∀ W, prefixWidth ≤ W → W % 2 = 0 → (∀ d, (cleanTree d).cutMem [(W : Int) / 2, 0] = true) →
      ∀ T, steps T (roundStart [⟨.M, W - 2⟩] W) ≠ none) :
    ∀ T, steps T ⟨blank, blank, .A⟩ ≠ none

theorem blank_halt_clean_direct (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :   -- thm/EndToEndDirect.lean
    ∃ W k, directWidth ≤ W ∧ W % 2 = 0 ∧ (∀ d, (cleanTreeG directWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W - 2⟩] W) ∧
      steps (T - k) (roundStart [⟨.M, W - 2⟩] W) = none ∧
      ∃ t, Reach ⟨[], 1, [⟨.M, W - 2⟩], W⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)

theorem blank_halt_clean_kernel (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :   -- no native_decide
    ∃ W k, kernelPrefixWidth ≤ W ∧ W % 2 = 0 ∧
      (∀ d, (cleanTreeG kernelPrefixWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W - 2⟩] W) ∧
      steps (T - k) (roundStart [⟨.M, W - 2⟩] W) = none ∧
      ∃ t, Reach ⟨[], 1, [⟨.M, W - 2⟩], W⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)

theorem blank_halt_structure_kernel (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) : …
  -- blank_halt_clean_kernel, blank_halt_loop and blank_halt_exit together

theorem never_halts_of_cut_classes_kernel
    (h : ∀ W, kernelPrefixWidth ≤ W → W % 2 = 0 →
      (∀ d, (cleanTreeG kernelPrefixWidth d).cutMem [(W : Int) / 2, 0] = true) →
      ∀ T, steps T (roundStart [⟨.M, W - 2⟩] W) ≠ none) :
    ∀ T, steps T ⟨blank, blank, .A⟩ ≠ none
```

In words: if the machine halts from blank tape, then

1. on the way it reaches a **clean tape** (the gap at 1, then only the end marker M at W − 2) of even width
   W ≥ 2³² = 4,294,967,296 whose half W/2 lies in a **cut class** of the clean-tape tree **at every depth** d, and it
   halts from that clean tape;
2. the mark model, run on from that clean tape, reaches a **stuck configuration**: a close at the right end (the gap
   meets the end marker at distance 0, or touches a block at the end of the tape) or an interior contact;
3. every **phase-0 pass start** it passes on the way (walls at a, b, E − R − 1, width E, a odd, b even, E even, every
   gap ≥ 448: `PassStart448`) is followed by a close-free stretch the model covers, through the pass starts whose gaps
   are again all ≥ 448 to the last of them (right end R₁ ≤ R), and the halt needs a stuck configuration after it:
   either right there, with R₁ in the closing set {2, 4, 8, 16, 24, 32, 48, 64, 176} and L₁ in R₁'s class
   (`InCloseClass`), or after a further close-free stretch to where the run leaves the loop (`LoopEnd`: it leaves
   phase 0, its end meetings leave the halving chain, or it reaches the next pass start, and it is not at a pass
   start with every gap ≥ 448 there);
4. every **loop state** it passes on the way (walls at a, b, c, width E, a odd, b even, c odd, E even, every gap ≥ 390)
   is followed by the certified exit stretch, close-free to where it ends (`ExitEvent`: a clean tape, a break of the
   end-meeting chain, or a loop state again after a full pass), and the halt needs a stuck configuration after it.

`blank_halt_clean` is items 1 and 2, `blank_halt_loop` item 3, `blank_halt_exit` item 4, and `blank_halt_structure`
all four.

**Why the stretches name their ends** (October 27). The first versions of items 3 and 4 said only "the model covers n
rounds from the start, with no close, and the halt needs a stuck configuration after them". With n = 0 that is just
the round theorem: it holds for every start, with no tree. The trees' leaves now end at events stated in
`BB6/Ends.lean`, none of which holds after zero rounds, so the stretches are real: from a pass start the run is
followed until it leaves phase 0, breaks the end-meeting chain, or reaches the next pass start, and through every pass
start whose gaps stay ≥ 448; from a loop state, until a clean tape, a chain break, or a loop state again.

`never_halts_of_cut_classes` is item 1 read backwards: the open question is now only about the clean tapes of width
at least 2³² that the tree leaves open at every depth. Since `∀ d` includes d = 36 and d = 40, such a clean tape lies
in the cut classes whose measure `thm/CleanMass.lean` and `thm/CleanMass40.lean` evaluate.

`blank_halt_clean_direct` and `never_halts_of_cut_classes_direct` (`thm/EndToEndDirect.lean`) are items 1 and 2 with
2⁴¹ for 2³²: every clean tape of width in [2³², 2⁴¹) reaches a wider one (`clean_step_direct`, below), so the clean
tape a halt needs is at least 2⁴¹ wide, and it lies in the cut classes at every depth of `cleanTreeG 2⁴¹ d`, the same
exploration with the cone W ≥ 2⁴¹. They trust one more evaluation (`clean_direct_ok`).

`blank_halt_clean_kernel`, `blank_halt_structure_kernel` and `never_halts_of_cut_classes_kernel` are the same with
2²⁰ = 1,048,576 for 2³², and they trust no evaluation by compiled code: `#print axioms` lists `propext`,
`Classical.choice` and `Quot.sound` alone. The run from blank tape to the clean tape of width 2²⁰ is checked by Lean's
kernel (`blank_prefix_kernel`, below), and from there on the clean-tape tree over the widths ≥ 2²⁰
(`cleanTreeG 2²⁰ d`, from the same proved explorer) takes over: `blank_halt_clean_from` with A = B = 2²⁰, so nothing
is run in between. The price is a larger measure of cut classes, from the cone's edge (below): at 36 digits the tree
leaves 1,653,905 classes of measure 2,018,149 / 2³⁶ ≈ 2.9 × 10⁻⁵ open (`thm/CleanKernelMass.lean`), against 1,660,017
of measure 1,660,086 / 2³⁶ ≈ 2.4 × 10⁻⁵ over the widths ≥ 2³².

## The pieces

| file | result | how |
|---|---|---|
| `thm/Prefix.lean` | `blank_prefix`: from blank tape the machine reaches the clean tape of width exactly 2³², without halting | the mark model from the first round start, 1,204,297,272 rounds, evaluated by `native_decide`, then `blank_rounds` |
| `thm/PrefixKernel.lean` (generated by `thm/gen_prefix.py` from the checkpoints of `PrefixGen.lean`) | `blank_prefix_kernel`: from blank tape the machine reaches the clean tape of width exactly 2²⁰, without halting | 294,033 rounds in 59 stretches of 5,000, each checked by the kernel (`decide +kernel`, `thm/PrefixPieces*.lean`), chained by `roundsZ_chain` |
| `BB6/CleanTree.lean` | `RTree.okW` / `RTree.soundW`: a route tree whose `clean` leaves are one-marker clean tapes **wider** than the start; `roundStart_one_ne`: clean tapes of different widths are different configurations | proved, standard axioms |
| `BB6/RouteExplore.lean` | `RTree.exploreW`: builds the clean-tape tree to any depth; `exploreW_okW`: every tree it builds passes `RTree.okW`; `exploreMassW`: its cut measure and leaf counts without the tree | proved, standard axioms |
| `thm/CleanTheorem.lean` | `clean_tree_step_G`: for every Γ ≥ 6 and every depth d, from every clean tape of even width W ≥ Γ, the machine reaches a wider clean tape without halting, unless W/2 is in a cut class of `cleanTreeG Γ d`; `clean_tree_step` is Γ = 2³² (`cleanTree d`) | `RTree.soundW` and `exploreW_okW`; nothing evaluated |
| `thm/EndgameTheorem.lean`, `thm/LoopTheorem.lean` | `endgame_stretch`: from a phase-0 pass start with gaps ≥ 448, a close needs R in the closing set and L₁ in R's class, and otherwise the run is close-free to an end event; `loop_stretch`: the same through every pass start with gaps ≥ 448 | the endgame trees checked by the kernel (`Tree.okEnd`, `decide +kernel`); strong induction on R |
| `thm/ExitTheorem.lean` | `exit_stretch`: from a loop state with gaps ≥ 390, the run is close-free to an exit event (`ExitEvent`) | the exit tree checked by the kernel (`Tree.okEnd`, `decide +kernel`) |
| `thm/LoopHalt.lean`, `thm/ExitHalt.lean` | `loop_halt_needs_contact`, `exit_halt_needs_contact`: a halt from a phase-0 pass start with gaps ≥ 448, or from a loop state, needs a stuck configuration after the certified close-free stretch | `loop_stretch`, `exit_stretch` and `halt_after_rounds` |
| `thm/EndToEnd.lean` | `clean_chain`, `blank_halt_clean_from`, `blank_halt_clean`, `blank_halt_clean_kernel`, `blank_halt_loop`, `blank_halt_exit`, `blank_halt_structure`, `blank_halt_structure_kernel`, `never_halts_of_cut_classes`, `never_halts_of_cut_classes_kernel` | strong induction on the halting time: at each clean tape, either it is cut at every depth, or some depth decides it and the run goes on to a wider clean tape, which takes at least one machine step |
| `thm/CleanMass.lean`, `thm/CleanMass40.lean` | `clean_tree_cut_mass`, `clean_tree_cut_mass40`: the leaf counts and cut measure of `cleanTree 36` and `cleanTree 40` | `exploreMassW` evaluated by `native_decide`; used by no theorem about the machine |
| `thm/CleanKernelMass.lean` | `clean_kernel_cut_mass`: the leaf counts and cut measure of `cleanTreeG 2²⁰ 36` | `exploreMassW`, `native_decide`; used by no theorem about the machine |
| `BB6/CleanRange.lean` | `directOK_sound`: a run of the mark model from a clean tape to a wider one, as a statement about the machine; `RTree.cuts1_sound`: the cut classes of a one-variable tree as residues of W/2; `rangeOK_sound`: every clean tape of width in [lo, hi) that the tree leaves open runs directly to a wider one | proved, standard axioms |
| `thm/CleanDirect.lean` | `clean_step_direct`: every clean tape of even width in [2³², 2⁴¹) reaches a wider clean tape, with no exception | `rangeOK` on `cleanTree 36` evaluated by `native_decide` (26,509,316 members of the cut classes, each run to a wider clean tape), and `clean_tree_step` for the rest |
| `thm/EndToEndDirect.lean` | `blank_halt_clean_direct`, `never_halts_of_cut_classes_direct` | `blank_halt_clean_from` (`thm/EndToEnd.lean`: the chain from a clean tape the run reaches, for any bounds A ≤ B with every clean tape of width in [A, B) reaching a wider one, with the tree `cleanTreeG B d` above B) with the prefix to 2³², A = 2³² and B = 2⁴¹ |
| `thm/CleanDirectMass.lean`, `thm/CleanDirectMass40.lean` | `clean_direct_cut_mass`, `clean_direct_cut_mass40`: the leaf counts and cut measure of `cleanTreeG 2⁴¹ 36` and `cleanTreeG 2⁴¹ 40` | `exploreMassW`, `native_decide`; used by no theorem about the machine |

## Why a one-variable tree over clean tapes, and not the two-marker route tree

The route tree (`ROUTE_TREE.md`) starts from two-marker states G 1, M m, M E − 2 with both gaps at least Γ. Chaining
it along the machine's run does not work: the machine's own run reaches two-marker states with a tiny first gap again
and again (for example m = 56 at width 34,478,025, m = 152 at width 12,260,337), which no cone of large gaps contains.
Clean tapes have one number, the width W, and every position on the way to the next clean tape is an affine function
of it, so the cone is just W ≥ Γ, and the clean tapes the run reaches are all wider than the first one. This is the
class tree of the exhaustive check (`../csearch/nrefdfs2.c`), proved: a split on the next binary digit of W/2 when a
round is not decided, and a path stops at the first wider clean tape.

## The clean-tape tree

The tree is built by the proved explorer, so `clean_tree_step` and the end-to-end theorems hold at every depth and
evaluate nothing; the depth only decides how many classes are cut. The cut classes, evaluated (`RouteStats.lean`, and
`thm/CleanMass.lean`, `thm/CleanMass40.lean`, `thm/CleanDirectMass.lean` for 36 and 40 digits), for the tree with the
cone W ≥ 2³² (`cleanTree d`) and the one with the cone W ≥ 2⁴¹ (`cleanTreeG 2⁴¹ d`, used above the direct runs):

| depth | cone 2³²: closed | cut | cut measure | cone 2⁴¹: closed | cut | exhaustive check, open classes |
|---|---|---|---|---|---|---|
| 20 | 1,850 | 1,930 | 1.8 × 10⁻³ | 1,850 | 1,930 | 1,930 |
| 24 | 9,814 | 10,722 | 6.4 × 10⁻⁴ | 9,814 | 10,722 | 10,722 |
| 28 | 52,599 | 57,934 | 2.2 × 10⁻⁴ | 52,599 | 57,934 | 57,934 |
| 32 | 276,728 | 303,560 | 7.1 × 10⁻⁵ | 276,729 | 303,560 | 303,560 |
| 36 | 1,507,364 | 1,660,017 | 2.4 × 10⁻⁵ | 1,507,376 | 1,660,024 | 1,660,024 |
| 40 | 8,107,467 | 9,188,787 | 8.4 × 10⁻⁶ | 8,107,587 | 9,188,899 | 9,188,898 |

The cut classes grow about 1.52-fold per digit, as the open classes of the exhaustive check do (1.53), so the cut
measure falls about 0.76-fold per digit. With the cone W ≥ 2⁴¹ the cut classes are the exhaustive check's open classes
(`../dfs/merged56_fixed.txt`; compared class by class at 36 and 40 digits) but for one class at 40 digits; with the
cone W ≥ 2³² they differ by the few edge classes below. A path is cut when it has made d splits without reaching a
wider clean tape. Longest path at 36 digits: 59 rounds. Every clean leaf is a one-marker clean tape decided to be
wider than the start (`exploreW` stops only where `symClean1` and `widerB` hold, which is what `RTree.okW` checks).

Some cut leaves are instead comparisons that come out differently for the smallest member of a class: 7 at 36
digits, at depth 31 to 35, of measure 76 / 2³⁶ ≈ 1.1 × 10⁻⁹. At depth 31, for example, the class W = 2 + 2³²z
(z ≥ 1) has after 30 rounds the marks M 4z, M 5 + 268,435,464z, W 59 + 2,281,701,380z, and the round asks whether the
first marker is exactly 3 cells right of the gap: 4z = 4, true only for the smallest member, W = 2³² + 2. (Before the
integer-aware `ltDec` the order 4z ≥ 4 was undecided as well, the cone being a condition over the rationals, and that
cut sat one level higher.) A residue split cannot separate the smallest member from the others, so with the cone
W ≥ 2³² these classes are cut at every depth, and the clean tapes left open at every depth are not a set of measure
zero. With the clean tapes below 2⁴¹ run one by one (next section), the tree above 2⁴¹ has the cone W ≥ 2⁴¹, which
leaves these smallest members out (z ≥ 512 in the example): `cleanTreeG 2⁴¹ 36` has 1,660,024 cut leaves, all at
depth 36, and 1,507,376 closed ones (`thm/CleanDirectMass.lean`), exactly the exhaustive check's open classes at 36
digits.

The edge moves with the cone; it does not go away. `cleanTreeG 2⁴¹ 40` has two leaves where a comparison is undecided,
both at depth 40, so they count among its 9,188,899 cut leaves (`thm/CleanDirectMass40.lean`). In the class W = 2 +
2⁴¹z the first marker is at 4z after 39 rounds, and the test is again 4z = 4, true only for the smallest member W =
2⁴¹ + 2 (the example above, one level below the cone's exponent). In the class W = 2⁴⁰ + 2 + 2⁴¹z it is at 2 + 4z, and
the test 2 + 4z = 4 is false for every member but true at z = 1/2 (W = 2⁴¹ + 2 again), which the cone, a condition
over the rationals, contains. The cone W ≥ 2³² has the same pair at depth 31, around W = 2³² + 2. The exhaustive check
keeps an exact integer threshold for each comparison and runs the members below it directly; it leaves the first class
open at 40 digits as well and settles the second, hence its 9,188,898. Both classes stay cut at every depth beyond 40,
so the clean tapes that the tree over the widths ≥ 2⁴¹ leaves open at every depth are not of measure zero either;
their measure is 2 · 2⁻⁴⁰ against 8.4 × 10⁻⁶ for all cut classes at 40 digits.

The cone W ≥ 2²⁰ of the kernel-only theorems has its edge lower, and wider. `cleanTreeG 2²⁰ 36` has 1,074 cut leaves
above depth 36 (`RouteStats.lean`): 2 at depth 19, the same pair one digit below the cone's exponent (W = 2 + 2²⁰z with
4z = 4, and W = 2¹⁹ + 2 + 2²⁰z with 2 + 4z = 4), of measure 2 · 2⁻¹⁹ = 262,144 / 2³⁶; then 1 at depth 22, 4 at 23, 3 at
24, 3 at 25, 13 at 26, 14 at 27 and 28, 23 at 29, 30 at 30, 53 at 31, 106 at 32, 179 at 33, 290 at 34 and 339 at 35,
of measure 103,174 / 2³⁶ together. With its 1,652,831 cut leaves at full depth that is 2,018,149 / 2³⁶ ≈ 2.9 × 10⁻⁵
(`thm/CleanKernelMass.lean`). Running a class's smallest member directly, as the exhaustive check does, and going on
with the cone above it would remove these cuts.

## Clean tapes below 2⁴¹, one by one

The exhaustive check (`../csearch/nrefdfs2.c`) covers the small members of its open classes by running them, up to
2⁶¹. `BB6/CleanRange.lean` does the same in Lean: `directOK W` runs the mark model from the clean tape of width W for
at most 10,000 rounds, until a one-marker clean tape wider than W, and `directOK_sound` turns a run that gets there
into a statement about the machine. `RTree.cuts1` lists the cut classes of a clean-tape tree as residues of W/2
modulo powers of two, `rangeOK lo hi t` runs every member of every cut class with lo ≤ W < hi, and `rangeOK_sound`:
every clean tape of width in [lo, hi) that the tree leaves open passes `directOK`. `thm/CleanDirect.lean` evaluates
`rangeOK 2³² 2⁴¹ (cleanTree 36)` with `native_decide` (26,509,316 clean tapes in the 1,660,017 cut classes,
each run to a wider one in at most 127 rounds), and with `clean_tree_step` for the other clean tapes, `clean_step_direct`: every clean tape of width in
[2³², 2⁴¹) reaches a wider one. `blank_halt_clean_from` (`thm/EndToEnd.lean`) is the chain for any such bound B,
with the tree over the widths ≥ B above it, and `blank_halt_clean_direct` is the case B = 2⁴¹.

## What is trusted

`blank_halt_clean`, `blank_halt_structure` and `never_halts_of_cut_classes`: Lean's kernel, plus Lean's compiler
through `native_decide` for one evaluated check, `prefix_ok` (`#print axioms` lists it besides `propext`,
`Classical.choice` and `Quot.sound`). The clean-tape tree is not evaluated (the proved explorer), and the exit and
endgame trees are checked by the kernel itself (`decide +kernel`, subtree by subtree in `thm/ExitPieces*.lean` and
`thm/EndgamePieces*.lean`, assembled in `thm/ExitTheorem.lean` and `thm/EndgameTheorem.lean`). `blank_halt_clean_direct`
adds the direct runs (`clean_direct_ok`). `check_end.sh` compiles the BB6 modules to a shared library and loads it
with `--load-dynlib`, so that `native_decide` runs native code; this adds the C compiler to the trusted base
(`--interpreted` avoids it, at about an hour for the prefix alone).

`blank_halt_clean_kernel`, `blank_halt_structure_kernel` and `never_halts_of_cut_classes_kernel`: Lean's kernel
alone (`#print axioms` lists `propext`, `Classical.choice` and `Quot.sound`, nothing else). The prefix to 2³² cannot be
moved to kernel evaluation at any reasonable cost (1.2 × 10⁹ rounds; the kernel does about 600 rounds a second on
them), nor can the 26.5 million direct runs, but the run to 2²⁰ can: `blank_prefix_kernel` (`thm/PrefixKernel.lean`)
takes about 2 minutes on 4 cores, and the tree above it, like every clean-tape tree here, is not evaluated at all.

## What is not claimed

* **The clean tapes left open at every depth.** Nothing is said about them: whether the machine halts from one of them
  is exactly what remains open. At each depth they lie in the cut classes of that depth; the measure of those falls
  with the depth, but not to zero with either cone (the edge classes above: from depth 31 for the cone W ≥ 2³², from
  depth 40 for the cone W ≥ 2⁴¹). In Lean such a clean tape is at least 2⁴¹ wide
  (`blank_halt_clean_direct`); combined with the exhaustive check (every clean tape below 2⁶¹ reaches the next one
  without halting; a C computation, not in Lean), at least 2⁶¹.
* **Item 3** is a statement about the stretches after a pass start, not a claim that a halt goes
  through the loop. The σ bound (log₂W ≤ σ + 6.38 at the first pass start) is still not in Lean: the L₁ classes of
  the closing R are (`endgame_stretch`), but it also needs the pass map (R′ = R/16, L₁′ = L₁/64) and a way across
  half passes.
* The **two-marker route tree** (`route_tree_clean`) is not used here.

## How to check

```sh
LEAN=/path/to/lean LEANLIB=/path/to/lib/lean ./check.sh       # the BB6 modules
LEAN=/path/to/lean LEANLIB=/path/to/lib/lean ./check_end.sh   # the theorem files, the direct runs, the 36-digit measures
LEAN=/path/to/lean LEANLIB=/path/to/lib/lean ./check_end.sh --deep   # also the 40-digit measures
# the tree's statistics, or the tree itself (optional, after check_end.sh; Γ = 2²⁰, 2³² or 2⁴¹):
LEAN_PATH=/path/to/lib/lean:out lean --load-dynlib=cbuild/so/libBB6all.so --run RouteStats.lean clean 4294967296 36 tree.txt
# the checkpoints of the run to 2²⁰ and the kernel-checked prefix from them (optional; the files are in the repository):
LEAN_PATH=/path/to/lib/lean:out lean --run PrefixGen.lean 1048576 5000 checkpoints.txt
python3 thm/gen_prefix.py checkpoints.txt thm 8
```

## Running time (Lean 4.34.0 release build, native code via `--load-dynlib`, 4 cores)

| step | time |
|---|---|
| `thm/PrefixPieces*.lean`, `thm/ExitPieces*.lean`, `thm/EndgamePieces*.lean` (kernel, 4 modules at a time; the prefix pieces take about 2 min of it) | 4 min 33 s |
| `thm/PrefixKernel.lean`, `EndgameTheorem.lean`, `ExitTheorem.lean`, `ExitHalt.lean`, `LoopTheorem.lean`, `LoopHalt.lean` | seconds |
| `thm/Prefix.lean` (1.2 × 10⁹ rounds) | 4 min 42 s |
| `thm/CleanTheorem.lean`, `thm/EndToEnd.lean`, `thm/EndToEndDirect.lean` | seconds |
| `thm/CleanMass.lean` (36 digits, 3.2 million leaves) | 4 min 57 s |
| `thm/CleanKernelMass.lean` (36 digits, cone 2²⁰) | 4 min 55 s |
| `thm/CleanDirect.lean` (the 36-digit tree, then 26,509,316 direct runs) | 11 min 36 s |
| `thm/CleanDirectMass.lean` (36 digits, cone 2⁴¹) | 4 min 53 s |
| `thm/CleanMass40.lean`, `thm/CleanDirectMass40.lean` (40 digits, `--deep`) | 27 min each |

The whole of `check_end.sh` took 21 min 37 s (4 cores; the files of a stage run in parallel); with `--deep` it took
34 min 56 s before the kernel's prefix and its tree were added.
