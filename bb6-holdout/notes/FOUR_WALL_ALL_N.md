# The 4-wall loop's halting family for every number of passes: where a proof gets stuck

October 29. This note asks whether the run from blank tape can be kept off the 4-wall loop's halting family by one
argument that covers every number of passes, ideally in Lean. It starts from the sketch at the end of the October 28
lab-notes entry ("The 4-wall loop's halting pass starts against the run's own").

**Verdict.** There is no proof here. The statement for every number of passes is as hard as the open question the
project already states (`integ/INTEGRALITY.md`, section 5). The 2-adic handle in the sketch can be made exact for
any one class of clean tapes, but on the clean tapes that matter it gives no bound. Two Lean results come out of the
attempt, both new:

- **The machine's conserved count, in Lean** (`lean/BB6/Count3.lean`, standard axioms only). The number of 1s plus
  the state's weight (A 0, B 2, C to F 1) never changes mod 3, and it is 0 on blank tape. So a three-wall round start
  with a pass start's parities, reached from blank tape, has **W ≡ 2 (mod 6)** (`blank_pass_mod6`), and a one-marker
  clean tape has **W ≡ 4 (mod 6)** (`blank_clean_mod6`). `blank_halt_open_big_count` and `never_halts_of_big_count`
  (`lean/thm/CountHalt.lean`) add both to the end-to-end statement. The trees decide 2-adic classes, and every such
  class holds every residue mod 3, so the trees could not state this.
- **A correction, with replacements** (`lean/thm/LoopFarCount.lean`). `loop4_far_66` and `loop5_far_66` have widths
  ≡ 4 and 0 (mod 6), so the run from blank tape reaches neither, whatever the first wall (`loopFar45_unreached`).
  They met every condition the theorems stated, but not this one. Members that do meet it exist on the same lanes and
  routes, and the kernel checks that they halt and are open at every depth: `loop4_far_66c` (width
  153,220,594,947,397,302,464, about 2^67.05) and `loop5_far_66c` (97,633,604,797,689,018,560, about 2^66.40). Both
  come from moving the proved member along the lattice of b's classes in `far_shape.md` (see the file's docstring).
  `loopFar2`, `loopFar3` and `loopFar66` already have W ≡ 2 (mod 6).

## 1. What has to be shown

The lanes are Q + 5·2^k − 4 = 2^j or 3·2^j, where Q = W − b + 2R + 22. For k = 3 and every k ≡ 2 or 3 (mod 4) they
carry halting classes. On the lane with k = 4n + 7 the walls make n passes of the 4-wall loop before the re-entry
(`routes/loop4/README.md` in the halting-classes project files). At lane value 2^j a route's halting pass starts are
the R in a class mod 2^(k+2) together with the b in one class mod about 2^(1.5j). Call the union over n, j and the
routes H. Ruling out the family means proving that the pass start `blank_halt_open_big_count` gives (the last pass
start of the loop's chain from the run's own entry) is never in H.

## 2. Conditions on the pass start cannot do it

Every condition the theorems put on that pass start leaves halting members in H, for 2 to 5 passes and above the
2⁶⁶ floor from three passes on: R ≥ 769, every gap ≥ 448, 15W ≤ 64(W − b), width above the floor, open in
`passTreeSym` at every depth, and now W ≡ 2 (mod 6) as well. These are `loop2_far_wide`, `loop3_far_wide`,
`loop3_far_66`, `loop4_far_66c` and `loop5_far_66c`, and PR #90 checks the pass counts. The October 28 entry shows
that the shapes of the run's own entries and full-pass landings do not separate them either. The far-shape search
expects members for every n ≥ 3 from some scale on (`far_shape.md`, "Why the counts stop"). So any proof has to use
where the pass start comes from: the run's own clean tapes.

## 3. Congruences cannot do it

The count mod 3 is the only conserved quantity of its kind. The searches found no other, with weights on patterns of
up to 7 cells, position classes mod up to 8, head terms, and moduli 2 to 63 and the rationals (lab notes, October 24;
`integ/INTEGRALITY.md`, "Odd moduli", which also covers affine forms on the return pieces mod every odd prime below
400). The run's clean tapes form a single cycle mod every 2^k through the residues ≡ 2 (mod 3). Their visit
frequencies match the 2-adic Markov chain (INTEGRALITY, section 4). So no condition mod 3 · 2^s on the clean tape is
left to use. A lane value is a size condition (Q equal to a given number), and the halting class is a 2-adic one. A
proof has to use both together, which is what the sketch tried.

## 4. The 2-adic handle, made exact, and why it stops

**Setting.** Take a class of clean tapes, n = c + 2^d t, that a finite tree takes to a loop entry with every round
decided. On it the entry's walls are affine in t. Fix the number p of full passes of the chain, which is a condition
on t's low digits, since R must be ≡ 0 (mod 16^p). On that subclass the chain's last pass start has
W, b, R, Q = affine functions of t with dyadic coefficients. Fix a route on lane k.

**What it gives.** The lane fixes t. The candidate is t_j = (2^j − 5·2^k + 4 − β)/α, where Q = αt + β, and it must be
an integer of the subclass. As j → ∞, t_j → t_∞ = (4 − 5·2^k − β)/α 2-adically, with |t_j − t_∞|₂ = 2^(−j)|α|₂⁻¹. So
p stabilizes (unless t_∞ is the loop's locked point L₁ = 0), and b(t_j) → b(t_∞). The halting class h_j (mod 2^(m_j),
m_j ≈ 1.5j) agrees with h_j′ in exactly j + 1 low bits on every route checked, so h_j → h_∞. A halt at lane value 2^j
needs b(t_j) ≡ h_j (mod 2^(m_j)). That forces v₂(b(t_∞) − h_∞) ≥ j − O(1). So **from one class, only the lane values
j ≤ J(C) = v₂(b(t_∞) − h_∞) + O(1) can halt, unless b(t_∞) = h_∞**. As k → ∞ (more passes), Q(t) ≡ 4 (mod 2^k) pins t
to a 2-adic neighbourhood of the point where Q = 4, so the same comparison runs at that point.

**What this would still need, even for one class.** Three things:

- The convergence of h_j, proved. It is untrusted now (the censuses at 2³⁹ to 2⁶⁶). The route forms have to be
  written as functions of the lane value 2^j, which they are affine in, so h_j is the solution of a congruence system
  whose coefficients are affine in 2^j.
- Every route at every R (the route-completeness thread's question). The censuses missed ζ, the route at R ≡ 1,702 and
  γ's paths until they were run at every R of a class.
- Every k, uniformly. That needs the forms for every number of passes, which PR #90 gives for n = 0 to 9 only.

**Why it does not close.** J(C) is a bound for one class, and the class's depth d sets the scale. A clean tape of K
binary digits is followed by the trees for about K digits (INTEGRALITY, section 5). A class settled to an entry at
depth d is useful only for lane values well above 2^d, where t_j is a 2-adic approximation and not just a small
integer. The clean tapes the trees cannot settle within their own length number about 1.52^K of the 2^K with K digits.
For them the class that reaches the entry has depth comparable to K, so J(C) ≈ d + O(1) is no restriction at the
lane values they could hit. Those are exactly the clean tapes the end-to-end statement already leaves open. So the
handle reduces the 4-wall family to the project's open question, and no further. The sketch says the same thing in
its last sentence ("what is left is the classes that the tree cuts at every depth"). The halting clean tape, if it
exists, is one of those classes: it halts, so no tree settles it.

## 5. What this leaves, and what would still help

- **One concrete computation, which would shrink the problem but not settle it.** Most of the run's clean tapes reach
  their entry within a few dozen rounds. In the blank-run data, 18,189 of the notable first entries are in round 26,
  and the 40-digit tree has 169,631 entries. For each entry class of the 36- to 44-digit trees, and each route found,
  the handle gives J(C). If every J(C) is below 66, the untrusted 64-digit check removes those classes. A halt through
  the family would then need a clean tape whose route to its entry is longer than the tree's depth. That is the same
  kind of residue as the clean-tape tree's cut classes, but narrower. The cost is the route forms as functions of 2^j
  for every route, and the 2-adic limits h_∞ for every k. With p and k unbounded this is again infinitely many cases,
  unless the forms are proved uniformly in n.
- **A uniform-in-n description of the family in Lean** (the forms of `four_wall_pass` iterated n times, with the
  invariant r³/Λ²). This belongs with the route-completeness work (PR #90). It is a prerequisite for anything that
  covers every number of passes.
- **The heuristic stands** (October 28 entry): the expected number of halts through the family above 2⁶⁶ is around
  2⁻¹⁰⁰, and no pass start of the run to 2⁴³ lies on any lane of the family. The count leaves this unchanged: all
  3,637,999 three-wall round starts in `below2p34` and `sample16k` of the blank-run data have W ≡ 2 (mod 6), as
  `blank_pass_mod6` says they must.
