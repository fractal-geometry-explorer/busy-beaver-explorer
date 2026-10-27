# Can integrality close the open clean-tape classes? (October 27)

The question (option 2 of the plan after PR #47): `../lean/END_TO_END.md` ("Deeper trees") found that the clean-tape
tree's cut classes at a fixed number of digits keep their number as the tree gets deeper (1,255,820 of the 1,255,963
classes cut at 36 digits are still cut at 40), because a class keeps 2-adic values of W/2 that no depth settles. An
actual width is a finite whole number. Is there an argument that uses this to close classes, the way the loop's lock
(L₁ ≡ 3 mod 7, never 0) closes the loop? The lab notes cited below are `../notes/LAB_NOTES.md`.

**Short answer: no class can be closed this way without settling a question of Collatz type.**

- Below every open class the tree keeps branching (section 1). A class does not hold one 2-adic value that no depth
  settles, which a countdown could exclude for integers as L₁ ≡ 3 (mod 7) excludes the loop's fixed point L₁ = 0; it
  holds a Cantor set of them. Of the 9,129 classes cut at 24 digits, 2 close by 36 digits, and every other one still
  has between 42 and 304 cut classes at 36 digits (`spine_24_12`, Lean, `native_decide`). Of the 1,706 cut at 20
  digits, all but one have between 238 and 1,593 at 36 (`spine_20_16`), and of the 46,101 cut at 28, all but 9 have
  between 5 and 77 (`spine_28_8`). None is a single path.
- Single two-marker segments branch too (section 2): the leftmost marker halves every round while the rest of the tape
  runs a two-marker chain of its own.
- So no lock can exist for a class (section 3): a never-zero countdown that every step divides by 2 would vanish at
  every one of the class's unsettled 2-adic values, of which there are infinitely many, and a polynomial with
  infinitely many zeros is 0. Residues modulo odd numbers, the other integer structure a 2-adic class cannot see, give
  nothing new: the only conserved one is the count of 1s mod 3, and the return pieces keep no linear form mod any odd
  prime below 400 except E mod 3.
- Nor can congruences keep the run from blank tape out of the classes: modulo 2^k it visits a class once per lap of
  3·2^k, and over the laps it sweeps the subclasses (section 4).
- What is left (section 5) is to follow each integer past the digits it has: the tree follows a width W faithfully for
  about log₂W digits and then can only run it directly. That every such run settles is a statement of the same kind as
  the Collatz conjecture's "every n > 1 eventually falls below itself".

## 1. Below every open class, the tree keeps branching

`SpineCount.lean` (theorems, `native_decide`) and `SpineStats.lean` (driver, histograms on all cores) follow
`cleanTreeGE 2⁴¹ d` (the clean-tape tree with loop entries over the widths ≥ 2⁴¹, the tree of `blank_halt_pass`) to
the nodes after b splits that need another split (the cut classes at b digits), and count the cut leaves of each one's
subtree with r more splits: its cut classes at b + r digits.

| cut at b digits | close by b + r | cut classes at b + r below each of the others | per digit |
|---|---|---|---|
| 1,706 (b = 20) | 1 | 238 to 1,593 (r = 16, `spine_20_16`) | 1.41 to 1.59 |
| 9,129 (b = 24) | 2 | 42 to 304 (r = 12, `spine_24_12`) | 1.37 to 1.61 |
| 46,101 (b = 28) | 9 | 5 to 77 (r = 8, `spine_28_8`) | 1.22 to 1.72 |
| 236,207 (b = 32) | 90 | 4 to at most 128 (r = 8, `spine_32_8.out`) | 1.19 to at most 1.83 |

Histograms of the counts (`spine_*.out`; the bins are 1, 2, 3, 4, then 5–8, 9–16, …):

| b → b + r | 0 | 4 | 5–8 | 9–16 | 17–32 | 33–64 | 65–128 | 129–256 | 257–512 | 513–1,024 | 1,025–2,048 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 20 → 36 | 1 | | | | | | | 28 | 356 | 1,090 | 231 |
| 24 → 36 | 2 | | | | | 610 | 3,538 | 4,834 | 145 | | |
| 28 → 36 | 9 | | 37 | 5,567 | 29,936 | 10,437 | 115 | | | | |
| 32 → 40 | 90 | 1 | 206 | 25,423 | 143,641 | 66,795 | 51 | | | | |

No class has 1, 2 or 3 cut classes below it: every class that does not close splits into at least 4 open subclasses
within 8 digits, and the subclasses keep growing at about the rate of the whole tree (1.52 per digit). The few classes
that close do so early (the 9 at 28 digits and the 90 at 32 within 4 digits, `ProjPar.lean`'s 46,092 and 236,117).
A class with a single unsettled 2-adic value, such as the fixed point of a loop, would show a count of 1 at every r.
The tree branches finitely, so a class whose count keeps growing holds infinitely many unsettled 2-adic values, and at
the rates measured a set of them of dimension about log₂ 1.5 ≈ 0.6 in the 2-adic integers.

This corrects the reading of "Deeper trees" in `../lean/END_TO_END.md` and `../HANDOFF.md`: an open class holds not one
2-adic value that no depth settles but a Cantor set of them, with about 1.5^r open subclasses r digits down.

What this means for an integer: if x is an unsettled 2-adic value in a class C, then for every k the widths
W ≡ x (mod 2^(k+1)) in C (there are such W above 2⁶¹ for every k) follow x's run for k digits and then go on into
whatever part of the Cantor set lies next to x. An integer differs from the other 2-adic numbers only in that its
digits are eventually 0, and the tree reads digits, not sizes, except at the edge of its cone, where a drop runs the
class's smallest member directly.

## 2. Single segments branch too

The two-marker reduction (lab notes, October 20) cuts a run into segments, from one two-marker state G 1, M m, M E − 2
to the next or to a clean tape. One could hope that the branching is all in the chains of segments and that each
segment has a lock. It is not. `RouteSpine.lean` makes the count of section 1 for the route tree with loop entries
(`routeTreeE 2²⁶ d`: one segment, m and E free, the next two-marker state counted as its end; `route_spine_*.out`):

| cut at b splits | close by b + r | 1 | 2 | 3 | 4 | 5–8 | 9–16 | 17–32 | 33–64 | 65–128 | 129–256 | 257–512 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 218 (b = 16, r = 8) | 87 | 2 | 1 | 5 | 3 | 12 | 46 | 42 | 20 | | | |
| 700 (b = 20, r = 12) | 239 | 2 | 6 | 10 | 11 | 28 | 37 | 39 | 138 | 134 | 55 | 1 |
| 2,427 (b = 24, r = 8) | 749 | 70 | 99 | 70 | 60 | 158 | 480 | 449 | 289 | 3 | | |
| 8,943 (b = 28, r = 8) | 3,043 | 258 | 286 | 315 | 374 | 645 | 1,520 | 1,536 | 957 | 9 | | |

About a third of a segment's cut classes close within 8 more digits (and not many more within 12); the rest branch. The
cut paths (`../lock/PathSamples.lean route 67108864 30`) show why. In almost all of them the leftmost marker halves
every round (in one sampled path it is at m/2^k in round k for k = 1 to 14; in another, after a wall, at (3/2^k)m +
(19/2^(k+1))E + 1469/2^(k+1) in round k + 4 for k = 7 to 15), and meanwhile the marks to its right go through G M M-like
rounds of their own, reading digits of E: the rest of the tape runs a two-marker chain, but with a third marker on the
left the tape is never a two-marker state, so the segment does not end. The clean-tape tree has the same paths (the
class W ≡ 2 mod 2³¹: the first marker at (W − 2)/2^k for 30 rounds while the rest passes eight two-marker states). For
an integer the halving stops within log₂ of the marker's position, a positive integer, but at a width of 2⁶¹ that allows
61 rounds, and the class holds positions with any number of trailing zeros.

## 3. Why no lock exists for a class

The locks found so far each bound one mechanism:

| mechanism | countdown | bound |
|---|---|---|
| the plain loop | L₁ ≡ 3 (mod 7), divided by 64 per pass | log₆₄(280E) passes |
| the extra-wall pass P, the detour Q, every periodic word in them | L₂, D_Q, the word's norm form | 2/3 to 4/5 of the halvings |
| each reset return piece (14,063 of them) | L = K(m − λE − μ), never 0, divided by 2^r per return | log₂(E)/r repeats |
| each pure-halving return piece (104) | m itself | log₄E repeats |
| a halving marker | its position | log₂ of the position |

None is shared: the reset pieces' fixed lines differ (λ = 6/7, 2/5, 1/7, …) and a change of piece renews the
countdown (`../lock/LOCK_NOTES.md`, sections 4 and 7). The branching of section 1 shows that no shared one can exist,
of any algebraic form:

> Suppose F is integer-valued on the states of a class C's runs, never 0 at a state reached from a width in C, and
> every step of a run that does not settle divides it by 2 or more. Along C's run every position is affine in W, so
> F at the class's starting state is P(W) for a function P, a polynomial if F is one. A width whose run makes k steps
> has 2^k | P(W); so P would bound the steps by deg P · log₂W + O(1), and C would close. But at an unsettled 2-adic
> value x of C the widths W ≡ x (mod 2^d) make more and more steps as d grows, so P(x) = 0 in the 2-adic integers.
> There are infinitely many such x (section 1) and a nonzero polynomial has finitely many roots, so P = 0, and then
> P(W) = 0 at the widths too, where F must not vanish.

The same holds for F given by finitely many polynomials on residue classes (every open subclass still holds infinitely
many unsettled values) and for any F that is continuous 2-adically: such an F must vanish on the Cantor set and nowhere
at a width, which is the statement to be proved. The loop's lock works because the loop's unsettled set is one point
per entry, L₁ = 0.

**Odd moduli.** A 2-adic class holds every residue modulo an odd number equally, so a quantity conserved modulo an
odd number is the one kind of integer structure the trees cannot see. The lab notes searched for them at the tape and
at the mark level ("They pass the machine's conserved count", October 24: weights on patterns of up to 7 cells,
positions modulo up to 8, head terms, moduli 2 to 63): the only one is the count of 1s plus state weight mod 3. It
makes every jump between clean tapes a multiple of 3 (every clean tape has n ≡ 2 mod 3) and gives E ≡ 3 (mod 6) at a
four-wall round start, and the closing classes, being 2-adic, do not conflict with it. For the two-marker chains,
`oddinv.py` (`oddinv.out`) asks for affine forms F = a·m + b·E + c that each of the eight largest return pieces
multiplies by a constant mod p: for every odd prime p below 400 there are none but constants and, for p = 3, E itself
(every return adds a multiple of 6 to E). For a general p the two largest resets alone decide it: a form with a ≠ 0
needs both pieces' fixed lines to agree mod p, and 6/7 ≡ 2/5 (mod p) means p | 16.

## 4. The run from blank tape does not avoid the classes

Modulo 2^k the run's clean tapes follow T(r) = r + J(r) wherever the class of r is settled (lab notes, "The trajectory
as a track"). Every jump is a multiple of 3, so the run comes back to a residue mod 2^k only after an advance that is a
multiple of 3·2^k, a lap; each class is visited once per lap or never (the 11-meeting class first visited at
n = 37,558,132,238 came back at exactly n + 3·2³⁵). While the track repeats, the visit in lap L is at
n₀ + 3·2^k·L, and since 3 is odd, the next digits of n₀ + 3·2^k·L run through every residue as L does: over the laps
the run's visits to a class sweep every one of its subclasses. Measured on 10⁸ cycles of the real run (October 20,
`trajmarkov.c`, `trajent.c`), the visit frequencies match the 2-adic Markov chain to a total variation of 0.004 mod
1,024, and deep classes are hit within a factor of about 3 of their measure. So no congruence at a finite depth keeps
the run out of the open classes.

## 5. What remains, stated exactly

The tree follows a width W through the digits it has. By the spare-digit bound (lab notes, "Residue classes of n":
j_min ≤ 1 in every class checked), a member of a class at depth d with at least one more binary digit above the
class's makes the class's choices, so W is followed faithfully to about log₂W digits; beyond that W is the smallest
member of its class, at the edge of the cone, and the tree can only run it directly (a drop). Below 2⁶¹ every width
settles (the exhaustive check). Above, the widths that the tree leaves undecided at their own length are about
2^K · 0.76^K = 1.52^K of the 2^K widths with K digits: still infinitely many, each a computation of its own. The
integrality question is whether every one of them settles.

For the Collatz map the residue class of n mod 2^k fixes the first k steps, the classes on which k steps do not yet
bring n below itself keep growing in number while their measure falls (Terras, 1976), an integer is followed by its
classes for about as many steps as it has digits, and the conjecture is that every n > 1 still falls below itself in
the end. The structure measured here (uniform branching inside every class, no shared countdown, no odd-modulus
invariant) is the same, and gives no handle that the Collatz problem lacks. The heuristic odds (lab notes, "Heuristic
odds of a halt above 2^45") are unaffected: about 10⁻²⁴ or less.

## What would still help

- Statements that use size and digits together, as the σ bound and the entry checks already do. A halt is a size event:
  some distance equals a fixed constant. On a class a distance is an affine form in the class's free numbers, and one
  that is not constant equals a constant only on a slice of the class, which 2-adic rounds never isolate (every residue
  class around the slice holds other values); so a tree can decide a halt only where the form is constant on the class
  or at the edge of the cone. The eight halting families of `open_halt_families` are such slices: each fixes R (at 178
  to 914) and moves the walls and the width by multiples of 2^k, so every distance its close needs is constant on it,
  while `passTreeSym`, whose classes leave R/2 free, leaves them open at every depth (only R = 178 is at the edge of its
  cone R ≥ 178). The entry checks use this (Cramer's rule on each candidate point), and the landing condition of
  option 1 applies it to the halting families.
- A density theorem (almost every clean tape settles) would follow from a uniform bound on the branching, for example
  that from every node at least a fixed share of the measure settles within a fixed number of digits. It would not
  decide the machine.

## Files

| file | what it does |
|---|---|
| `SpineCount.lean` | `spine_20_16`, `spine_24_12`, `spine_28_8`: the counts of section 1 as evaluated theorems (`native_decide`, about 3 to 4 minutes each) |
| `SpineStats.lean` | driver: the histograms of section 1 for any b and r, on all cores (`spine_*.out`) |
| `RouteSpine.lean` | driver: the same for the route tree with loop entries (section 2, `route_spine_*.out`) |
| `oddinv.py` | the common affine eigenforms of the eight largest return pieces mod odd primes (section 3, `oddinv.out`) |
| `check.sh` | checks `SpineCount.lean` (after `../lean/check.sh` and `../lean/check_end.sh`) |

Run the drivers from `../lean` after `check_end.sh`:
`lean --load-dynlib=cbuild/so/libBB6all.so --run ../integ/SpineStats.lean 24 12` and
`lean --load-dynlib=cbuild/so/libBB6all.so --run ../integ/RouteSpine.lean 67108864 24 8`.
