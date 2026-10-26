*The route tree, certified the same way* (`../cert/check_tree.py`, `tree36_leaves.txt`; the explorer `../csearch/rtree3e.c`
is `rtree3d.c` with a leaf printer). The route tree over two-marker states is the computation behind the ceilings, and
it can be audited the same way as the endgame. With `LEAFPRINT=1` the explorer writes every leaf of the tree: the kind
of ending (the next clean tape, or a cut at the depth limit), the list of meeting outcomes along the way (d mod 4 at
every meeting of the gap with a marker, in order) and the round shapes. Nothing else is needed: the checker replays
each leaf from the start state G 1, M m, M E − 2 (m even, E odd, all valid two-marker states) with its own
implementation of the rules on affine forms in (m, E). At each meeting it decides d mod 4 from the current class if it
can, and then the recorded outcome must agree; if the class does not decide it, the recorded outcome is imposed and
counted as a split. Comparisons of positions are decided on the cone of large gaps (m and E − m) — the explorer
decides them at an asymptotic ratio, so this is a stronger rule, and it never had to refuse — and every configuration
outside the rules is a refusal. The split sequences of all leaves must then form a complete prefix code (no sequence
a prefix of another, measures 2^−depth summing to 1), which is the partition of the start class; the recorded cosets
are not used at all. Along each path the checker also notes every phase-0 pass start (the rounds G W W W, G B W,
G M B) with its own forms of b, c and E, and recomputes the σ ceiling, so the tree's summary (entry measure by
ceiling, largest ceiling, undecided measure) is reproduced from the leaves alone.

Result at 36 binary digits: TREE36_RESULT

Why the exactness threshold is large here: a leaf whose run makes j end meetings has a meeting at distance
(t + k)/2^j, and deciding that this is at least 4 needs t ≳ 2^(j+2). So the threshold grows with the depth of the
run, as it must: it is the statement that the gaps are wide enough for j halvings to happen at all. On the machine's
own tapes beyond 2^59 every gap is of order 2^58, far above the thresholds of any route in the tree.

The 46-, 62- and 64-digit trees are the same explorer run deeper (`rtree3d.c`, which differs from `rtree3e.c` only
by the printer); they are not certified leaf by leaf, since the leaf count grows about 1.43-fold per digit (946,207
at 36 digits, about 4 million at 40, of order 10^9 at 62).
