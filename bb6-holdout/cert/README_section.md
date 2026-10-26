**Certificates and independent checkers (October 24; `../cert/`).** The exact end of the loop rested on two programs
(`endsym.py` on the stepper engine, `gx2 endgame` in C) agreeing. It now rests on something that can be audited
without trusting either: each explorer writes out its result as a *certificate*, a list of leaves, and a separate
program re-derives every leaf from the mark rules alone. The pieces:

- `endgame_leaves.txt` (40,991 leaves, every even R from 2 to 4096): the phase-0 pass starts G 1, W a, W b,
  W c = E − R − 1, M E − 2 (a odd, b even, E even), partitioned into 2-adic classes of (a, b, E), each leaf with its
  claimed outcome: `close` (an end meeting at distance d ≤ 2, the only configuration from which the machine can halt),
  `pass` (the rounds G W W W, G B W, G M B appear again), `break` (an end meeting at a non-constant distance that is not
  the continuation of the previous one), `notphase0` (the first two rounds are not G B W, G M B, so the start was not
  in the loop); and the round shapes along the way.
- `endgame_anyphase_leaves.txt` (83,699 leaves): the same from every G W W W start of that class, phase or no phase.
- `exit_leaves.txt` (358 leaves): the G W W W tape with a, b, c, E all free (the loop state in either phase), followed
  until a break, a clean tape, or a full loop cycle (`pass`).
- `check_endgame.py`, `check_exit.py`: the checkers. Each has its own implementation of the round recurrence (the
  table under "How the rules give the round recurrence") on symbolic positions, affine forms with exact rational
  coefficients. A digit test (d mod 2, d mod 4, the parity of a packet's target) is decided by the leaf's class, and the
  checker refuses if the class does not decide it. An order comparison (which mark comes first; do two marks overlap;
  is a meeting at distance at least 4, so that the swap and merge rules apply and the meeting is not a close) is decided
  by the signs of the gap coefficients alone, with no geometry, and the checker refuses if the signs are mixed. Every
  configuration the rules do not cover (a packet reaching a block, marks touching, a shift meeting a sleeping gap, …)
  is a refusal too. For each R the checker also verifies that the leaves are a partition of the start class: every
  lattice has index 8·2^bits, the measures sum to 1, and the cosets are pairwise disjoint (Hermite normal form). It
  then reads the closing table, the L₁ classes, the pass condition and the bound off the verified leaves.
- Results: all three certificates **valid**, with no failure, no undecided test and no uncovered configuration. The
  endgame checker reproduces the closing set {2, 4, 8, 16, 24, 32, 48, 64, 176}, the nine L₁ classes, the pass condition
  R ≡ 0 (mod 64), L₁ ≡ 1536 (mod 1792) and the bound 3 log₂R − 2 log₂|L₁|min ≤ 6.38; the any-phase checker the closing
  set {2, 4, 6, 8, 16, 22, 24, 32, 48, 64, 176}; the exit checker a longest chain of 8 end meetings, no close, and a
  full loop cycle on measure exactly 1/1024 (the 10 bits per pass).

*Where the cone rule is exact.* A sign decided from the gap coefficients is the true sign when the gap part outweighs
the constant: Σ gᵢtᵢ > |c|, which holds for every gap tᵢ > Γ with Γ = |c| / Σ|gᵢ|. The checkers record the largest Γ
over every decision they make (and over the decisions that involve each set of gaps):

| certificate | every decision exact once every gap exceeds | by the gaps a decision involves |
|---|---|---|
| endgame (phase 0) | 447 cells | a alone 1; a, b−a 447; a, b−a, c−b 8.0; c−b alone 10 |
| endgame (any phase) | ΓA cells | ANYPHASE_BY |
| exit (R free) | 447 cells | a alone 1; a, b−a 447; a, b−a, c−b 355; all four 22.1; c−b alone 10; c−b, R+1 10.7; R+1 alone 241 |

So the theorem under "The shape of what is proved" is certified in this form: *for every phase-0 pass start whose three
stripes a, b − a, c − b exceed 447 cells, and any R*: if R ≤ 4096 the endgame certificate applies with R exact; if
R ≥ 242 the exit certificate applies (its decisions that involve the end distance alone are exact from R + 1 > 241),
and it allows no close at all, at most 8 end meetings, and a continuation of the loop only on 1/1024 of the class. The
two overlap on 242 ≤ R ≤ 4096. The stripe hypothesis is exactly the "marks far apart" of the theorem, now with a
number; a pass start with a stripe shorter than 447 cells is a tape on which two marks are within a few hundred cells
of each other, which is family (c) of the three that remain (none occurs below 2^59, where the class tree logs the
least separation of every settled class; on the machine's own tapes it is one affine form in n and E landing in a window of width 447, a
coincidence of the same kind and rarity as the ones a halt needs).

*What the checkers trust.* The mark rules (each proved from the transition table in `proofs.py`, with the contact
conditions under which they hold); exact rational arithmetic; and nothing from the explorers except the leaf lists,
which they treat as claims. The one thing a reader has to accept beyond the rules is the 2-adic bookkeeping itself:
that a residue class of (a, b, E) on which every digit test is decided and every comparison has a fixed sign follows
one sequence of rules, so one symbolic run settles the whole class. That is the content of the checkers' loop.

*Found on the way.* The first version of the exit checker (and the C explorer in `exit` mode) never asked whether an
end meeting at a non-constant distance d = (R + k)/2^j could already be a close; both apply the swap or merge rule and
go on, which is right only for d ≥ 4. The checker now decides d ≥ 4 on the cone like every other comparison and
records its margin: that is where the exit certificate's threshold on R + 1 (241 cells) comes from, and it is exactly
what keeps the exit certificate from contradicting the closes at R = 64 and 176 that the endgame certificate finds.
Without that test the threshold read 49, which would have been a false proof that R = 176 cannot close.
