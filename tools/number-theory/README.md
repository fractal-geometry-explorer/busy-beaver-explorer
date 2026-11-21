# The number-theory bucket: which Collatz-like holdouts could be solved?

The Collatz-like triage put 40 holdouts in a "number theory" bucket. For each of them Lean already proves that the
machine halts iff an explicit map does something, so what is left is a question about the map. This folder ranks the
40 by how likely a proof is, from what the maps look like, and records what was tried (21 November 2026).

The ranking is a judgement, not a result. It is in [`ranking.json`](ranking.json) (rank, machine, class, tier,
reason, next step) and on the page
[`pages/holdouts/number-theory.html`](../../pages/holdouts/number-theory.html) (built by `build_page.py`).

## Tiers

| tier | meaning | machines |
|---|---|---|
| A | a route that needs no number theory may exist | 1 |
| B | an invariant of a simple kind (parity, residue) is plausible | 2 |
| C | Collatz-type, but a Lean step is still open that sharpens the question | 14 |
| D | Collatz-type, and known methods are shown not to work | 10 |
| E | Antihydra type, or not fully reduced yet | 5 |
| F | probably halts, but the halt is out of reach of any computation | 8 |

## Findings

**The best candidate is 1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC.** Its step map `(W, N) -> (W', N')` changes the
wall `W` only through `N mod 2`, and no halting condition is known. So the walls reachable when the parity is
chosen freely at every step contain the real ones, and a closed set of them without a halting step would prove
non-halting with no number theory. `wallstack.py` explores that set with the stack-of-counters model
(`holdouts/<machine>/py/stackmodel.py`):

- The model agrees with the Lean step map (`py/zonemap.py`) on all 558 steps of the free-parity wall graph to 300
  cells. That includes walls with a closed empty counter under other items, which the model did not claim
  (`wallstack.py compare 300`).
- Under free parities no count ever goes below zero (29,195 walls to 30,000 cells, `wallstack.py bfs 30000`). Every
  counter is at least 5 times the one below it, and counters below the top never pass 17.
- Along the real orbit the counters below the top stay at 10 or less for 300,000 steps (`wallstack.py orbit`).
- The only way a count goes negative is through an open counter whose top neighbour stays odd for a long run of
  odd steps. Each such step takes about half the lower count from the top, while both grow by 3/2, so the run has to
  be about as long as the top count itself. A run of length J needs the top count to agree with a fixed 2-adic number
  in J binary digits. Among the reachable walls no run gets past 10% of the length needed
  (`wallstack.py margin 3000`).

So the remaining step is a statement about 2-adic digits, not about the orbit of N. The stack rules for every
stack are now proved in Lean (`holdouts/<machine>/lean/Stack.lean`). The 2-adic statement is spelled out in that
machine's README ("What the 2-adic condition says"): no 2-adic number rho(V), over the stacks V that occur, may
have a run of zero digits from position p to about 2^p/6. The stacks V form an infinite family, so this is not a
finite check. It is in the same class as Antihydra, but heuristically far safer. This is a much better position
than the other 39, but it is still not a proof.

**Three machines iterate one function.** 1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE,
1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_---0RE (in the coordinate N = 2n + 2) and
1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_---0LE all iterate `f(n) = 3n - 10*2^k + 3k + 14` on `h_k < n < h_(k+1)`, with
`h_k = 5*2^k - k - 6`, and halt at `n = h_k`. Their starts are 4, 10 and 1, and the orbits share no value in their
first 20,000 terms (`samemap.py`). The tables were known to be one table started in different states; that the
reduced maps coincide is new. They remain three separate questions. Each folder now has `lean/Closed.lean`, which proves the closed form for every n by the kernel (`pstep_closed`/`pstep_halt`, `next_closed`/`next_halt`), so all three Lean reductions now read directly as "does the orbit of 4 (10, 1) under f land on some h_k".

**Subtract-and-multiply maps have no residue invariant.** `residues.py` replaces the counters by residues mod M and
the size comparisons by either branch. The halting class is reached for every M = 2^a 3^b up to 7,776 in all four
maps tried (1RB1LF_0RC1RD_1LA1LD_1LE0RA_---1LC_0LA1LA, 1RB1RE_1LC0RA_0RD1LB_---1RC_1LF1RE_0LB0LE,
1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD, 1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE).

**The all-ones family has no visible pattern.** For 1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_---0RE, the map from one
all-ones length to the next (2 -> 28 -> 492 -> 772 -> 2197 -> ...) shows no structure for lengths below 400. For it and for 1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_---0RE and
1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE, `lean/Fatal.lean` now proves the fatal all-ones lengths for every n
(kernel; before, `native_decide` for n < 10^5), as the fourth machine of the family already had. All four now
reduce to one question each: does an all-ones length ever land on an explicit list such as 20*2^k - 2k - 12?

## Files

- `ranking.json`: the 40 machines, ranked.
- `wallstack.py`: the free-parity wall search for 1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC.
- `samemap.py`: the shared function of the three threshold machines.
- `residues.py`: the residue screen.
- `build_page.py`: writes `pages/holdouts/number-theory.html` from `ranking.json`.
