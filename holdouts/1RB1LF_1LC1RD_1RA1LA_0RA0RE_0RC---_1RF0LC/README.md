# 1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC

bbchallenge id 3292. One of the six-state holdouts whose halting from blank tape is open.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LF |
| B | 1LC | 1RD |
| C | 1RA | 1LA |
| D | 0RA | 0RE |
| E | 0RC | --- |
| F | 1RF | 0LC |

## What it does

Family: **Collatz-like (3n/2) with a tower of counters.**

Write `b` for the word `110`. The run is a sequence of *steps*; at the start of each the whole tape is

    W A> 0 b^N 1

a short *wall* `W` (a word ending in 1) on the left and one long block of `N` copies of `b`, blank on both sides.

* **Transfer.** The head builds a junction `111` and sweeps: `L 1 b^(x+2) 111 F> b^(y+1) 1` becomes
  `L 1 b^x 111 F> b^(y+4) 1` in 18y + 50 steps (the head runs to the right end and back, taking two copies of `b`
  from the left block and adding three to the right block). When the left block is used up the right block holds
  about `3N/2` copies and the next step starts. The tape grows on the right during the sweeps: the right side
  grows like sqrt(steps).
* **The wall.** The parity of `N` decides how the step ends; the next step is `W' A> 0 b^N' 1` with
  `N' = (3N + c)/2` and `(W', c)` depending only on `(W, N mod 2)`. The commonest cases:

| wall `W` | `N` even | `N` odd |
|---|---|---|
| `1` | `1`, 3N/2 + 7 | `1^4 b 1`, (3N+9)/2 |
| `1^(3j+1) b 1` (j odd) | `1^(3j+4)`, 3N/2 + 7 | `1 b^(j+1) 1^3 b 1`, (3N+9)/2 |
| `1^(3j+1)` (j even) | `1`, 3N/2 + 7 + j | `1^(3j+4) b 1`, (3N+9)/2 |
| `1 b^k 1^3 b 1` | `1 b^k 1^6`, 3N/2 + 7 | k even: `1 b^(3k/2+2) 1^3 b 1`; k odd: `1^4 b 1 b^((3k-1)/2) 1^3 b 1` |
| `1 b^k 1^6` | k even: `1`, 3N/2 + 3k/2 + 9; k odd: `1^4 b 1`, 3N/2 + (3k+13)/2 | k even: `1^4 b 1`; k odd: `1` |

  So alternating parities lengthen the wall `1^(3j+1)`, an odd step at the wrong moment turns the wall into a
  number `k` (the block `b^k`), and that number is itself multiplied by about 3/2 at later odd steps (with its own
  parity deciding whether a further level appears); two even steps in a row fold the wall back into `N`. The wall
  changes once per step and steps come exponentially further apart: the left side grows like log(steps).

From the run: `N` = 468, 709, 1068, 1609, 2418, 3634, 5462, 8200, 12307, 18465, 27702, ... with walls `1`, `1`,
`1^4 b 1`, `1^7`, `1^10 b 1`, `1^13`, `1`, `1`, `1`, `1^4 b 1`, `1 b^2 1^3 b 1`, ...

**Halting.** The only halting transition is E on 1, reached only through `A> 0 1 1 1` (A writes 1, B and D read the
next two 1s, E the third). No step of the map halts in any case seen:

* the orbit: 40,000 steps of the Lean step map from the step start at step 10,206 of the run (`N` then has 23,405
  bits, 83 walls occur, the map always answers), and 300,000 steps of the plain step map `py/stepmap.py` from
  `1 A> 0 b^468 1` (`N` then has about 175,000 bits; 117 walls occur, the wall `1` in 24% of the steps, the longest
  with three levels such as `1 b^2 1^3 b 1 b^10 1^3 b 1 b^1390 1^3 b 1`);
* the graph: breadth-first search of all walls of at most 300 cells reachable from `1` with either parity
  (279 walls, 558 steps, `py/zonemap.py graph 300`): no halt.

So unlike the Antihydra-type cryptids no halting condition on the map is known. Non-halting is not proved either:
the reachable walls are towers of 3/2-counters whose shapes have not been described in general.

**The step map, for every wall (Lean).** A step is not one transfer loop but three parts:

1. the head crosses the block (`0 C> (110)^k` becomes `(110)^k 0 C>`), builds a few short-lived junctions at the
   right end, and then the junction `L 1 b^x 111 F> b^(y+1) 1` with `x = N - const`;
2. the transfer loop (`sweeps`): `x mod 2` copies are left, the right block has `y + 3 floor(x/2) + 1`;
3. the end of the step works on the wall, crossing the right block a few times (`0110 A> (110)^k` becomes
   `(111)^k 0110 A>`; `(111)^k F> 1` becomes `F> 1 (110)^k`), and leaves `W' A> 0 b^N' 1`.

Parts 1 and 3 are computed by a small simulator (`lean/Zone.lean`, `py/zonemap.py`) that steps cell by cell near
the wall and near the right end, with some copies of `b` kept on each side as working room (about one wall length),
and jumps over the copies between by one of the three shift rules. It never looks at how many copies it jumps, and
gives the step map

    stepMap (W, N) = (W', N')   or halt   or stuck

(`stuck`: `N` too small for the working room (about two copies of `b` per wall cell), a meeting with the block that the rules do not cover, or out of
fuel; never seen along the orbit). Lean proves that the answer is what the machine does, for every wall
(`step_next`, `step_halt`), that blank tape reaches the step start `11101101111101 A> 0 b^48 1` in 10,206 steps
(`blank_to_start`), and the reduction (`halts_iff`): **if the map never answers `stuck` along the orbit from that
step start, the machine halts from blank tape iff the orbit reaches a halting step.** Unconditionally, a halting step
in the orbit gives a halt (`halts_of_orbit`) and an orbit that never ends gives a run that never halts
(`not_halts_of_orbit`).

## Status

Open; reduced to the orbit of the step map, and (22 November) to a statement about integers only: **if the integer
counter-stack recursion from `(K(2), 48)` never makes a count negative, or zero anywhere but directly on the pile,
the machine never halts** (`not_halts_of_model`, `lean/Model.lean`; see "Non-halting from integers alone" below).
Lean, all by the kernel:

* `lean/Blank.lean` (generated): the halting configurations (`step_none_iff`); no halt in 10,000 steps by the
  kernel, in 10,000,000 by `native_decide`.
* `lean/Rules.lean` (generated by `py/rules.py`): `sweep` (one sweep, any wall), `first` (from the wall `1`, the
  start of a step reaches the first junction, for all `n`).
* `lean/Sweeps.lean`: `one_sweep` and, by induction, `sweeps`: `t` sweeps take the junction `J (x + 2t) y` to
  `J x (y + 3t)` for every wall.
* `lean/Zone.lean` (generic in the machine): the simulator around one long repeated block and its soundness for
  every number of copies (`arun_sound`, `arun_halt`).
* `lean/Reduction.lean`: the three shift rules, `stepMap`, `step_next`, `step_halt`, `blank_to_start`, `orbit`,
  `halts_iff`, `halts_of_orbit`, `not_halts_of_orbit`; `first_steps`: the map answers for the first 40 steps of the
  orbit (kernel evaluation); `orbit_5`: after five steps the wall is `1` and `N = 468`.
* `lean/StackDefs.lean`, `lean/StackRules.lean` (generated by `py/stack.py`), `lean/Stack.lean`: the stack of
  counters for every stack, `stack_step` (see "The stack rules in Lean" below).
* `lean/Pile.lean`: closed empty counters stay in one pile at the bottom unless a count reaches 0
  (`mstep_good`, `good_iter`; see "Odd runs of a pair" below).
* `lean/Model.lean`: the cell-level rules cover the integer model on every good wall (`res_complete`,
  `stepRes_complete`), so non-halting follows from the integer orbit alone (`not_halts_of_model`); the first 50,000
  steps of that orbit satisfy the hypothesis (`model_first`, kernel evaluation); the bound "each counter at least 5
  times the one below" is not kept by the rules (`ratio5_not_enough`).
* `lean/Closed.lean`: every set of walls closed under both parities contains `1 K(0) K(9i + 7)` for every i
  (`family`, `closed_family`; see "A closed set of walls" below).

Computed: `py/zonemap.py` is the Lean step map in Python: `check 4000` compares it with the plain step map
(`py/stepmap.py`, one step simulated in C by `c/stepc.c`, three values of `N` per case) for 4,000 steps from
`(1, 468)`; `orbit` and `graph` as above. The plain step map agrees with the machine for the ten steps up to step
4.1·10^9 of the run, and ran 300,000 steps from `(1, 468)` without a halt. C (`tools/c/triage.c`): no halt in 10^9
steps.

## For later

* ~~Remove the hypothesis of `halts_iff`~~: done another way. `not_halts_of_model` goes through the stack rules
  instead of the zone simulator, and needs only the integer statement (no count fails).
* Describe the walls as a list of counters and prove the step map on that list (done in `lean/Stack.lean`
  except for an odd signal on `K'(0)` under other items); then either a halting wall appears
  in the description, or a closed language of walls without `A> 0 111` would prove non-halting. The zone simulator
  gives the exact map to test such a description against; the wall graph up to 300 cells has 279 walls.

## The wall as a stack of counters (observed)

Every wall met along the orbit is `1 X_1 ... X_n` with items `K(k) = b^k 1^3 b 1` (open counter) and
`K'(k) = b^k 1^6` (closed counter), the last item next to the block. `py/stackmodel.py` has a recursive rule for a
step: the parity of N goes into the wall; an open top counter closes (even) or becomes about 3k/2 and passes the
parity of k down (odd); a closed counter is dissolved into the block after passing a parity down, or gets a new open
counter on top (k = 0, odd). The rule gives the same (W', N') as `py/zonemap.py` (the step map proved in Lean) on
100,000 orbit steps (at most 7 items in a wall; N has 58,503 bits at the end) and on 2,563 random walls.
It was fitted by hand; it is now proved for every step where `stepRes` of `lean/Stack.lean` answers (see "The
stack rules in Lean" below). It has no halting rule; it does not cover a count going below zero, or an empty
closed counter under other items.

    python3 py/stackmodel.py orbit 100000
    python3 py/stackmodel.py random 1500

Tried without success (scratch tools, not in the repository): n-gram closed sets up to n = 30 and pushdown closures
with a DFA on one side; none gives a certificate. About 200,000 random and exhaustive small configurations of the
step-start and mid-step shapes do not halt.

## Free parities (21 November)

The step map changes the wall only through N mod 2, so the walls reachable when the parity is chosen freely at
every step contain the real ones. `tools/number-theory/wallstack.py` explores that set with `py/stackmodel.py`:

- The model agrees with the Lean step map on all 558 steps of the free-parity wall graph to 300 cells (`compare 300`).
  That includes walls with a closed empty counter under other items, which the model did not claim.
- Under free parities no count goes below zero: 29,195 walls to 30,000 cells (`bfs 30000`). Every counter is at least
  5 times the one below it, and counters below the top never pass 17. Along the real orbit (300,000 steps) the
  counters below the top stay at 10 or less (`orbit 300000`).
- A count can go negative only if an open counter stays odd for a long run of odd steps while the counter under it
  is open. Each such step takes about half the lower count from the upper one, while both grow by 3/2, so the run has
  to be about as long as the upper count. A run of length J needs the upper count to agree with a fixed 2-adic
  number (set by the stack below) in J binary digits. For the stack below that is empty at the start, that number
  has no run of more than 11 zero bits among its first 3,000 bits. Among the reachable walls no run gets past 10% of
  the length needed (`margin 3000`).

So a proof along these lines needs (1) an invariant that rules out those long odd runs, which is a statement about
2-adic digits and not about the orbit of N, and (2) the stack rules for every stack in Lean. This is still the most
promising of the 40 number-theory holdouts (`tools/number-theory/README.md`).

## The stack rules in Lean (21 November)

`lean/Stack.lean` proves the counter-stack step with symbolic counts, for walls of any height, by the kernel
(no `native_decide`). Items are listed top first (`It.o k` = `K(k)`, `It.c k` = `K'(k)`); `wt ws` is the wall as
a tape. Besides the step start `START W M c` (`W A> 0 b^M`, then `rhs c`) there are two places where a signal
arrives at a wall `W`:

* odd (N odd): the junction `CALL W 0 y c`, i.e. `W 111 F> b^(y+1)`;
* even: `QQ L n c`, the head in state F on the last cell of `W = L 1`, then `1 b^n`.

The context `c` is what follows the block: `1 0^inf` at the top, or `1 0 1 0 b^m` and then the context above,
when an open counter higher up has turned its block into a new block for the level below (`1 0 1 0` is the
marker; `b^m` is what is left of the block above, and every sweep under it uses up one copy of it).

`StackRules.lean` has one rule per case, each for any tape below the item and any context, with exact step
counts (found by the symbolic simulator `tools/py/bbtools/symtm.py`, proved by `rfl`, `cross_r`/`cross_l` and a
small normaliser for re-bracketed tapes). For example `o0`: `CALL (itT (.o (k+1)) W) 0 y c` reaches
`CALL W k 2 (.deep y c)` in 20 steps (an open counter on an odd signal: its block becomes the left block of a
transfer loop one level down); `reb`: `START W (n+1) (.deep (m+1) c)` reaches `START (itT (.o n) W) (m+1) c` in
`5n + 23` steps (the answer from below becomes the new count); `cq`: `QQ` on `K'(j+1)` reaches `CALL W j (n+1) c`
in 7 steps (a closed counter is dissolved into the block below and its parity goes down); `sweepD`: one sweep
under an item, in `18y + 56` steps; `part1`: `S W (n+5)` reaches the junction `CALL W n 12` for every wall.

`Stack.lean` puts them together by induction on the stack: `res ws s n` (the answer of the wall to a signal: new
wall, new count, copies used up above), `res_ok` (the machine does it, in every context), `stepRes` and
`step_stack` (`S W N` reaches `S W' N'` for the whole step), and `mstep`/`mstepN` (`step`/`stepN` of
`py/stackmodel.py`, transcribed) with `step_model`: **whenever `stepRes` answers, it is `stepN`**, so the fitted
model is proved on those steps (`stack_step` states both). `res` answers in every case except two: a count would
go below zero, or an odd signal reaches a closed empty counter `K'(0)` with something other than `1 K'(0)^a`
below it (the run of 1s then merges with the item below and the machine works on that item; no rule for it yet).
Along the orbit from step 10,206 of the run `stepRes` answers in all of 30,000 steps and gives the Lean step map
(`python3 py/stack.py orbit 30000`, 7 minutes; N has 17,555 bits at the end); on random walls it gives
`stackmodel.py` (`python3 py/stack.py random 3000`). Under free parities (breadth-first from `1` with
N = 10^12 + parity, `python3 py/stack.py graph 100000`: 100,001 walls, 199,928 steps) the only steps where it does
not answer are the 870 where `stackmodel.py` does not either (a count below zero); the uncovered `K'(0)` case
does not occur there.

Left for a non-halting proof along these lines: the odd signal on `K'(0)` under other items (or a proof that it
never comes), and an invariant ruling out counts below zero (see "Free parities").

## What the 2-adic condition says (21 November)

The free-parity search (above) and the Lean stack rules leave one gap: a proof that no count goes negative.
`tools/number-theory/wallstack.py need` and `runs` measure what a negative count would take.

- **Only a long odd run can do it.** A count goes negative only when two open counters are on top, the top one
  (count k, over a lower count kl) stays odd, and the step signal stays odd, for J steps in a row. J grows linearly
  in k: about 2.8 k/kl steps, so at least k/6 while the lower counters stay at 17 or below (the most seen under free
  parities). For example kl = 2 needs J = 9, 35 and 664 for k = 10, 50 and 1000.
- **That run is a 2-adic coincidence.** Under J odd signals the stack below evolves in a fixed way, and the top
  stays odd for J steps exactly when k agrees with a 2-adic number rho(V), fixed by the stack V below, in J binary
  digits. Once k > 60 or so, J > log2 k, so the agreement means k *equals* rho(V) mod 2^J. In other words, the
  digits of rho(V) from about log2 k up to about k/6 must all be 0. Computing B digits of rho(V) therefore rules
  out every top count below 2^B over V, except one count and the counts below about 6B, all checked directly. Counts at or
  above 2^B would need a run of at least 2^B/6 zero digits. For the empty V the longest zero run in the first
  3,000 digits is 11.
- **Why this is not finite.** Under free parities the stacks V that occur are infinite: piles of empty closed
  counters `C0^j` under the rest grow without bound, and each changes rho(V). So the statement left is "no rho(V)
  over a reachable V has a zero run from position p to about 2^p/6". Its digits come from another 3/2 map (the stack
  below, driven by odd signals). This is the same kind of statement as Antihydra's. Heuristically it is far safer: a
  top count k is dangerous with probability about 2^(-k/6), and the free-parity search already clears every wall up
  to 30,000 cells.
- **The real orbit** (`runs 300000`): the wall never has more than 7 items. Odd runs of N are geometric (75,357 of
  length 0, 37,138 of 1, 18,723 of 2, and so on), with the longest 15. The fewest odd steps in a row any wall on the
  orbit would need for a negative count is 9 (counters (2, open), (10, open) at step 1,275). Each time, the top
  counter turned even long before that.

So the holdout is solvable to the same degree as the other 3/2-map holdouts: the reduction is now proved in Lean,
and what is left is a 2-adic avoidance statement, with no known technique to prove it.

## Odd runs of a pair (22 November)

The 2-adic condition above involves a number rho(V) for every stack V that can lie under the top counter, and
those stacks are infinitely many. `py/pairs.py` and `lean/Pile.lean` show that they come in a much smaller family,
and compute the condition for it exactly. Here P_a is a pile of a closed empty counters K'(0), and Phi(V) is the
stack V after one odd signal (`step(V, 1)` of `py/stackmodel.py`).

- **The pile (Lean, `Pile.lean`).** Every K'(0) lies in one pile at the bottom, and K(0) occurs only directly on
  that pile. `mstep_good` proves that a step keeps this, unless the step itself makes a count 0 away from the pile,
  and `good_iter` extends it to any sequence of signals. So the case the Lean stack rules leave open (an odd
  signal on K'(0) with something other than `1 K'(0)^a` below it, `good_c0`) can only come after a count has
  reached 0. The two gaps of `Stack.lean` are one gap: a count going to 0 or below.
- **Every pair lies on one of the orbits Phi^m(P_a K(0)).** New items are only ever put directly on the pile (as
  K(0)). An open counter j stays open only while every signal it gets is odd, so if an open counter k sits
  directly on an open counter j, the stack from j down is Phi^m(P_a K(0)), where a is the pile height when j was
  made and m is the number of signals j has had since. Checked on every pair of open counters in the free-parity
  walls to 30,000 cells (`structure 30000`: all 2,242 pairs in the 29,195 walls lie on such an orbit, with a <= 3 and m <= 7, and no wall has a K'(0) above the pile).
- **The run of the top is one affine map.** While k is odd it passes odd signals down, and
  k' = (3k - 1)/2 + om(a, m), where om(a, s) is what Phi^s(P_a K(0)) answers to its next odd signal. The sequence
  om(a, ·) does not depend on k. So with theta_t the least start value for which the t-th value is still at least
  1, a start value k_0 reaches a count below 1 exactly when k_0 < max(theta_0, ..., theta_r), where r is its run
  length, and the start values with run length r form one residue class mod 2^(r+1) (the class of the 2-adic
  number rho(a, m) = 1 - sum_s (2/3)^(s+1) om(a, m + s)). That gives the exact set of bad start values below 2^B
  in O(B) operations, with no search over k_0 (checked against a direct search for a <= 2, m <= 7).
- **Pairs made over a pile never fail (computed).** When the pair is made (m = 0), the largest bad start value
  for pile heights a <= 4,000 and start values below 2^4000 is 37,609 (at a = 3,989; always far below 2^(a+2)), and no start value below 2^4000
  has a run longer than 4,064 steps (`creation 4000 4000`). A pair made over P_a starts with k_0 >= 2^(a+2): the
  counter directly over the pile grows by a factor of at least 9/4 for every K'(0) added under it (argued from the
  rules, not in Lean; the least values seen in the walls to 30,000 cells are 7, 79, 727 and 6,559 for a = 0, 1, 2, 3). So **every pair made with a top count below
  2^4000 stays clear of 0 for its whole run**, whatever the pile height. 
- **What is left: pairs that start later.** A pair can also start at m >= 1, when a closed counter between k and
  j is dissolved and k lands directly on j with a new count. For those the bad start values reach about
  0.24 m times the lower count j_m (`table 40 80 1000`: at most 19.0 j_m for a <= 40, m <= 80), because the
  run that a 2-adic coincidence needs is shorter when k/j is small. All pairs met in the free-parity walls to
  30,000 cells have their top count above the bad range of their (a, m). So a proof needs a lower bound on k/j_m
  at such a start that beats that range (an inequality, not a statement about digits), plus the tail: start values
  of 2^4000 or more, which would need rho(a, m) to have about 2^4000/3 zero digits in a row starting below digit
  4,000.

```sh
python3 py/pairs.py structure 30000        # 10 minutes
python3 py/pairs.py creation 4000 4000 3   # 10 minutes on 3 cores
python3 py/pairs.py table 40 80 1000
python3 py/pairs.py rho 0 3000
```

## Non-halting from integers alone (22 November)

`lean/Model.lean` closes the two gaps between the machine and the integer model `mstep` of `py/stackmodel.py`:

- **The rules cover the model** (`res_complete`). `res` of `Stack.lean` (the rules proved on the tape) answers on
  every good wall (`Pile.lean`: all K'(0) in one pile at the bottom, K(0) only directly on it) whenever `mstep`
  answers and the block it hands back is not empty. Its buffer conditions (`rebR`: the new count is at least 0 and
  fewer copies are used up than the block above has) are exactly the model's own checks one level up, so the rules
  never run out of room where the model does not. `stepRes_complete` is the whole step for `N >= 5`.
- **Non-halting** (`not_halts_of_model`). `morbit` iterates `mstepN` from `(K(2), 48)`, the step start
  `11101101111101 A> 0 b^48 1` that blank tape reaches in 10,206 steps. If every `morbit i` exists, has `N >= 5`
  and is `okO` (no K(0) off the pile), then the machine does not halt from blank tape. This replaces the
  hypothesis of `halts_iff` (the zone simulator never stuck): no tape, no simulator, just a recursion on a list of
  integers.
- **Checked.** The kernel checks the hypothesis for the first 50,000 steps (`model_first`, 40 seconds; N then has
  29,255 bits). `python3 py/modelorbit.py 3000000` runs the same recursion for 3,000,000 steps (30 minutes; N has
  1,754,894 bits, at most 10 items in the wall): the hypothesis holds throughout. Each step takes more than N
  machine steps (`part1`), so this run means no halt in the first 10^528,274 steps.

**The 5x bound.** Along those 3,000,000 steps every open counter is at least 5 times the open counter under it
(the least ratio, exactly 5, is the pair K(2) K(10)), as in the free-parity walls. If that held forever no count
could fail. But it is not an inductive invariant, and not a sufficient local condition either:

- Along an odd run of the top counter k over an open counter j, both grow by 3/2 but k pays about j/2 per step,
  so k/j falls by about 1/3 per step; every bound of the form k >= c j breaks after about 3c steps of such a run.
- `ratio5_not_enough` (kernel): the wall `1 K(0) K(114520) K(596629)` satisfies the bound, falls below it after one
  odd signal, and 16 odd signals in a row make a count negative. (`K(0) K(114520)` is the lower stack after 26 odd
  signals; for 657 of the 880 orbit positions (a <= 10, m <= 80) of `py/pairs.py` there is such a failing start
  value of at least 5 j_m.)

So the statement left for a proof is not the 5x bound but the one of "What the 2-adic condition says": for every
pair that occurs, the top count is not in the sparse residue classes that fail. With `not_halts_of_model` that
statement, about integers only, is now exactly what non-halting needs.

## A closed set of walls (24 November)

The wall changes only through the parity of N, so a set of walls that contains `1`, is closed under `mstep` for
**both** parities and never lets a count fail would prove non-halting with no information about N. The natural
candidate, "every counter at least 5 times the one below", is not closed (`ratio5_not_enough`). `lean/Closed.lean`
shows why no set of that kind can work:

- **The family (kernel).** From the wall `1`, the parities `1 (01)^n` build `1 K'(0)^n K(0)` (`mrun_pile`); an odd
  parity dissolves the pile into the count, `1 K(2n + 2)` (`odd_on_pile`); on a single counter an odd parity makes
  `K(4i + 2)` into `K(6i + 5)` (`single_even`) and that into `K(0) K(9i + 7)` (`single_odd`). So
  `1 (01)^(2i) 1 1 1` leads to `1 K(0) K(9i + 7)` for every i (`family`), and every set of walls that contains `1`
  and is closed under both parities contains all of them and every wall of the odd runs from them
  (`closed_family`).
- **Their safety is a digit statement.** Over `K(0)` (pile height 0, m = 0 in "Odd runs of a pair") the top count k
  stays odd for t steps exactly when k agrees with the 2-adic number rho(0, 0) in t binary digits, and the bound
  theta_t of `py/pairs.py` grows like t, so a run fails only after about k steps. Below 2^3000 the only start value
  that fails is k = 1, which is not in the family (`closed.py bad 3000`). A larger k fails only if rho(0, 0) has a
  run of about k zero digits starting near digit log2 k (the first 3,000 digits have no run longer than 12). So a
  closed set of walls, whatever its form, proves that rho(0, 0) has no such runs: the same kind of statement as
  the rest of "What the 2-adic condition says". Inequalities between neighbouring counts cannot express it,
  because they cannot see residues modulo powers of 2; in particular no bound of the form "each counter at least c
  times the one below" can give a proof by itself.
- **Not only this family.** Under free parities, every lower stack met so far carries a whole arithmetic
  progression of top counts (`closed.py families 400 600`: 26 lower stacks with at least 8 top counts each, such as
  `K(23)` with tops 4,479 + 9n and `K(0) K(31)` with tops 4,749 + 243n), and no member of any of these progressions
  is a bad start value below 2^600.

This holds for closed sets inside the counter-stack model. When a count fails the machine leaves the model's walls
(in the cases seen it went on without halting), so a failure in the model is not by itself a halt; a closed set
that also contains the walls after a failure would have to describe those walls too. The closed-set route
therefore does not avoid number theory; it moves the question into the digits of 2-adic numbers like rho(0, 0).

```sh
python3 py/closed.py family 2000
python3 py/closed.py bad 3000
python3 py/closed.py families 400 600
```

## Regular invariants tried (21 November)

The machine halts only through A0 → B1 → D1 → E1, so a halt needs the head in state A on a 0 with 111 to its right.
In cell-level runs from random stacks (300 walls of up to 4 items, counts up to 12) the cells after A on 0 are
always 1101, 1011, 1100, 1010, 1000, 0000 or 1001, never 111.  From arbitrary-count stacks under free parities no
halt was met either (3,790 walls for 3 items with counts up to 5; 2,437 for 2 items up to 16).  But no regular
certificate was found:

* the window CTL of `tools/py/bbtools/ctl.py` (K = 3 to 9) finds no closed set without a halt;
* a SAT search for two automata (each side read from its far end) and a closed set without a halt is UNSAT with
  8 + 8, 6 + 14 and 14 + 6 states;
* a pushdown check (one side kept exactly, post* saturation) with the other side abstracted by windows of up to 25
  cells, or by an automaton built from the observed right-hand shapes, reaches a halt.

So the remaining step is still the invariant on counts (no count goes negative), not a finite-state one.

## Remainder classes (family survey)

- **Rounds between end events, by remainder class** (trusted). Sample the run whenever the head is in state B reading 1 with only 0s to its right. Read leftwards from the head, the tape is then `A U^m B`: one long periodic block between two short context words. For each class (A, U, B, m modulo 1 or 2 (the smallest modulus that works for the context)) the next sample is simulated for six values of m and extended as an affine map of m (with a cubic step count). Along the direct run from blank tape to 3·10^9 steps (39 events) the class map predicts the next event in all 26 rounds it applies to. This is an extrapolation checked by computation, not a proof. Command: `python3 holdouts/1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---/py/ctxround.py 1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC R B 1 check 3e9`
- **273,141 rounds of the class map without a halt** (heuristic). Iterated with exact integers from the event at step 29,839 of the run (A = `(empty)`, U = `110`, m = 79, B = `1^8 0110 1^3`): 273,141 rounds without meeting a halting class; m then has 79,895 bits (about 10^48,102 steps of the machine). 226 distinct contexts occur, the longest of 4,246 cells. The iteration stops there, at a context too large for the six simulations (a second long block has formed); this is a limit of the tool, not an event of the machine. Command: `python3 holdouts/1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---/py/ctxround.py 1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC R B 1 orbit 273141`
- **No halting class among 530 contexts** (heuristic). Breadth first from the starting context, with every remainder at every context (whether or not the numbers can really produce that sequence of remainders, and only for m large compared with the contexts): 530 contexts expanded, 530 found, to depth 186. None of them halts; the search is not complete (the set of contexts keeps growing), and it says nothing about a halt that needs a context as long as the block itself. 36 contexts longer than 300 cells were not expanded. Command: `python3 holdouts/1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---/py/ctxround.py 1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC R B 1 bfs 530`

## Pages

- [`pages/holdouts/1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC/explainer.html`](../../pages/holdouts/1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC/explainer.html)
- [`pages/holdouts/1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC/proof-status.html`](../../pages/holdouts/1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC/lean/check.sh   # about 2.5 minutes
python3 holdouts/1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC/py/zonemap.py check 1500
python3 holdouts/1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC/py/zonemap.py orbit 20000   # 1 minute; 40000 takes 15
python3 holdouts/1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC/py/zonemap.py graph 80
python3 holdouts/1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC/py/stack.py random 3000
python3 holdouts/1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC/py/pairs.py creation 500 1000 2
python3 holdouts/1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC/py/modelorbit.py 100000   # 20 seconds
python3 holdouts/1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC/py/closed.py family 2000
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB1LE_1LC1RC_1LA1RD_1LD0RB_0LC0LF_0LB---`](../1RB1LE_1LC1RC_1LA1RD_1LD0RB_0LC0LF_0LB---/README.md): rename A→C, B→A, C→B, D→E, E→F, F→D and exchange left and right; it is this table started in state B, in a mirror
- [`1RB1LB_1RC1LD_1LA1RE_1RD0LA_0RB0RF_0RA---`](../1RB1LB_1RC1LD_1LA1RE_1RD0LA_0RB0RF_0RA---/README.md): rename A→B, B→C, C→A, D→E, E→F, F→D; it is this table started in state C

<!-- end of related machines -->
