# lemcert: a generic lemma-certificate search (experimental, does not close anything yet)

This directory is an attempt to make the proof method of DeepMind's cryptids pull request 37
generic. That pull request proves that 1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA--- never halts.
The goal was to apply the method to the other "counter plus messy end" holdouts (families F04 and
R15).

**Status (26 November 2026): the search does not reproduce the PR 37 proof on its own machine,
so it has settled no machine.** It is kept here as a record of what was tried and why it stops
short.

## How PR 37's proof works (short)

- **The encoding.** The left tape is a list of digits d, each written `1 1^d 0`. The right tape
  is a list of digits z, each written `0^z 1`. There are about 25 one-shot macro rules and a
  few accelerated sweep lemmas.
- **The outer loop** runs from `A> ` at `E k = 0 0 1^k 0` (in digits) with any right tape. It
  comes back to `E k'` with k' = 2⌊2(k − 10 + c)/3⌋, where c ≥ 0 is supplied by the tail. Only
  "k ≥ 42" is carried, and a strong induction on fuel closes the loop.
- **The tail is handled once, for every tail.** Two lemma nodes, E(6, ANY) and S1(7, ANY), say
  what one excursion into an arbitrary right tape does. It either runs forever, or it returns
  with "a run of 2s, then a digit ≥ 5" and the left counter intact.
- **The certificate** has 578 nodes. Each node is a left context with capped digits (capD d = d
  for d < 9, else 6 + d mod 3) and a coarse right-tape class RT, together with its exit buckets.
  It is checked by `decide +kernel`.

## What the search here does

- `engine.py` is a symbolic simulator over run-length tapes. An item is (word, count), where the
  count is a linear form over naturals. It has shift rules and regrouping.
- `search.py` proves loop rules (induction from a generic pattern with adaptive minimum counts)
  and has the generalisation helpers. Abstract counts are `c + p·v`, a lower bound with a residue
  mod p, which plays the role of capD.
- `search2.py` is the summary search. A node keeps a few cells or runs on each side, with `S`
  standing for "the caller's tape".
  - Exits are found by a fixpoint over the call graph, and call sites are re-explored
    incrementally.
  - Options: two-sided frame lemmas, run-level context cuts, splitting the counter run at a call
    (like DeepMind's E(6) context), loop look-ahead through calls, and "tail loops" (a walk into
    the unknown tail is closed by generalising an ancestor).
- `verify.py` samples concrete instances of every node and checks that each observed exit is
  covered by a recorded exit. The last version has no unsound node.
- `run_ek.py` starts the search from `0^inf 01 (011)^k 0101 A> ANY`, which is E k in cells.
- `run_tail.py` is a later variant that takes its tail lemmas from rlepds (see "Tail summaries from
  rlepds" below).

## Why it does not close

1. **The counter's bound decays.** The proof needs the counter's exact linear value to survive a
   whole round, so that k' ≥ 42 can be checked. Each time a configuration that holds the counter
   becomes a new node, the counter is re-abstracted to a lower bound, and the bound drops
   (44 → 26 → 15 → …) until a spurious halt appears. Several of these leaks are fixed; others
   remain.
2. **The tail fact is lost.** In cells, DeepMind's exit fact is `(001)^c 0^{≥5} 1`. Here the
   zero-run's bound comes from the constant part of a symbolic count, often 2. The fact is then
   lost, and the search follows "era" branches (a `(01)^N` run growing ×4 per pass) that never
   return to E k.
3. **Size.** Without those two facts, the search grows to thousands of nodes and stops at the
   20,000-step cap per node or at the memory limit. PR 37 needs 578 nodes.

Fixing 1 and 2 comes down to DeepMind's hand-chosen digit-level domain: capped digits, a right
tape of one digit or one run of equal digits plus a coarse atom, and exits bucketed in that
domain. That domain is specific to the machine.

## Tail summaries from rlepds (26 November 2026, later the same day)

`run_tail.py` replaces the lemma search of `search2.py` by tail summaries computed by
`tools/c/rlepds.cpp`, and keeps this directory's engine for everything else. **It still settles no
machine**, but it removes failure 1 above, shrinks failure 3 and makes failure 2 exact.

- **A node** is a configuration whose head faces the bare unknown tail. Between two nodes every
  count is an exact linear form and sweeps are loop rules, so nothing decays inside a round.
- **The tail lemma** is one call: `rlepds MACHINE 2 1 9 9 3 3 3 1 enter=Qh lctx=CELLS`. CELLS are the
  literal cells left of the head (the left context). The answer lists every way the head can leave
  the context to the left, for every tail, as a state and the first two runs of the rewritten
  tail. A walk of any length into the tail is inside the call, because the left side above the
  context is the stack of rlepds's pushdown system. Each call takes a few milliseconds and has
  1 to 16 exits.
- **Lower bounds are exact** below a cap (400), so a node keeps the true minimum of its counter.
- `--check N` runs the real machine on N random tails for every summary used and tests that each
  way out is a listed exit: 12,800 excursions over the 64 summaries of the run below, none
  uncovered.

Result on 1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---, from `0^inf 01 (011)^k 0101 A> ANY`, k ≥ 42:

- The rounds are followed exactly. For example `(011)^(v+41)` becomes `(101)^(4w+59)` after one
  round and `(101)^(16w'+89)` after two, with 56 node shapes among 602 nodes (not thousands).
- The search stops after 602 nodes (6.5 minutes) at a spurious halt, and the reason is one chain
  of nodes: `0^inf 01 (011)^k 11010111 D> ANY` leads to the same shape with k − 1, for every k
  from 41 down to 1 (41 nodes).
  One abstract excursion takes one unit of the counter, and the next node forgets everything to
  the right of the head, so the same thing can happen again.
- On the real machine this step exists but does not repeat. From `01 (011)^k 10101 A>`, the tail
  `110` gives the same shape with k − 1 in 21 steps, and a 10-cell tail gives k − 2 in 146 steps.
  No tail of up to 22 cells gives k − 3 within 3,000 steps. What stops it is what the excursion
  itself wrote on the right, which is the part a two-run summary forgets. This is failure 2
  above (the lost fact `(001)^c 0^{≥5} 1`) in its smallest form.
- Summaries that remember more do not help yet. With 4 runs (`--sumk 4`) the junk left of the
  head grows (contexts of 20 and more cells) and the search was stopped after 25 minutes at 450
  nodes, still with new shapes. With one repeated digit
  (`rlepds ... 3 2 9 9 3 3 3 1 slack=1`) a single summary has 4,483 exits.

So what is missing is small and specific: an exit that carries `(001)^c` as one item, bucketed as
PR 37 does it (one run of equal digits, then one digit class), instead of rlepds's general runs.

```sh
g++ -O2 -std=c++17 -o rlepds ../../c/rlepds.cpp
python3 run_tail.py --rlepds ./rlepds --check 200 --nodes   # 6.5 minutes; ends at the spurious halt
python3 run_tail.py --rlepds ./rlepds --maxnodes 60 --nodes   # the first nodes with their parents
```

## Does the method transfer to F04?

The F04 machine closest to PR 37's is its sibling 1RB0LE_1LC0RD_0RA1LD_0LC1RA_1LF1LA_---1LA,
which has the same 4/3 round map. The argument does not transfer to it, because there the tail
works against the counter.
- The first tail run a grows by 4/3 while m ≢ 1 (mod 3), and the main counter pays:
  m' = (4m − a)/3.
- The machine halts when a reaches about 4m (see that machine's README, third pass).
- So "m ≥ K" alone is not inductive. Any proof has to show that about 2m rounds in a row with
  m ≢ 1 (mod 3) never happen, which is a Collatz-type question.

Most other F04 machines, and the R15 family ("Collatz-like maps and cryptids"), are described in
their folders as Collatz-like maps whose halting depends on residues. In those maps a tail
contribution that is never negative (c ≥ 0 in PR 37) is not available either.
