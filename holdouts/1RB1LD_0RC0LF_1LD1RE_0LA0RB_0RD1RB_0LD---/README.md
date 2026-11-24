# 1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD---

bbchallenge id 173741. One of the six-state holdouts whose halting from blank tape is open. Family: Carry system: binary counters in 4-cell digits (left) and 3-cell digits (right), halting on the pattern >0111.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LD |
| B | 0RC | 0LF |
| C | 1LD | 1RE |
| D | 0LA | 0RB |
| E | 0RD | 1RB |
| F | 0LD | --- |

**Verdict.** **The question is open.** No halt in the first 10^10 steps (C simulator). The whole machine is a carry system of eight local rules on the tape, each proved in Lean (round 6, below). It halts exactly when state B comes to stand in front of `0 1 1 1`, and the only rule that can bring it there (R1) was used 424 times in the first 10^10 steps, each time in front of a 0. The right half as a whole has not been turned into numbers, so the question has not become arithmetic.

## What it does

The head shuttles around the start cell. Each round trip goes once left and once right.

- **Left half: a binary counter of round trips.** From the left end: an optional `10`, then 4-cell digits `1010` (one)
  and `1000` (zero), least significant next to the centre, then a `1`. Each visit adds one
  (`L 1000 (1010)^n 1 D>0 R -> L 1010 1 (0001)^n E>0 R`, proved for all n). An all-ones counter overflows in two
  half-steps (with and without the prefix `10`), so the left end grows exactly when the number of round trips T is
  2^k or 3·2^(k-1). Checked for all 8,388,630 visits in 10^9 steps.
- **Right half: a chain of counter segments.** Binary counters with 3-cell digits (`100`/`010`/`001` for one, `000` for
  zero, the phase depending on the segment), separated by markers like `101`; the lowest one changes every round trip and
  carries into the next. At each growth of the left counter the lowest segments are re-laid (one gains a digit and
  changes phase). The right end grows at irregular T (974, 1277, 1405, 1903, ..., 14,168,192).
- **Halting** needs F reading a 1 (`0 1 F>1 1`), and F does not occur in the left counter's moves, so a halt would have to happen right of the left counter.

<!-- F02-visit-law:begin -->
## The visit law, and where the run leaves the PR59 machines (F02, 13 November 2026)

**Proved in Lean (kernel), `lean/Visit.lean`.** A *visit*: the head enters a stream `s` (all cells from some cell on)
in state C with a 0 on its left, and comes back in state A two cells further left, the 0 restored and `s` rewritten
to `v(s)`. `Vis s s'` says exactly that, for every tape to the left. The rules, for every stream `s`:

| stream | after the visit | theorem |
|---|---|---|
| `0 s` | `1 s` | `vis_0` |
| `100 s` | `000 v(s)` | `vis_100` |
| `110 s` | `000 v(s)` | `vis_110` |
| `1010 s` | `1010 v(v(s))` | `vis_1010` |
| `1011 s` | `1000 s` | `vis_1011` |
| `111 s` | the machine halts | `vis_111_halts` |

`111 s` halts the machine (`vis_111_halts`). The six prefixes 0, 100, 110, 111, 1010, 1011 cover every stream, so the
rules are the whole machine: it halts from blank tape only if some visit meets `111` (each rule is a theorem; this
"only if" is read off the case list and is not itself stated in Lean).

The run is a sequence of rounds (`start`, `round`, `round_halts`): after 4 steps the tape is `0^inf A> 1 0 S_1` with
`S_1 = 1 0^inf`, and a round turns `0^inf A> 1 0 S` into `0^inf A> 1 0 S'` with `S' = v(1 0 S)`. If a nested visit
halts, so does the visit around it (`vis_100_halts_1`, `vis_110_halts_1`, `vis_1010_halts_1`, `vis_1010_halts_2`).

**The same first four rules as the machines of busycoq PR59.** `1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RC---` and its two
relatives obey `0 s -> 1 s`, `100 s -> 000 v(s)`, `110 s -> 000 v(s)`, `1010 s -> 1010 v(v(s))` too, with the same
rounds; they halt on `1011` (on `111` the three differ). PR59 proves in Rocq that they halt: rounds 1 to 161,210 use
only those four rules and round 161,211 meets `1011`. This machine differs only in what it does on `1011` and `111`.

**Computed (not proved): this machine does not halt there.** `c/vis.c` in
`../1RB0LB_0RC0LD_1LD1RE_0LA0RF_1RB0RD_0RB---/` runs the visit law with counts (2^j visits cross the word
in round 2j; counts are kept as 2^e - c). It learns every rule from the machine's own table, by direct simulation of a
visit, and falls back to direct simulation for anything without a rule. Checks: against a direct run of the machine
(every top-level visit of the first 3·10^7 steps, `py/vis_check.py`), against the same algorithm with exact integers
(`py/vis.py`, 1,500 rounds, same tape), and on the PR59 reference machine it halts in round 161,211 on `1011`, as PR59
proves. Result: rounds 1 to 161,210 use the four shared rules only; round 161,211 meets `1011` at the right end of
the word, rewrites it to `1000` and the run goes on. Observed: no halt and no visit to `111` up to round 200,000
(the run is still going; each further 100,000 rounds costs more than the last, the cost grows with the square).

A guess at how `1011` arises (not checked against the run): a count that dies exactly on a block leaves a stale
`110`; a later round whose blocks are aligned two cells earlier reads `0011`, writes `1011`, and comes again. Aligned
one cell earlier it would read `011` and then `111`. Nothing we know excludes a halt of this kind, and nothing proves one.

Tools (all in `../1RB0LB_0RC0LD_1LD1RE_0LA0RF_1RB0RD_0RB---/`): `py/visit.py MACHINE NAMESPACE OUT` writes
`lean/Visit.lean` by symbolic execution; `c/vis.c` (`gcc -O2 -o vis c/vis.c; ulimit -s unlimited; ./vis MACHINE [TOPVISITS [DUMP]]`,
two top-level visits per round for machines whose A1 is 0LB, one for A1 = 1LD); `py/vis.py`, `py/vis_check.py`.
<!-- F02-visit-law:end -->

<!-- visp-run:begin -->
## The visit law to round 4,000,000 (22 to 23 November 2026)

**Computed (not proved): no halt in the first 4,000,000 rounds.** `c/visp.c` runs the visit law about 15 times
faster than `vis.c`: round 200,000 in 3 minutes on 4 cores, round 1,000,000 in 80 minutes, and round 4,000,000 in
about 17 hours from a checkpoint at round 1,799,999. Through round 4,000,000 no visit meets `111`. A visit meets `1011`
(and writes `1000`) only 20 times, each time a few cells from the right end of the word. The positions below are in
the simulator's cell numbering:

| round | cell |
|---|---|
| 161,211 | (the round where the PR59 machines halt) |
| 194,647 | 819,721 |
| 757,566 | 3,191,503 |
| 906,776 | 3,820,394 |
| 1,042,307 | 4,391,628 |
| 1,731,289 | 7,295,578 |
| 1,768,131 | 7,450,689 |
| ... | three more between rounds 1,768,131 and 1,799,999 (log lost at a container restart; the count is in the checkpoint) |
| 1,975,597 | 8,325,010 |
| 2,717,690 | 11,452,858 |
| 2,783,756 | 11,731,381 |
| 3,281,058 | 13,826,689 |
| 3,287,695 | 13,854,540 |
| 3,424,111 | 14,429,576 |
| 3,538,057 | 14,909,797 |
| 3,621,507 | 15,261,604 |
| 3,701,314 | 15,598,059 |
| 3,988,383 | 16,807,815 |

The events come at irregular rounds, roughly a few per million, and the number of rounds between them does not grow.
At round 4,000,000 the word runs from cell -8,000,000 to 16,856,787. Every round sends a count of about 2^(r/2)
visits along the whole word, so one round costs time proportional to the length of the word, and the whole run grows
with the square of the number of rounds.

**What the count does.** The prefix `(10)^a` (a = r plus a constant) sends 2^(a/2) visits to the word behind it,
alternately at two entry points two cells apart. Those lead into two parse chains through the same cells, one used by
odd rounds and one by even rounds; at round 4,000 they have no position in common. Along each chain the count is
2^e - c with c small (mostly 1 to 10) and e falling by about one every 9 cells. So a round is a small
finite-state pass over the whole word, and it rewrites about a quarter of the word's cells. The rare `1011` events happen at
the right end, where e has run out and the count is small.

**How `visp.c` is faster, and why it is still exact.**
1. Several rounds at once. A round's cascade only moves right: its outermost position never decreases and it
   touches nothing left of it. Round r+1 works only on cells left of round r's outermost position, with a margin,
   so the tape is cell for cell the tape of the sequential program.
2. The prefix in one jump. n visits of `(1010)^j s` are n·2^j visits of `s`, with the blocks written back unchanged.
   This is proved in Lean: `visN_rep1010` in `lean/VisitPow.lean` (kernel only).
3. A short lead-in followed by a cycle (e.g. `010 -> 110 -> 000 -> 100 -> 000 ...`) is compressed in one step when all
   its nested visits go to the same cell.
4. Checkpoints (`CKPT`, `CKPTEVERY`, `RESUME`) taken with no round in flight. A resumed run equals an uninterrupted
   one (dump compared at round 20,000 after resuming at round 6,999).

**Checks.** Dumps of the whole tape equal those of `vis.c` at rounds 5,000 and 20,000 (1 and 3 threads). On
`1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RC---` (busycoq PR59), `visp.c` and `vis.c` both halt in top visit 322,423
(round 161,211), at cell 678,829, with the same 81-cell window.

```sh
gcc -O2 -o visp holdouts/1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD---/c/visp.c -lpthread
./visp 1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD--- 1000001 - 3 50000     # 80 minutes on 4 cores; prints E1011 lines
CKPT=ck.bin CKPTEVERY=50000 ./visp 1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD--- 4000001 - 3 50000   # about a day
./visp 1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RC--- 400000 - 3            # PR59 machine: HALT during top visit 322423
```
<!-- visp-run:end -->

<!-- right-end:begin -->
## 1011 and 111 only at the right end (proved, 22 November 2026)

**Proved in Lean (`lean/Cascade.lean`, no `native_decide`): halting is a right-end question.** In every round a
visit can meet `1011` or `111` only from two cells before the place where the previous round's visits stopped.
So the machine halts from blank tape exactly when, in some round, the last few cells of the cascade meet `111`.

*The cascade.* A round is one visit to the stream `X = 1 0 S`. Its nested visits run in single file from left to
right: the block at offset 0 takes its visits and passes the ones it owes on to the block behind it, which passes its
own on, and so on, until a block receives visits and passes none on. That block is the round's **stop**. With `n`
visits (n ≥ 1) a block does (`Blk`, closed forms proved by induction from the rules of `lean/Visit.lean`):

| block | n visits leave | visits passed on |
|---|---|---|
| `000` | `100` if n odd, `000` if n even | ⌊n/2⌋ |
| `100` | `000` if n odd, `100` if n even | ⌈n/2⌉ |
| `110` | `000` if n odd, `100` if n even | ⌈n/2⌉ |
| `010` | `110` if n = 1; else as `110` after one visit | 0 if n = 1, else ⌈(n−1)/2⌉ |
| `1010` | `1010` | 2n |
| `0010` | `1010` | 2(n−1) |
| `1011`, `0011`, `011`, `111` | handled one visit at a time (`Casc.e`, `Casc.d`, `Casc.u1`, `CascH`) | |

*The invariant.* Every block that passes visits on is left as `000`, `100` or `1010` (`Blk.out`): no two adjacent
1s, last cell 0. Only the stop block can be left with adjacent 1s (`010` hit once becomes `110`; after a dirty stop
also `1011` or `111`). So after every round the stream has no two adjacent 1s left of the stop (`Casc.clean`,
`reach_clean`). A visit meets `1011` (or `0011`, which becomes `1011`) only on the 1s at its offsets 2 and 3, and
`111` (or `011` hit twice) on the 1s at offsets 0, 1 or 1, 2. Hence:

- `right_end_1011`: in round r+1, every visit that meets `1011` does so at an offset p with F ≤ p + 2, where F is
  the offset (in `1 0 S`) of round r's stop.
- `right_end_halt`: a round whose cascade halts on `111` does so at an offset p with F ≤ p + 2.
- `halts_iff`, `halts_iff_right_end`: the machine halts from blank tape if and only if, for some r, the cascade of
  round r+1 halts, and then at p ≥ F − 2.

*Why this is a statement about the machine.* `Casc.vis` and `CascH.vis` derive each cascade from the visit-law
theorems (n visits of the machine, or a halting one among them); `total` shows that every number of visits to an
eventually blank stream is a cascade or a halting cascade; `reach_steps` puts round r of the model on the machine's
run after at least r steps. Nothing about the size of the counts is used: the invariant holds from any starting word
(the explainer's panel lets you try random dirty words).

*What is left.* The counts entering the blocks are about 2^(r/2) at the front of round r and fall by about one
binary digit every 9 cells, reaching a handful of visits only in the last cells of the word. The open question is
now confined there. A stop leaves two adjacent 1s (a *dirty stop*) when its block is `010` hit once, which becomes
`110` with the 1s at F, F+1. The next round then either holds cell F in a block starting at F (it reads `110` and
cleans it), at F−2 (it reads `1011` and writes `1000`), or at F−1, where it reads `011`: with two or more visits there
the machine halts. So the machine halts exactly if a dirty stop is ever met by the next round one cell to the left,
with at least two visits (or a later dirty pattern of this kind).

**Computed (`c/visps.c`, the pipelined simulator with every stop recorded, rounds 1 to 1,000,000):**

| | |
|---|---|
| dirty stops | 4 (the rounds just before the four visits to `1011`) |
| next round after a dirty stop | block at F−2 all 4 times, so `1011` at exactly F−2: the bound of `right_end_1011` is attained |
| next round after a clean stop | block holding F starts at F−2 in 379,302 rounds, at F−1 in 601,268, never at F; 19,425 rounds stop before F |
| visits to `1011` | 4, each at p = F − 2, each followed by a stop 3 cells further right |

| round of the visit to `1011` | its cell | previous round's stop F |
|---|---|---|
| 161,211 | 678,826 | 678,828 |
| 194,647 | 819,721 | 819,723 |
| 757,566 | 3,191,503 | 3,191,505 |
| 906,776 | 3,820,394 | 3,820,396 |

The danger, alignment F−1 after a dirty stop, is common after clean stops (60% of rounds) but has not yet followed
one of the rare dirty stops. Whether it ever does is the right-end question.

```sh
gcc -O2 -o visps holdouts/1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD---/c/visps.c -lpthread
./visps 1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD--- 1000001 - 3 100000   # 76 minutes on 4 cores; EV, DIRTY lines at the end
```

<!-- right-end:end -->

<!-- dfa-search:begin -->
## No small automaton certificate (24 November 2026)

**Computed (SAT, not proved): no assume-guarantee automaton of up to 7 states proves the visit law safe.** This is the
style of busycoq PR #112, applied to the visit law: `py/vsat.py` asks for a DFA that reads a stream from its first
cell, a map `g` with `v(L_q) ⊆ L_g(q)` for every state `q`, closure under the round `S -> v(1 0 S)`, `1 0^inf` accepted,
and every halting prefix rejected. With pysat (CaDiCaL) it is UNSAT for every size from 1 to 7 states, for this
machine (`python3 py/vsat.py a 7`) and for `1RB0LB_0RC0LD_1LD1RE_0LA0RF_1RB0RD_0RB---` (`b`, where `1011 s -> 0001 s`).
It is also UNSAT up to 6 states on the PR59 rules (`pr59`), as it must be, since those machines halt.

This was expected. The four shared rules are exactly those of the PR59 machines, which run 161,210 rounds before they
meet `1011`, and here the danger lies only at the right end of the cascade, where the counts are small and depend on
the whole history. A certificate would have to separate this machine from PR59 by what happens after a dirty stop,
which a few states reading from the front of the stream cannot see. The cascade above is already the column-by-column
view that busycoq PR #110 uses; what is missing is a potential or invariant at the stop.

<!-- dfa-search:end -->

<!-- shift-law:begin -->
## The next round's blocks, and the dirty stop (24 November 2026)

**Proved in Lean (`lean/Shift.lean`, kernel only, standard axioms): where the next round cuts the stream, and what a
dirty stop can do.**

*Tokens.* A block that passes visits on is left as `000`, `100` or `1010` (`Blk.out`). So a round leaves its stream, up
to its stop, as a row of these three *tokens* (`Casc.tokens`), and after round r+1 the stream `1 0 S` is `10`
followed by that row, with the stop F right after it (`reach_toks`).

*The shift law.* The next round reads the row again from the front, and its blocks are cut in a fixed way (`shift`).
Every block starts one or two cells before the end of a token, one block per token, and never at a token boundary.
What is left of the token ahead of the block is `0`, `10` or `00`:

| left before the token | token | the block reads | left before the next token |
|---|---|---|---|
| `0`, `10` or `00` | `1010` | `0 10`, `10 10` or `00 10` | `10` |
| `0`, `10` or `00` | `100` | `0 10`, `10 10` or `00 10` | `0` |
| `0` | `000` | `0 00` | `0` |
| `10` or `00` | `000` | `10 0` or `00 0` | `00` |

The front `10` of `1 0 S` is the first thing left. Every block start the rules allow, for any counts, is one of these
positions or lies at least 3 cells past the last of them (`Starts`, which contains every block of an actual cascade:
`Casc.starts`, `CascH.starts`). The last position is 1 or 2 cells before F, so **the block of round r+2 that holds
round r+1's stop starts at F−1 or F−2 and never at F** (`never_at_stop`). This explains why the run never showed a
block starting at F after any stop.

*The dirty stop.* A stop leaves two adjacent 1s at F and F+1 when its block is `010` hit once (it becomes `110`), or
`011` hit once (it becomes `111`). Then the next round's block at the last position reads `0 11` if `0` is left. That
is `011`, and with a second visit the machine halts. If `10` or `00` is left, the block reads `1011` or `0011`, and
here both become `1000`, so the visit is safe. `dirty` and `dirty_next` state this exactly: a halt of round r+2 lies
at F−1, or at F+1 or beyond. A halt at F−1 needs `0` left. By `fin_r0`, `0` is left exactly when **the last token other
than `000` before the stop is `100`** (`LastO`).

**Derived from these theorems, not in Lean: the count condition.** A dirty stop is a block `010` that gets exactly
one visit. Take a dirty stop that lies inside the row of the round before, as all observed ones do. The shift law,
applied to that round, says that after the dirty round's last doubling block (`1010` or `0010`, which leaves `1010`)
the only blocks are `000` and `010`. Both halve the count, rounding down, and are left `000` after an even number of
visits and `100` after an odd number. So if the last doubling block sends c visits, the blocks behind it get c,
⌊c/2⌋, …, 2 or 3, then 1 at the stop. All of them are left `000` exactly when c is a power of 2. That gives:

> After a dirty stop, the next round meets it one cell to the left (and can halt there) exactly when the count c
> sent by the last doubling block before the stop is not a power of 2.

**Computed (`c/vispl.c`, rounds 1 to 1,000,000, and `py/dirty_counts.py`).**

| rounds 1 to 1,000,000 with a halving chain after the last doubling block | next round's block holding F at F−2 | at F−1 |
|---|---|---|
| c not a power of 2 | 0 | 454,327 |
| c a power of 2, clean stop | 330,167 | 61,631 (a `100`-type block in the chain, which rounds up) |
| c a power of 2, dirty stop | 4 | 0 |

| dirty stop (round, as in the tables above) | stop F | counts from the last doubling block on | next round's block |
|---|---|---|---|
| 161,210 | 678,828 | 2, 1 (sent by a `0010` that got 2) | F−2 |
| 194,646 | 819,723 | 2, 1 | F−2 |
| 757,565 | 3,191,505 | 2, 1 | F−2 |
| 906,775 | 3,820,396 | 2, 1 | F−2 |

With k blocks after the last doubling block (the stop included), c lies in [2^(k−1), 2^k), and c is even (a
doubling block sends 2n or 2(n−1) visits). So k = 2 forces c = 2: **a dirty stop with only one block between it and
the last doubling block is safe whatever the counts.** All four dirty stops have k = 2, while over all rounds k is 2
in only 37.5% of them (19.2% have k = 3, 12.4% k = 4, 30.9% k ≥ 5). A halt therefore needs a dirty stop with k ≥ 3
and c not a power of 2 (c = 6 for k = 3).

So c is a power of 2 at every dirty stop, though in most rounds it is not. Through round 4,000,000 a visit met
`1011` 20 times and the machine never halted. If dirty stops came out safe at the rate c is a power of 2 overall,
46.3% of the rounds with a halving chain, the four safe ones here would have a chance of about 5%, and twenty of about 2·10^-7. A structural
reason for c = 2 at dirty stops is therefore likely, but it has not been found. It would have to tie the counts of two
consecutive rounds together near the stop. A dirty stop comes from a round that falls one cell short of the previous
stop (F = previous F − 1), with counts like 10, 5, 2 (`0010`), 2, 1 in its last blocks.

```sh
gcc -O2 -o vispl holdouts/1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD---/c/vispl.c -lpthread
VLOG=v1m.log ./vispl 1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD--- 1000001 - 3 100000     # about 90 minutes on 3 cores
python3 holdouts/1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD---/py/dirty_counts.py v1m.log
```

**Two rounds in a row near the stop (computed, exact simulation of rounds 1 to 6,000, `py/next_round.py`).** Take a
round whose row ends in `100`, then j blocks `000`, then the stop, and suppose the next round's block reading into
that `100` is a doubling block. Then the next round sends c visits through j + 1 halving blocks, and the block at
F−1 gets ⌊c/2^j⌋ of them. A dirty stop there needs exactly 1. In rounds 1 to 6,000 this value is never 1:

| j | ⌊c/2^j⌋ | next round's visits to the doubling block minus this round's to the `100` |
|---|---|---|
| 0 | 2 (65 rounds) or ≥ 4 (953) | −1 to +2 |
| 1 | ≥ 4 (57) | 0 to +4 |
| 2 | 3 (63) or ≥ 4 (1) | 0 to +4 |
| ≥ 3 | 3 (61) | −1 to +3 |

So in an ordinary round the next round brings about as many visits to the `100` as this one, or a few more. That is
roughly twice what a dirty stop needs, so the visit at F−1 passes on and the round runs past the stop. A dirty stop
needs a round that falls short. At the dirty stops of rounds 161,210 and 194,646 the next round brought 2 visits
where this one had 4. That gap is j = 1, which forces c = 2 and is safe. For a dangerous dirty stop (j ≥ 2), the shortfall
would have to be larger still: the next round would need only about a third of the usual count at that point. No
local law fixes the next round's counts. Over all blocks, the next round's count minus twice this round's count at
the same token is spread widely. Also, a model of the last few blocks that lets the incoming count be anything can
produce the dangerous case (for example, j = 2 and c = 6). So a proof has to use where the counts come from: the
front of the stream, which gets 2^a visits from the left counter in each round.

```sh
python3 holdouts/1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD---/py/next_round.py 6000     # about 40 seconds
```

<!-- shift-law:end -->

## What is established

**Proved in Lean, kernel only:**

- **The halting configurations.** The machine stops exactly when it reads the symbol of a halting transition (F1); the generated statement covers every configuration. (`step_none_iff`, `lean/Blank.lean`)
- **No halt in the first 10,000 steps.** The list simulator of the shared library, proved to agree with the machine's semantics, runs 10,000 steps from blank tape without a halt, evaluated by Lean's kernel. (`blank_runs_kernel`, `lean/Blank.lean`)
- **The three moves of the left counter.** For every n and any tape around them: **increment** `L 1000 (1010)^n 1 D>0 R` reaches `L 1010 1 (0001)^n E>0 R` (n trailing one-digits become zero-digits, the zero-digit before them becomes a one); **overflow without prefix** `0^inf (1010)^n 1 D>0 R` reaches `0^inf 1 0 1 (0001)^n 0 D> R`; **overflow with the prefix 10** `0^inf 1 0 (1010)^n 1 D>0 R` reaches `0^inf 1 0 1 0 0 (0100)^n 0 C> R`. Each is a theorem about the machine's step function with an exact step count. (`left_increment`, `left_overflow_even`, `left_overflow_odd`, `lean/Rules.lean` (generated by `py/gen_rules.py`))

- **The shift law and the dirty stop.** Each round leaves tokens `000`, `100`, `1010` up to its stop. The next round's blocks start 1 or 2 cells before the end of each token and never at a boundary, so the block holding the stop starts at F−1 or F−2. After a dirty stop, the next round can halt there only at F−1, and only if the last token other than `000` before the stop is `100`. (`shift`, `never_at_stop`, `dirty`, `dirty_next`, `fin_r0`, `lean/Shift.lean`)

**Proved in Lean with `native_decide`:**

- **No halt in the first 10^7 steps.** The same run, evaluated by compiled code. (`blank_runs_native`, `lean/Blank.lean`)

**Trusted computation (C/Python, not Lean):**

- **No halt in the first 10^10 steps.** The C simulator `tools/c/tmrun.c` runs 10^10 steps from blank tape without a halt; at the end the tape holds only 91 ones. (`tmrun 1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD--- 10000000000`)
- **No halt in the first 10^9 steps.** The C simulator `tools/c/triage.c` runs 10^9 steps without a halt; at the end 252 cells have been visited and 77 of them hold a 1. (`holdouts/triage.json`)
- **Where a halt can be.** A closed tape language of windows of 5 cells (`tools/py/bbtools/ctl.py`, closure checked by the script, not by Lean) contains every configuration reachable from blank tape, and its only halting configurations have F reading a 1 with a 0 and then a 1 left of the head and a 1 right of it (`0 1 F>1 1`). (`python3 -m bbtools.ctl 1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD--- 5`)
- **The left half is a binary counter of round trips.** Every time D reads the 0 at cell 1 with a 1 at cell 0 (the head about to visit the left half), the cells from the left end to cell 0 read `(10)? w 1` with `w` a word of 4-cell digits `1010` (one) and `1000` (zero), least significant digit next to the centre. In the first 10^9 steps this happens 8,388,630 times and every time the number `w` is one more than the time before, except 45 growth moves, all of the two kinds above: `10`+all ones (b digits) becomes all ones with b+1 digits and no prefix, which overflows at the next visit to `10` + b+1 zeros. (`c/leftchk.c` | `py/leftdec.py` (see Reproduce))
- **The left end grows at 2^k and 3·2^k−1 round trips.** Counting the visits above as round trips T = 1, 2, 3, ..., the left end of the tape grows (by two cells) exactly when T is 2, 3, 4, 6, 8, 12, 16, 24, ..., 2^k, 3·2^k−1, ... up to T = 12,582,912 (all 46 growths in the first 10^9 steps). A round trip costs 135 to 225 steps on average, so the left end grows like the logarithm of the step count. (`c/rightgrow.c`)
- **Not decided by n-gram CPS up to width 14.** The n-gram Closed Position Set decider (`tools/c/ngramcps.c`) with equal widths 4, 6, 8, 10, 12 and 14, plain and with the fixed-length (1) and LRU history augmentations, either reaches a halting local configuration (UNKNOWN) or stops at 3·10^7 local configurations: it does not prove non-halting at these settings. (`ngramcps MACHINE N [-H 1 | -U] -m 30000000`)

**Heuristic:**

- **Growth shape: exp/exp.** Left of the start, the visited part of the tape grows like the logarithm of the step count: each new cell costs a roughly constant factor more time, the signature of a *counter* or of a Collatz-like map whose values are written on the tape (fitted exponent 0.075). Right of the start it grows like the logarithm of the step count: each new cell costs a roughly constant factor more time, the signature of a *counter* or of a Collatz-like map whose values are written on the tape (fitted exponent 0.065). (`tools/py/bbtools/triage.py`)
- **A gap growing by 3.** At the left records at 9.9·10^7, 1.4·10^8, 2.0·10^8 and 2.7·10^8 steps the longest gap shortly after the (1 0)^n stretch has 19, 22, 25 and 28 zeros. This gap is the lowest right-hand segment emptied out (all digits `000`) just after an overflow, and it gains one 3-cell digit per growth. (`tmrun 1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD--- 1000000000 records 100000`)
- **The right half: a chain of counter segments.** Right of the centre the tape is a chain of segments, each a binary counter with 3-cell digits (one of `100`, `010`, `001` for a one, depending on the segment, and `000` for a zero), least significant digit nearest the centre, separated by short markers such as `101` and `010 100`. The lowest segment changes on every round trip; a segment that overflows carries into the next one. At each growth of the left end the lowest segments are re-laid (one segment gains a digit and changes its phase). The right end grows at irregular values of T (974, 1277, 1405, 1903, ..., 8,360,447, 14,168,192), not at powers of 2. The rule for the re-laying has not been found. (`c/rightgrow.c`; read off snapshots, not checked mechanically)

**Open:**

- **Does it halt from blank tape?.** Not known. The macro configuration family has not been found.

## The carry system (round 6)

The community tracker says this machine is "equal to Beaver Math Olympiad problem 10, a seven-rule carry system",
with rules proved in Rocq. We have not seen that statement. What follows is our own derivation from the table; it
has eight rules and the halting pattern, and we cannot say how the Olympiad's seven rules group them.

Write `>` for the head in state B about to read the next cell (moving right) and `<` for the head in state D on the
cell before the mark (moving left). From one such moment to the next the machine does exactly one of:

| rule | before | after | steps | in words |
|---|---|---|---|---|
| R1 | `>011` | `011>` | 3 | pass over 011 |
| R2 | `>0100` | `011>0` | 5 | a digit one becomes 011 and the hit moves on: a carry |
| R3 | `>0101` | `0100>` | 4 | erase the 1 after 010 and go on |
| R4 | `>00` | `0<1` | 2 | turn round on 00, leaving 01 |
| R5 | `0>1` | `<00` | 2 | erase a 1 and go back two cells |
| L1 | `10<` | `<10` | 2 | skip a pair 10 |
| L2 | `00<` | `1>0` | 2 | turn round on 00, leaving 10 |
| L3 | `1<` | `0>` | 1 | erase a 1 and turn round |
| halt | `>0111` | | 5 | R1 in front of a 1 |

The start from blank tape is `1>` (one step of state A). The cases are complete: B reads 1 (R5, or the halt when
the cell on its left is 1), or 00, 011, 0100, 0101; D reads 1, or a 0 with a 1 or a 0 on its left.

**Proved in Lean, kernel only** (`lean/Carry.lean`, generated by `py/gen_carry.py`; plain words for what each theorem says):

- `r1`, `r2`, `r3`, `r4`, `r5_0`, `r5_1`, `l1_0`, `l1_1`, `l2`, `l3`: each rule of the table above, as a statement
  about the machine's step function: from the configuration on the left the machine reaches the configuration on the
  right in exactly the stated number of steps, for every tape around the cells shown. (R5 and L1 are stated twice,
  once for each value of the cell the head lands on.)
- `halt_pattern`: from B about to read `0 1 1 1` the machine halts four steps later, whatever else is on the tape.
  That every halt comes about this way is an argument on paper, read backwards from the table: F is entered only from
  B on a 1, and a B that reads a 1 with a 1 on its left was entered from E on a 1, E from C on a 1, C from B on a 0.
- `carry`: for every k, after a 1, the block `(010)^(k+1) 00` hit by B becomes `(000)^(k+1) 01` with D back on its
  first cell, in 10k + 12 steps. With `010` as the digit one and `000` as zero, lowest digit first, this is binary
  addition of one with a carry through k+1 ones.

**Computed (trusted Python/C, not Lean):**

- The rules replay the run. `py/carry_system.py` knows only the eight rules; 3·10^7 applications stand for 73,332,821
  machine steps, and at every millionth application the tape, head and state equal the plain machine's. Rules used:
  L1 10,000,057; L2 3,333,457; L3 3,333,200; R1 218; R2 3,332,982; R3 3,333,428; R4 3,333,458; R5 3,333,200.
- R1 is rare. R1 is the table entry E1. In the first 10^10 steps it is used 424 times (5 in 10^3 steps, 18 in 10^4,
  46 in 10^5, 90 in 10^6, 148 in 10^7, 228 in 10^8, 306 in 10^9), first at step 77, and each time the cell after the
  `011` is 0. A halt can only happen at one of these moments.

**How the rules count.** A hit on `000` (after a 1) turns round at once and leaves `010` (R4, L1). A hit on `010`
makes it `011` and passes the hit on (R2); when the hit finally turns round, the way back erases every `011` to `000`
(L1, L3, R5 in turn). The left half does the same with pairs: L1 skips pairs `10`, L2 turns the first `00` into
`10`, and R3 on the way back turns every second pair into `00`: the binary counter of round trips in 4-cell digits
(`1010` one, `1000` zero) that `lean/Rules.lean` already proves. In a plain block of digits R1 never fires, because
`011` exists only while a carry is on its way. In the round trips we traced by hand it fires where blocks of different alignment meet on the
right; which meetings can occur is the part that is not understood.

**The open question, as far as we can state it.** Does the rewriting system above, started from `1>` on blank
tape, ever reach `>0111`? We do not have it as a statement about numbers: that needs the right half described as a
list of counters with the rule for what happens where they meet, and we have not found it.

**The proved neighbours.** In the copy of busycoq we read, three machines one entry away from this one are proved:
E1 = `0RF` (`verify/SOMDCv1.v`, module TM13: a closed family of configurations with period 7, non-halting), E1 = `1RF`
(`verify/RRBAv3.v`, `tm455`, non-halting), and F0 = `1RD` (`verify/Eqv_v2.v`, TM511: halts exactly when the solved
machine `1RB---_0LC0RD_1RD1LB_0RE0LA_1LB1RF_0RB1RD` does). Here E1 = `1RB` is rule R1, used from step 77 on, and
F0 = `0LD` is half of rule R5, used in one rule application out of nine. Both entries are reached from blank tape, so
none of these proofs carries over by "the differing entry is never used".

## For later

With the carry system in hand: parse the right half at the moments R1 fires (`py/carry_system.py` can print them) into
blocks of 3-cell digits and the cells between them, and look for the rule that says what stands after an `011`. A first observation: of the 144 uses of R1 in the first
3·10^6 rule applications, 78 come as R3, R4, L2, R1 on `>0101001`, which becomes `0101011>`; so `>01010011` would
halt, and the question there is whether `11` can ever stand after `010100`.

Earlier note: The re-laying rule of the right segments at the growth moments of the left counter. Record the right half at the
46 growth moments (`c/rightgrow.c` prints it before and after), parse it into segments (marker, phase, width, value),
and look for the map between consecutive growth moments; then prove the carry through each kind of marker with
`bbtools.symtm.prove`. A full macro rule would turn this into an induction on T.

## Reproduce

From the repository root:

```sh
. /etc/profile.d/lean.sh      # after scripts/setup-lean.sh
holdouts/1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD---/lean/check.sh      # includes lean/Cascade.lean and lean/Shift.lean
gcc -O2 -o triage tools/c/triage.c && ./triage 1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD--- 1000000000
gcc -O2 -o tmrun tools/c/tmrun.c && ./tmrun 1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD--- 10000000000
cd tools/py && python3 -m bbtools.ctl 1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD--- 5
python3 holdouts/1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD---/py/gen_rules.py | diff - holdouts/1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD---/lean/Rules.lean
gcc -O2 -o leftchk holdouts/1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD---/c/leftchk.c && ./leftchk 1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD--- 1000000000 | python3 holdouts/1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD---/py/leftdec.py
gcc -O2 -o rightgrow holdouts/1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD---/c/rightgrow.c && ./rightgrow 1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD--- 1000000000 | grep ^A
python3 holdouts/1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD---/py/gen_carry.py | diff - holdouts/1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD---/lean/Carry.lean
python3 holdouts/1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD---/py/carry_system.py 30000000 1000000
g++ -O2 -o transcount holdouts/1RB1RF_1RC0RA_1LD1RB_1LE0LD_0RA0LB_0RB---/c/transcount.cpp && ./transcount 1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD--- 10000000000 E1
```

## Pages

- [`pages/holdouts/1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD---/explainer.html`](../../pages/holdouts/1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD---/explainer.html)
- [`pages/holdouts/1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD---/proof-status.html`](../../pages/holdouts/1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD---/proof-status.html)

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same tapes at another pace (observed, not proved).** Leave the states aside and compare only the tape and the place of the head. Then a large part of the first 10^7 configurations of this machine are configurations of the machines below, in the same order and up to the end of the run. The steps at which they occur differ, the tables are not renamings of each other, and equal tapes with different states may be continued differently, so this does not tie the halting questions together.

- [`1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD0LC_0RC---`](../1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD0LC_0RC---/README.md): 7,916,051 configurations, the last at step 9,165,688 here and step 10,000,000 there
- [`1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RB_0RC---`](../1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RB_0RC---/README.md): 7,916,520 configurations, the last at step 9,166,232 here and step 10,000,000 there
- [`1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RC---`](../1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RC---/README.md): 7,916,520 configurations, the last at step 9,166,232 here and step 10,000,000 there
- [`1RB0LB_0RC0LD_1LD1RE_0LA0RF_1RB0RD_0RB---`](../1RB0LB_0RC0LD_1LD1RE_0LA0RF_1RB0RD_0RB---/README.md): 6,666,345 configurations, the last at step 9,165,397 here and step 9,999,999 there
- [`1RB0LB_0RC0LF_1LD1RE_0LA0RB_0RD0RF_0LA---`](../1RB0LB_0RC0LF_1LD1RE_0LA0RB_0RD0RF_0LA---/README.md): 7,916,289 configurations, the last at step 9,165,962 here and step 10,000,000 there

<!-- end of related machines -->
