# 1RB1LE_0LC0RF_1RD0LB_1RE1RD_1RA0RC_1LB---

bbchallenge id 76942. One of the six-state holdouts whose halting from blank tape is open (group G09: the visited tape grows like the square root of the step count on both sides).

**What it does.** A bouncer whose tape, just after a rightward sweep, is a list of blocks of ones separated by single 0s, almost every block of length 4k+3: a list of numbers in unary. The leftward sweep turns each block of 4k+3 ones into 2k+1 single 1s; the rightward sweep zigzags over the list and rebuilds blocks of 4k+3 ones, but different ones: each round trip rewrites the list. The rewrite is decoded (section "The round trip as an XOR rule", proved in Lean): in 4-cell letters s = `0111`, c = `1111` the round trip replaces the word by its running XOR, so backwards in time it is the XOR cellular automaton (rule 102). Only a thin layer at the right end of the tape is not decoded, and a halt can only come from the ends. It halts only if B reads two adjacent 1s, which no run has shown. Decision: open. Twin of [1RB1RA_1RC0RE_1RD1LB_0LE0RF_1RA0LD_1LD---](../1RB1RA_1RC0RE_1RD1LB_0LE0RF_1RA0LD_1LD---/README.md): renaming the states A, B, C, D, E, F here to C, D, E, A, B, F gives that machine's table, so this one is it started in its state C (without the two 1s that machine writes first). The runs differ cell by cell but have the same structure.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LE |
| B | 0LC | 0RF |
| C | 1RD | 0LB |
| D | 1RE | 1RD |
| E | 1RA | 0RC |
| F | 1LB | --- |

## The tape as words

At the first new cell of a visit to the right end, write the tape as the lengths of its blocks of 1s between single 0s. Almost all are 4k+3
(553,908 of 554,278 blocks at every 7th such visit in the first 3·10^8 steps); the exceptions sit where the head was still working. The
k's for a few consecutive visits of the twin 1RB1RA_1RC0RE (this machine's lists differ in detail) (first entry: the partial block at the left end):

```
[2] 1 0 0 3 1 0 0 3 0 1 0 1 5 2 0 0 0 1 0 0 0 0 3 1 0 0 0 0 5 0 0 3 2 1 0 0 0 1 0 2 1 0 0 0 1 3 ...
[10] 0 0 0 2 0 0 4 1 0 0 0 1 0 0 1 0 1 1 0 0 0 1 1 0 0 1 0 1 0 3 3 1 2 1 1 2 0 0 3 0 0 0 0 0 1 1 ...
[2] 0 1 1 0 0 1 5 0 1 1 0 1 2 2 0 1 1 0 2 1 0 1 0 1 0 0 0 4 0 3 0 2 0 0 1 4 1 1 2 0 3 0 5 0 3 0 ...
```

The leftward sweep (state B, rule `left_pairs`) turns each `11` of a block into `10` and the block's left end `0111` into `00010`
(`block_end`): a block of 4k+3 ones becomes `000 (10)^(2k+1)`, so after a leftward sweep the tape is groups of 2k+1 single 1s separated by `000`.
The rightward sweep zigzags: at every block boundary the head backs up a few cells, and inside a group it turns `001`, `010`, `100` into `110`, `101`,
`011` (states C, D, E). A visit adds 1 to 4 cells at the left end and 3 to 8 at the right.

The rewriting of the list is decoded in the next section.

## The round trip as an XOR rule (`lean/Sweep.lean`, `lean/Bulk.lean`)

Cut the tape into 4-cell letters counted from the left end. After a rightward sweep every letter is s = `0111` (a block starts) or
c = `1111` (the block goes on); a block of 4k+3 ones with the 0 before it is s c^k. Write G_k = `1 (0101)^k 000`, the group of 2k+1 single 1s
the leftward sweep makes of it.

| rule | from | to | steps |
|---|---|---|---|
| `block_B` | `L 0111 (1111)^n B> 0 R` | `L B> 0 0001 0 (1010)^n R` | 8n + 6 |
| `group_E` | `L E> 1 (0101)^n 000 R` | `L (0111)^(n+1) A> R` | 4n + 4 |
| `group_A` | `L 0111 A> 1 (0101)^n 000 R` | `L 1111 (1111)^n 0111 E> R` | 28n + 30 |

`left_sweep` chains `block_B` over any list of blocks, `right_sweep` chains `group_E`, `group_A` over any list of pairs of groups: the
rightward sweep reads the groups in E and A in turn, with no exception, writes s^(k+1) for a group read in E, and c^(k+1) for a group read
in A, which also turns the s behind it into c. `outL_eq_pxor`: what the rightward sweep writes is the running XOR (`pxor`) of the letter word
it read, with s = 1. Its inverse is the XOR of neighbours (`xdiff_pxor`). So, with z = 1 for s,

    z_before(n) = z_after(n) XOR z_after(n-1)

at every letter n away from the ends: backwards in time the word evolves by the XOR cellular automaton (elementary rule 102, Pascal's
triangle mod 2), forwards by its inverse, the running XOR. On the list of numbers: read in pairs (a, b), each pair becomes a zeros and
then b + 1.

The ends (observed, not proved):

- The tape grows by exactly one cell at the left end each round trip, and the letter grid moves with it, so the letter index from the
  left end is fixed and the left end is a fixed boundary for the rule. The first 2^j letters repeat with period 2^(j+1) round trips
  (checked for j = 2..7): this is the short cycle of the first numbers.
- At the right end a layer of the last few groups is not in letter form: 13 cells on average and at most about 100 in the first 10^9
  steps, not growing between the first and last third of that run. In about 9% of round trips the rightward sweep turns back before the
  end of the tape. This layer is decoded in the next section.
- Information moves only to the right: a letter after a round trip depends only on the letters left of it.

`py/ca_check.py` checks the rule on the run: at every return to the left end, every letter that two consecutive round trips have in common,
up to the right-end layer. To 2·10^8 steps: 4,159 round trips, 8,492,322 letters, no exception, and the same for the five other machines
with these tapes (listed in that script).

Where a halt can come from: the three rules take a fixed number of steps for every n, so no halt happens in the bulk; a halt (B on two
adjacent 1s) has to come from one of the two ends, and the left end has been periodic in every run so far. The open question is the
right-end layer, fed by the running XOR that arrives from the left.

## The right-end layer (`py/endlayer.py`, `lean/EndRules.lean`)

**Tokens.** Read the tape at a return of the head to the left end (group form) as a list of tokens: `m` is a group
`1 (01)^(m-1)` of m single 1s followed by `000`; `m_2` a group followed by only `00`; `m_0` a group that touches the next
one (`... 1 1 ...`); `m$` the last group of the tape. In the bulk every token is an odd `m`, and the rightward sweep reads
the groups in pairs (a, b), in states E and A; a round trip turns the pair into `1` repeated (a-1)/2 times, then `b+2`
(the XOR rule above, in this notation). The **tail** is what follows the last pair of two odd groups.

**The tail evolves on its own.** Let `G(tail)` be one round trip of the machine on 16 bulk pairs followed by the tail, the
head arriving at the tail in E, until it is back on the bulk: a finite run. It never looks at the pairs except to sweep
them (every call checks that they come back as they should). So after a round trip the right end is (image of the
pairs) + `G(tail)`, and the only input from the rest of the tape is one bit: whether the first token of `G(tail)` is the
first or the second member of a pair at the next round trip (the parity of the running XOR there). The next tail is
`G(tail)` cut after its leading pairs of odd groups (`split` in the script; in the second case the bulk's odd group
in front of it only adds single 1s, so it is written as `1`). The right end is a machine of its own, fed one bit per
round trip by the bulk.

Checked against the runs (`endlayer.py check 1e10`, with `c/endtails.c`): at every round trip of the six machines to
10^10 steps, the tape after the round trip is the image of the pairs followed by `G(tail)`:

| machine | round trips checked | different tails | exceptions |
|---|---|---|---|
| 1RB1LE_0LC0RF_1RD0LB_1RE1RD_1RA0RC_1LB--- | 29,363 | 416 | 0 |
| 1RB---_0RC0LA_1LD0RB_1LE0LB_1LF0LC_1LB1RE | 28,725 | 339 | 0 |
| 1RB---_0RC0LA_1LD0RB_1LE1LD_1LF0LC_1LB1RE | 29,331 | 339 | 0 |
| 1RB0LE_1RC0RE_1RD0RA_1RE1LC_0LA0RF_1LE--- | 28,755 | 409 | 0 |
| 1RB0RD_1RC0RE_1RD1LB_0LE0RF_1RA0LD_1LD--- | 28,833 | 387 | 0 |
| 1RB1RA_1RC0RE_1RD1LB_0LE0RF_1RA0LD_1LD--- | 29,483 | 387 | 0 |

(About 35 round trips per machine are skipped by the check, near the start of the run, where the tape is too short for
its reference point.)

**One model for six machines.** The six machines give the same image of every tail tried (3,000 tails, `endlayer.py
same`), except one: `1 3_0 2_0 1$` becomes `5 3_0 1 2$` for the table of this machine (and its renamings
1RB---_0RC0LA_1LD0RB_1LE1LD_1LF0LC_1LB1RE, 1RB1RA_1RC0RE_1RD1LB_0LE0RF_1RA0LD_1LD---) and `8 1 2$` for the other table
(1RB---_0RC0LA_1LD0RB_1LE0LB_1LF0LC_1LB1RE, 1RB0LE_1RC0RE_1RD0RA_1RE1LC_0LA0RF_1LE---,
1RB0RD_1RC0RE_1RD1LB_0LE0RF_1RA0LD_1LD---). That tail occurs in the runs of 1RB0RD_1RC0RE_1RD1LB_0LE0RF_1RA0LD_1LD---
and 1RB1RA_1RC0RE_1RD1LB_0LE0RF_1RA0LD_1LD---.

**The rules at the front of the tail.** Each is checked on 1,500 random tails for all six machines (`endlayer.py rules`);
the sweep step behind each is a theorem of `lean/EndRules.lean` for every size of group (table below).

- *Pair*: `a b X` with a odd becomes `1`×(a-1)/2, `b+2`, then `G(X)`, for b odd or even. An even group in a second slot
  joins the block behind it (`even_A`) and grows by 2 per round trip: even groups are counters.
- *Even group in a first slot*: `2j b X` becomes `1`×(j-1), `1 3_0 b-1`, then X unchanged (b = 1: `1`×(j-1), `1 3_2`, X).
  The rightward sweep turns back at the even group (`even_E`), so everything right of it skips this round trip. The
  counter is paid out as single groups.
- *Touching group*: `3_0 c X` (c ≥ 2) becomes `1 1 c-1`, then X unchanged; the sweep turns back there too (`touch_E`).
- *Short gap*: at `3_2` the sweep goes on one cell off the grid (`gap2_E`) and leaves a block `11`; the leftward sweep turns
  right again at that block (`even_block_B`), so the part of the tail right of it gets a second round trip in the same
  visit. A short gap in a second slot turns the sweep back (`gap2_A`).
- *The end*: `2$` becomes `1 2$`, `1$` becomes `2 2$`, `3_0 1$` becomes `1 1$`, and a pair `a 2$` becomes its image
  followed by a new `2$`.

So the layer is a handful of particles: even counters that grow in second slots and are paid out in first slots,
stretches frozen for a round trip behind a turn, stretches that run twice as fast behind a short gap, and the end, which
emits new groups. The six runs keep it within about 100 cells of the end.

| rule | from | to |
|---|---|---|
| `even_E` | `L E> 1 (0101)^n 0 1 0 0 0 R` | `L (0111)^n 0 1 1 1 1 1 B> R` |
| `even_A` | `L 0 1 1 1 A> 1 (0101)^n 0 1 0 0 0 R` | `L 1 1 (1111)^n 1 1 1 1 0 1 1 1 E> R` |
| `gap2_E` | `L E> 1 (0101)^n 0 0 R` | `L (0111)^n 0 1 1 E> R` |
| `gap2_A` | `L 0 1 1 1 A> 1 (0101)^n 0 0 R` | `L 1 1 (1111)^n 0 1 1 1 1 B> R` |
| `touch_E` | `L E> 1 (0101)^n 1 R` | `L B> 0 0 (0100)^n R` |
| `touch_A` | `L 0 1 1 1 A> 1 (0101)^n 1 R` | `L 1 1 (1111)^n 0 1 1 0 C> R` |
| `even_block_B` | `L 0 1 1 (11)^n B> 0 R` | `L 1 1 0 1 D> (10)^n R` |
| `halt_even_touch` | `L E> 1 (0101)^n 0 1 0 0 0 1 1 R` | halts (F reads a 1) |

**What a halt needs.** An even group in a first slot followed by a single 1 that touches the next group, `2j 1_0`, halts
(`halt_even_touch`, for every j: E reads the even group, turns back, and F lands on the touching 1). Among all 1,205 tails of at most three tokens (groups up to 5, gaps `000`, `00`, none) these
are the only ones that halt (`endlayer.py halts`), and every random tail that halts contains this pattern.

**Every parity input.** Following the tail from `2$` with both parities allowed at every round trip, so for any content
of the bulk at all, 100,000 different tails are reached (groups up to 60, tails up to 264 cells), for each of the two
tables, and none halts or leaves the model (`endlayer.py explore 100000 60`). This suggests that the right end cannot
halt whatever the bulk does.

**Open.** A finite description of the reachable tails for every parity sequence (a regular language of token lists
closed under `G` and `split`, without `2j 1_0` in a first slot), and the same for the left end, would prove that the
machine never halts. The reachable set is infinite (counters, frozen stretches), so this needs an abstraction of the
counters and of the stretches of odd groups between defects.

## Halting

F1 is the only halting transition; F is entered only by B1 (write 0, move right), so the machine halts exactly when B reads a 1 followed by a
1. In the first 10^9 steps F is entered 117,032,159 times and reads 0 every time.

## Sweep rules (`lean/Rules.lean`)

Generated by `py/rules.py` with `tools/py/bbtools/symtm.py`; every rule holds for all values of `n` and every tape `L`, `R`, with the exact step count. `S>` is the head in state S on the next cell, `(w)^n` is n copies of w, `0^inf` is blank tape.

| rule | from | to | steps |
|---|---|---|---|
| `left_pairs` | `L (11)^n B> 0 R` | `L B> 0 (10)^n R` | 4 · n |
| `left_pairs_C` | `L (11)^n C> 1 R` | `L C> 1 (01)^n R` | 4 · n |
| `right_C` | `L C> (001)^n R` | `L (110)^n C> R` | 3 · n |
| `right_D` | `L D> (010)^n R` | `L (101)^n D> R` | 3 · n |
| `right_E` | `L E> (100)^n R` | `L (011)^n E> R` | 3 · n |
| `block_end` | `L 0 1 1 1 B> 0 R` | `L B> 0 0 0 1 0 R` | 6 |
| `right_end` | `L 0 D> 0^inf` | `L B> 0 0 0 1 0 0^inf` | 9 |
| `right_end_A` | `L 0 A> 0^inf` | `L B> 0 0 0 0^inf` | 3 |
| `left_end` | `0^inf C> 0 0 1 R` | `0^inf 1 1 0 C> R` | 3 |
| `ones` | `L D> 1^n R` | `L (1)^n D> R` | n |

## Status

Open. Lean, kernel only: the halting configurations (`step_none_iff`), no halt in 10,000 steps (`lean/Blank.lean`), the sweep rules (`lean/Rules.lean`), the round trip on the bulk as a running XOR (`lean/Sweep.lean`, `lean/Bulk.lean`), the sweep at the defects of the right-end layer and its halting pattern (`lean/EndRules.lean`). Lean with `native_decide`: no halt in 10^7 steps. C: no halt in 10^10 steps (`tools/c/tmrun.c`). Observed: the unary-list structure; the blocks of 4k+3 ones.

**For later.** The right-end layer is decoded as a machine of its own fed one parity bit per round trip (section "The right-end layer"); no halt in 100,000 of its tails reached under every parity input. Next: a regular invariant of those tails without the halting pattern `2j 1_0`, and the same for the left end.

## First look

Growth class **sqrt/sqrt** (left: sqrt, exponent 0.496; right: sqrt,
exponent 0.503). After 1,000,000,000 steps: 36,588 cells visited (6,817 left of the
start, 20,161 right), 21,207 ones.

- left, step 972,061,182: `C>0 0 1 0^3 1 0^3 1 0 1 0 1 0^3 1 0^3 1 0^3 1 0^3 1 0 1 0 1 0^3 1 0 1 0 1 0 1 0 1 0^3 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0^3 1 0^3 1 0 1 0 1 0 1 0 1 0^3 1 0 1 0 1 0^3 1 0^3 1 0 1 0 1 0^3 1 0 1 0 1 0 1 0 1 0 1 0 1 0^3 1 0^3 1 0 1 0 1 0^3 1 0^3 1 0 1 0 1 0^3 1 0 1 0 1 0 1 0 1 0^3 1 0 1 0 1 0^3 1 0 1 0 `
- left, step 987,812,176: `C>0 0 1 0^3 1 0 1 0 1 0^3 1 0^3 1 0 1 0 1 0 1 0 1 0^3 1 0^3 1 0^3 1 0 1 0 1 0^3 1 0 1 0 1 0 1 0 1 0^3 1 0^3 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0^3 1 0 1 0 1 0^3 1 0^3 1 0 1 0 1 0^3 1 0 1 0 1 0^3 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0^3 1 0 1 0 1 0^3 1 0 1 0 1 0^3 1 0^3 1 `
- right, step 976,869,914: `1^10 0 1^3 0 1^19 0 1^3 0 1^3 0 1^7 0 1^11 0 1^7 0 1^3 0 1^3 0 1^7 0 1^3 0 1^11 0 1^11 0 1^7 0 1^11 0 1^3 0 1^7 0 1^3 0 1^3 0 1^7 0 1^11 0 1^3 0 1^3 0 1^3 0 1^11 0 1^7 0 1^11 0 1^3 0 1^3 0 1^11 0 1^3 0 1^15 0 1^3 0 1^7 0 1^3 0 1^11 0 1^3 0 1^3 0 1^7 0 1^7 0 1^3 0 1^3 0 1^3 0 1^7 0 1^27 0 1^3 0 1^3 0`
- right, step 992,885,655: `1^2 0 1^7 0 1^3 0 1^11 0 1^19 0 1^7 0 1^7 0 1^3 0 1^7 0 1^15 0 1^3 0 1^3 0 1^7 0 1^7 0 1^3 0 1^27 0 1^3 0 1^3 0 1^3 0 1^3 0 1^3 0 1^3 0 1^27 0 1^3 0 1^15 0 1^19 0 1^27 0 1^7 0 1^3 0 1^3 0 1^11 0 1^3 0 1^7 0 1^7 0 1^3 0 1^3 0 1^15 0 1^15 0 1^11 0 1^3 0 1^3 0 1^7 0 1^27 0 1^3 0 1^3 0 1^7 0 1^7 0 1^23 `

## Deciders tried (F11, 13 November 2026)

None closes. Each reaches a halting configuration in its abstraction, which says nothing about halting.

- n-gram CPS (`tools/c/ngramcps.c`), equal widths on both sides: a halting local configuration is reached with plain up to width 24, history 1 up to width 24, history 2 up to width 24, history 3 up to width 24, LRU history up to width 7 (larger widths ran out of the 150 s or 60 million configuration budget).
- n-gram CPS with every cell tagged by its position mod p: fails for p = 2 up to width 20, p = 3 up to width 20, p = 4 up to width 20, p = 6 up to width 20.
- n-gram CPS where each side also carries the state of a small automaton that has read that side from the far end (every automaton with up to 3 states on both sides, or 4 states on one side), with position mod 1..4 and widths 4, 6, 8: no closed set without a halt in all 120 parameter sets.
- Run-length windows (the K nearest runs of equal macro cells on each side, run lengths kept exactly below T and mod M above): fails for all 72 parameter sets (cells of 1 to 4 bits, K = 2, 4, 6, T = 2, 4, M = 1, 2, 4).
- Two-automaton closed tape language by SAT (a deterministic automaton reading each side inward, n states each, CaDiCaL): no solution for n = 2..8; n = 9 not finished in 150 s.

## Where a halt can come from

`lean/Route.lean` (kernel, written by `py/route.py`): `halt_route`, two steps before any halt the machine is in one
of: A with 0 under the head, 1 right, 1 two right; F with 1 left, 0 under the head.

## Pages

- [`pages/holdouts/1RB1LE_0LC0RF_1RD0LB_1RE1RD_1RA0RC_1LB---/explainer.html`](../../pages/holdouts/1RB1LE_0LC0RF_1RD0LB_1RE1RD_1RA0RC_1LB---/explainer.html)
- [`pages/holdouts/1RB1LE_0LC0RF_1RD0LB_1RE1RD_1RA0RC_1LB---/proof-status.html`](../../pages/holdouts/1RB1LE_0LC0RF_1RD0LB_1RE1RD_1RA0RC_1LB---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LE_0LC0RF_1RD0LB_1RE1RD_1RA0RC_1LB---/lean/check.sh
python3 holdouts/1RB1LE_0LC0RF_1RD0LB_1RE1RD_1RA0RC_1LB---/py/rules.py | diff - holdouts/1RB1LE_0LC0RF_1RD0LB_1RE1RD_1RA0RC_1LB---/lean/Rules.lean
python3 holdouts/1RB1LE_0LC0RF_1RD0LB_1RE1RD_1RA0RC_1LB---/py/ca.py | diff - holdouts/1RB1LE_0LC0RF_1RD0LB_1RE1RD_1RA0RC_1LB---/lean/Sweep.lean
python3 holdouts/1RB1LE_0LC0RF_1RD0LB_1RE1RD_1RA0RC_1LB---/py/ca_check.py 200000000
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB---_0RC0LA_1LD0RB_1LE1LD_1LF0LC_1LB1RE`](../1RB---_0RC0LA_1LD0RB_1LE1LD_1LF0LC_1LB1RE/README.md): rename A→F, B→B, C→C, D→D, E→E, F→A and exchange left and right; it is this table started in state F, in a mirror
- [`1RB1RA_1RC0RE_1RD1LB_0LE0RF_1RA0LD_1LD---`](../1RB1RA_1RC0RE_1RD1LB_0LE0RF_1RA0LD_1LD---/README.md): rename A→C, B→D, C→E, D→A, E→B, F→F; it is this table started in state D

**Same tapes at another pace (observed, not proved).** Leave the states aside and compare only the tape and the place of the head. Then a large part of the first 10^7 configurations of this machine are configurations of the machines below, in the same order and up to the end of the run. The steps at which they occur differ, the tables are not renamings of each other, and equal tapes with different states may be continued differently, so this does not tie the halting questions together.

- [`1RB0LE_1RC0RE_1RD0RA_1RE1LC_0LA0RF_1LE---`](../1RB0LE_1RC0RE_1RD0RA_1RE1LC_0LA0RF_1LE---/README.md): 9,589,851 configurations, the last at step 9,589,854 here and step 10,000,000 there

<!-- end of related machines -->
