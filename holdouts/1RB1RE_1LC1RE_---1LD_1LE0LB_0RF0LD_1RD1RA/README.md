# 1RB1RE_1LC1RE_---1LD_1LE0LB_0RF0LD_1RD1RA

bbchallenge id 4905. One of the six-state holdouts whose halting from blank tape is open.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RE |
| B | 1LC | 1RE |
| C | --- | 1LD |
| D | 1LE | 0LB |
| E | 0RF | 0LD |
| F | 1RD | 1RA |

## What it does: halve blocks from the left with a carry, pour the halves to the right

Look at the tape each time the head comes back to the left end (state E, on the blank cell left of the tape). From
step 50 on it has the form

    E> 0  1 a^x0 110 a^x1 110 ... 110 a^xk          a = 01

so the tape is a **list of numbers [x0, x1, ..., xk]**; blocks can be empty (the earlier notes wrote `110110` as a
separator D: it is an empty block). One *round* takes a left-end tape to the next one. From blank tape the lists are

    [0,0,2] [2,2] [7] [13] [22] [10,0,22] [7,32] [2,57] [30,0,62] [17,92] [7,157] [2,81,0,160] [84,0,162] ...

A round has two parts.

* **Sweep.** The head runs right once. Block by block it turns pairs `0101` into `b = 0111` (so a block of x a's
  becomes about x/2 b's) as long as a *carry* survives: the first block passes the carry on when it is odd, every
  later block when it is even. A block that stops the carry is still halved, and all blocks after it are left as
  they are (their separators become a single `1`).
* **Drains.** Then, from the right end, one trip per b, last b first: the trip turns the b back into a's and
  returns, adding one a to the block just right of the b's and two to the last block (`drainS`, `drainSD` in
  `lean/Rules.lean`, for every list of blocks). When a group of b's is used up, the two short blocks left at its
  place merge with their neighbours, and the group to its left is drained in the same way.

### The round map in closed form (large blocks)

Write the result of the sweep as groups of b's with counts m0, m1, ..., one per halved block:

| block | passes the carry on | b's | otherwise | b's |
|---|---|---|---|---|
| first, x0, with other blocks after it | x0 odd | (x0-5)/2 | x0 even: sweep ends, next block +5, the others +1 | x0/2 - 2 |
| a later block x, not the last | x even | x/2 - 3 | x odd: sweep ends, next block +5, the others +1 | (x-5)/2 |
| the last block x, reached with the carry | | | x even: leaves `a` | x/2 - 1 |
| | | | x odd: leaves `a^2 1011 a` (a new empty block) | (x-5)/2 |
| a single block [x] | | | x odd: leaves `a` | (x-1)/2 |
| | | | x even: leaves `a^2 1011 a` | x/2 - 2 |

Then with R the list of blocks right of the last group (R = [1] or [2, 1] when the carry reached the last block), for
the groups from last to first: R[0] += m, R[last] += 2m; then, for a group that is not the first, R[0] += 4,
R[last] += 2 and a new block 2 is put in front of R; for the first group R[last] += 2. The next left-end list is R
with every block but the last one less, the last one more (and an empty block before the last in the `1011` cases).
This is `closed` in `py/roundmap.py`; it holds whenever no b-count above is negative. Worked out for short lists:

    [x]            x odd    ->  [(3x+5)/2]                      x even  ->  [x/2-1, 0, x]
    [x0, x1]       x0 even  ->  [3x0/2 + x1 + 2]
    [x0, x1, .., xk]  x0 even, k >= 2  ->  [x0/2 + x1 + 2, x2, .., xk + x0]
    [x0, x1]       x0 odd, x1 even  ->  [(x0-3)/2, x0 + 3x1/2 + 2]
    [x0, x1]       x0 odd, x1 odd   ->  [(x0-3)/2, (x1+5)/2, 0, x0 + x1 - 4]

So a single block is a Collatz-like number: it is multiplied by 3/2 while odd, and when even it splits off its half
as a new first block, which is then halved again and again (an odd first block x0 always goes to (x0-3)/2) while the
halves are poured into the blocks on the right. The total number of a's grows by about a factor 1.24 per round
(0.31 bits), the step count by its square: the tape length goes like the square root of the step count.

### Small blocks, and the exact map

Blocks smaller than 6 change the sweep locally (a block of 0, 2 or 4 a's met with the carry has no room for a group
of b's and borrows from the group before it), and such blocks occur all the time (the empty block before the last
one, the blocks 2 and 3 left by used-up groups). Instead of a table of all small cases, `py/roundmap.py` computes
the round **exactly for every list** this way: for a fixed parity, the round is affine in each block above 16, so
`nxt` cuts every large block down to 16 or 17, runs the cut-down tape and its neighbours (one block larger by 2,
by 4) on the plain machine, checks that the two differences agree, and extends linearly. This is exact as far as
that affinity holds; it is checked, not proved: 6,000 random lists of up to 6 blocks with values up to 70 against
the plain machine (`py/orbit.py test`), and all 1,669 multi-block left-end tapes of the independent accelerated run to
10^400 steps (`py/run.py`, which does not print single-block tapes).

## Does it halt?

The only halt is C reading 0. On the lists above it happens in exactly two ways (all 2,899 lists of up to three
small blocks and 20,000 random lists of 2 to 6 blocks below 10 were run on the plain machine, `py/direct.py`):

* the first block is **x0 = 1** and there is another block: the machine stops after 21 steps (29 when the next block
  is empty), whatever the rest of the tape (`halt1S`, `halt1D` in `lean/Rules.lean`, kernel);
* the tape is the single empty block [0] (7 steps). It has not occurred in the orbit.

By the map, x0 = 1 comes from [5, ...] (odd first blocks go to (x0-3)/2) or from the single block [4] (which goes to
[1, 0, 4]). A run of odd first blocks halves x0 + 3, so **the machine halts iff some run of odd rounds starts with
x0 + 3 a power of two, or a single block [4] occurs** (provided the orbit stays among the lists the map handles: a
few small lists, e.g. [3, 0, x] and [0, x, 0], lead to a tape outside the family, and `nxt` raises an error
there; the orbit has not met one).

From blank tape the map has been iterated for **1,000,000 rounds without a halt** (`py/orbit.py`): at the end the
tape holds a number of a's with 314,797 bits, so the machine has run more than 10^94,000 steps (a round takes more
steps than the tape is long). The earlier accelerated run, which simulates the machine itself, covers the first 2,110
rounds (10^400 steps).

**Heuristic.** This is a Collatz-like (cryptid-like) question: halting needs a specific number to be exactly a power
of two. If x0 at the start of a run of odd rounds behaves like a random number of n bits, the chance is about 2^-n,
and n grows steadily. Past the rounds already followed every such x0 has tens of thousands of bits: the machine
almost certainly does not halt, but a proof would need to control a 2-adic property of an exponentially growing
orbit, which is out of reach in the same way as for the known cryptids.

## For later

Stopped at: the complete round map as a computed function on lists (closed form for large blocks, exact
extrapolation for small ones), checked against the machine; the halting condition in terms of it; the drain trips and
the halting rounds in Lean. Not done: the reduction in Lean. Next: (1) the sweep as symbolic rules: the in-place
conversion `b^k E> a a -> b^(k+1) E>` is a linear cycle (`bbtools.cycles`), the carry passing from one block to the
next a fixed stretch (`symtm.prove`), with the case split by parity; the borrow of the small blocks 0, 2, 4 needs
its own cases, also when the group before is itself empty; (2) the end of a group in the drains (the merge of
`a^4 11 a^p`) and the last return to the left end as rules over lists (`seqtm`); (3) define the map on lists in
Lean, prove one round for every list by induction over the groups, then `HaltsFromBlank <-> the orbit reaches
x0 = 1` as in `holdouts/1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD/lean/Reduction.lean`; the tapes outside the
family have to be excluded by an invariant of the orbit or included as further cases.

## Files

- `lean/Rules.lean` (generated by `py/rules.py`): `drain1`, `drain2D` (drain trips with one and two blocks, exact step
  counts), `drainS`, `drainSD` (any list of middle blocks, `bbtools.seqtm`, `lean/Seq.lean`), `halt1S`, `halt1D` and
  their `_stop` lemmas (first block 1: the machine stops).
- `py/roundmap.py`: the round map on lists: `closed` (closed form, large blocks) and `nxt` (every list).
- `py/direct.py`: one round on the plain machine, from a list of blocks.
- `py/orbit.py`: iterates the map from blank tape (`orbit.py 1000000`, about 9 minutes), compares it with the tapes of `run.py`
  (`orbit.py 3000 rounds.txt`) and with the plain machine on random lists (`orbit.py test 6000`).
- `py/run.py`: the run from blank tape with the accelerator `py/genacc.py` (exact run-length simulation
  `py/rlsim.py`, plus linear cycles extrapolated once seen three times: here the drain trips); prints the tape at
  the left-end visits with more than one block.
- `py/rounds.py`: reads that output and checks the rule for odd first blocks; `py/try.py`: runs a built tape.

## Status

Open. Lean (`lean/Blank.lean`): the halting configurations (`step_none_iff`), no halt in 10,000 steps by
the kernel, in 10,000,000 by `native_decide`. Lean (`lean/Rules.lean`, kernel): drain trips, halting from x0 = 1.
C (`tools/c/triage.c`): no halt in 1,000,000,000 steps. Python: no halt in 10^400 steps of the machine
(`py/run.py`), and in 1,000,000 rounds of the round map (`py/orbit.py`, more than 10^94,000 steps), the map being
checked against the plain machine but not proved.

## Pages

- [`pages/holdouts/1RB1RE_1LC1RE_---1LD_1LE0LB_0RF0LD_1RD1RA/explainer.html`](../../pages/holdouts/1RB1RE_1LC1RE_---1LD_1LE0LB_0RF0LD_1RD1RA/explainer.html)
- [`pages/holdouts/1RB1RE_1LC1RE_---1LD_1LE0LB_0RF0LD_1RD1RA/proof-status.html`](../../pages/holdouts/1RB1RE_1LC1RE_---1LD_1LE0LB_0RF0LD_1RD1RA/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RE_1LC1RE_---1LD_1LE0LB_0RF0LD_1RD1RA/lean/check.sh
python3 holdouts/1RB1RE_1LC1RE_---1LD_1LE0LB_0RF0LD_1RD1RA/py/run.py 1e100 > /tmp/rounds.txt
python3 holdouts/1RB1RE_1LC1RE_---1LD_1LE0LB_0RF0LD_1RD1RA/py/rounds.py /tmp/rounds.txt
python3 holdouts/1RB1RE_1LC1RE_---1LD_1LE0LB_0RF0LD_1RD1RA/py/orbit.py test 6000
python3 holdouts/1RB1RE_1LC1RE_---1LD_1LE0LB_0RF0LD_1RD1RA/py/orbit.py 3000 /tmp/rounds.txt
python3 holdouts/1RB1RE_1LC1RE_---1LD_1LE0LB_0RF0LD_1RD1RA/py/orbit.py 100000
```
