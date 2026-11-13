# 1RB1LC_1LC0RF_0LF1LD_0LE---_1RF1LC_1LE0RA

bbchallenge id 126128, a BB(6) holdout (group G06). Family: **3/2 Collatz-like map with a tail of digits**. Open;
each phase multiplies a block length by about 3/2 and its parity steers a short tail of digits.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LC |
| B | 1LC | 0RF |
| C | 0LF | 1LD |
| D | 0LE | --- |
| E | 1RF | 1LC |
| F | 1LE | 0RA |

## What it does

Everything happens left of the start. A **phase** starts when the head, in state C, reaches a new cell at the left
end followed by a block of `l` cells (`1^l` or `10 1^(l-2)`) and a short **tail** `T`, often empty. During the
phase the left part is `0^inf F> 0 0 (110)^x 1^y T`:

* `round` (`lean/Rules.lean`): `0^inf F> 0 0 (110)^x 1^(y+5) R` -> `0^inf F> 0 0 (110)^(x+2) 1^(y+1) R` in 12x+26
  steps, for all x, y and every tape R;
* `rounds` (`lean/Rounds.lean`, induction): `(110)^x 1^(y+4k+1)` -> `(110)^(x+2k) 1^(y+1)` for every k.

Four ones become two words of three cells, so when the ones are used up the block is about `3l/2` long. The phase
map (computed with `c/m6phase.c`, on the run and on constructed tapes):

* empty tail, `l` even: `l' = 3l/2 + 4`, empty tail;
* empty tail, `l` odd: `l' = (3l+5)/2`, tail `011`;
* tail `(011)^c`, `l` even: `l' = 3l/2 + 4 + 3c`, empty tail;
* odd `l` with a non-empty tail, and other tails: longer tails such as `011111111011` (not yet worked out).

From blank tape (first phase start at step 3920, `0^inf E> 0 0 1^86`) the lengths are 88, 136, 208, 316, 478, 721,
1084 (tail 011), 1633, 2452 (011), 3685, 5530 (011), 8302, 12457, 18688 (011), 28039, 42061 (011), 63091 (tail
`011111111011`, at step 2.4*10^9). 42061 is the first odd length with a non-empty tail.

### The run, jumping over the rounds (`c/m6fast.c`)

`m6fast` applies the Lean rule `rounds` in one stroke (exact step counts, 128-bit). From blank tape it reaches 47
phase starts, the last at step 3,428,480,554,246,233,263 with l = 2,390,425,546 (3 minutes, 3 GB of tape), without
a halt. Write a tail as `[b1,b2,...]` for `0 1^b1 0 1^b2 ...`. Only `[]`, `[2]`, `[8,2]`, `[26,2]`, `[359,2]` occur,
and for large l (measured at l = 10^5 to 10^5+3, from constructed starts `m6fast 1 SIZE l b1,b2`) the map is

| tail | l even | l odd |
|---|---|---|
| `[]` | 3l/2 + 4, `[]` | (3l+5)/2, `[2]` |
| `[2]` | 3l/2 + 7, `[]` | (3l-1)/2, `[8,2]` |
| `[8,2]` | 3l/2 + 19, `[]` | (3l-19)/2, `[26,2]` |
| `[26,2]` | 3l/2 + 46, `[]` | (3l-625)/2, `[359,2]` |
| `[359,2]` | 3l/2 + 538, `[8,2]` | (3l-1717)/2, `[1232,2]` |
| `[1232,2]` | 3l/2 + 1855, `[]` | (3l-3079)/2, `[2780,2]` |

The 47 phases follow it exactly (e.g. 63091 `[8,2]` -> 94627 `[26,2]` -> 141628 `[359,2]` -> 212980 `[8,2]` ->
319489 `[]`).

### Where the halts-iff reduction stops

The lead asked for a reduction "halts iff the map reaches ...". It is not reached:

* The constants for `[b,2]` are not a simple function of b: the block `1^b` is worked through like a small copy of
  the run (odd l on `[5534,2]` leaves `[18692,2]`, then `[42065,2]`, next to the main run's 5530, 18688, 42061), and
  some b leave longer tails (`[42065,2]`, odd l: `[212987,8,2]`). So the tails do not form a finite family; the
  natural state is a nested list of blocks, each with its own 3/2 dynamics.
* When b is not small against l the outputs change regime (`[26,2]` from l = 101, 201: other lengths and tails).
* None of the phase ends is proved in Lean; only the rounds are.

No halting tail has been found in any of these experiments.

## Status

Open. Lean: `lean/Blank.lean` (halting configurations, no halt in 10^4 steps by the kernel, 10^7 by
`native_decide`), `lean/Rules.lean` and `lean/Rounds.lean` (the rounds above). The only halting transition is D
reading 1; the rounds cannot halt, so a halt can only come at a phase end, where the tail is rewritten. The parities of
`l`, which grows by a factor 3/2 a phase, decide what the tail does: a problem of the same kind as Mahler's 3/2
problem and the Antihydra cryptid, so a decision is not expected.

## For later

* Decode the nested-tail process (a tail block run as its own phase sequence) and prove the phase ends with symtm;
  then a halts-iff statement on the nested map would be in reach.
* Work out the phase end for general tails (the digit words and their rules), prove them with symtm, and iterate the
  map far beyond plain simulation (a phase costs about 2.25 times the one before).
* Then look for a halting tail reachable under some choice of parities, as for 1RB1LB_1LC1LA_1RD0LB_1RA1RE_1RF0RD_---1RD.

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LC_1LC0RF_0LF1LD_0LE---_1RF1LC_1LE0RA/lean/check.sh
gcc -O2 -o m6phase holdouts/1RB1LC_1LC0RF_0LF1LD_0LE---_1RF1LC_1LE0RA/c/m6phase.c && ./m6phase 86 "" 17
gcc -O2 -o m6fast holdouts/1RB1LC_1LC0RF_0LF1LD_0LE---_1RF1LC_1LE0RA/c/m6fast.c && ./m6fast 47 3221225472
```

## Remainder classes (family survey)

- **Rounds between end events, by remainder class** (trusted). Sample the run whenever the head is in state A reading 0 with only 0s to its right. Read leftwards from the head, the tape is then `A U^m B`: one long periodic block between two short context words. For each class (A, U, B, m mod 4) the next sample is simulated for six values of m and extended as an affine map of m (with a cubic step count). Along the direct run from blank tape to 3·10^9 steps (23 events) the class map predicts the next event in all 14 rounds it applies to. This is an extrapolation checked by computation, not a proof. Command: `python3 holdouts/1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---/py/ctxround.py 1RB1LC_1LC0RF_0LF1LD_0LE---_1RF1LC_1LE0RA R A 0 check 3e9`
- **189 rounds of the class map without a halt** (heuristic). Iterated with exact integers from the event at step 57,486 of the run (A = `0`, U = `001`, m = 104, B = `(empty)`): 189 rounds without meeting a halting class; m then has 77 bits (about 10^47 steps of the machine). 38 distinct contexts occur, the longest of 6,270 cells. The iteration stops there, at a context too large for the six simulations (a second long block has formed); this is a limit of the tool, not an event of the machine. Command: `python3 holdouts/1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---/py/ctxround.py 1RB1LC_1LC0RF_0LF1LD_0LE---_1RF1LC_1LE0RA R A 0 orbit 189`
- **No halting class among 22 contexts** (heuristic). Breadth first from the starting context, with every remainder at every context (whether or not the numbers can really produce that sequence of remainders, and only for m large compared with the contexts): 22 contexts expanded, 22 found, to depth 10. None of them halts; the search is not complete (the set of contexts keeps growing), and it says nothing about a halt that needs a context as long as the block itself. 8 contexts longer than 300 cells were not expanded. Command: `python3 holdouts/1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---/py/ctxround.py 1RB1LC_1LC0RF_0LF1LD_0LE---_1RF1LC_1LE0RA R A 0 bfs 22`

## Pages

- [`explainer.html`](../../pages/holdouts/1RB1LC_1LC0RF_0LF1LD_0LE---_1RF1LC_1LE0RA/explainer.html)
- [`proof-status.html`](../../pages/holdouts/1RB1LC_1LC0RF_0LF1LD_0LE---_1RF1LC_1LE0RA/proof-status.html)

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB1LC_1LA0RD_0LB1LF_1RE1LC_1LC0RB_0LA---`](../1RB1LC_1LA0RD_0LB1LF_1RE1LC_1LC0RB_0LA---/README.md): rename A→D, B→E, C→C, D→F, E→A, F→B; it is this table started in state E
- [`1RB0LC_1LA1RE_1LD1RE_1RE0LA_0RA1RF_0RB---`](../1RB0LC_1LA1RE_1LD1RE_1RE0LA_0RA1RF_0RB---/README.md): rename A→C, B→D, C→E, D→F, E→B, F→A and exchange left and right; it is this table started in state F, in a mirror

<!-- end of related machines -->
