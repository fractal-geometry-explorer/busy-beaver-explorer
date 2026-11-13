# 1RB1LC_1LA0RD_0LB1LF_1RE1LC_1LC0RB_0LA---

bbchallenge id 65944. One of the six-state holdouts. Analyzed by hand (group G02), partly.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LC |
| B | 1LA | 0RD |
| C | 0LB | 1LF |
| D | 1RE | 1LC |
| E | 1LC | 0RB |
| F | 0LA | --- |

## What it does

Sample: B at the left end, `K(pre, N, S) = 0^inf B> 0 0 pre 1^N S 0^inf`, pre in {empty, `10`}, S a short word.
Each round trip turns 4 ones into two words `110` (`B>0 0 a^8705 1^18465` -> `a^8707 1^18461` at 10^9 steps);
when the ones are used up the run of `110` is rebuilt into a block of ones about 3/2 as long. Samples of the run:
N = 175, 263, 395, 584, 923, 1388, 2090, 3140, 4717, 7074, 10624, 15940, 23914, 35873, 53811 (to 1.7·10^9 steps).

Measured map (`py/kmap.py`, N = 20..31), pre empty and S empty:

    N = 4j   -> (empty, 3N/2 + 4, empty)       N = 4j+1 -> (10, (3N+1)/2, 011)
    N = 4j+2 -> (10,    3N/2 + 2, empty)       N = 4j+3 -> (empty, (3N+5)/2, 011)

With pre = `10` the offsets are 3N/2 + 7, 3N/2 + 5, (3N+7)/2, (3N+11)/2. So: a **Collatz-like 3n/2 map** with a
one-bit prefix, and odd N feed a counter-like word S at the right end.

## Lean

`lean/Rules.lean` (from `py/rules.py`): fourteen shift rules over 3-cell words.

## Halting

Only F1 halts. Open; n-gram CPS (widths 3..7) fails; no halt in 10^9 steps (C). `bbtools.cycles` (K = 1..3) makes
little progress within 40 s.

## Notes for later

* Prove the round-trip rule (`1^(N+4)` -> two more `110`) and the rebuild with `bbtools.symtm`, then the map for the
  other S words; work out the S counter and where F1 can fire.
* Compare with the sister machine `1RB1LC_1LA0RD_1LB1LF_1LE1RE_0LA0RB_0LB---` (shared rows A, B, D; a 4n/3 map).

## Remainder classes (family survey)

- **Rounds between end events, by remainder class** (trusted). Sample the run whenever the head is in state B reading 1 with only 0s to its right. Read leftwards from the head, the tape is then `A U^m B`: one long periodic block between two short context words. For each class (A, U, B, m mod 4) the next sample is simulated for six values of m and extended as an affine map of m (with a cubic step count). Along the direct run from blank tape to 3·10^9 steps (26 events) the class map predicts the next event in all 15 rounds it applies to. This is an extrapolation checked by computation, not a proof. Command: `python3 holdouts/1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---/py/ctxround.py 1RB1LC_1LA0RD_0LB1LF_1RE1LC_1LC0RB_0LA--- R B 1 check 3e9`
- **448 rounds of the class map without a halt** (heuristic). Iterated with exact integers from the event at step 41,888 of the run (A = `11`, U = `100`, m = 87, B = `1`): 448 rounds without meeting a halting class; m then has 178 bits (about 10^108 steps of the machine). 38 distinct contexts occur, the longest of 6,267 cells. The iteration stops there, at a context too large for the six simulations (a second long block has formed); this is a limit of the tool, not an event of the machine. Command: `python3 holdouts/1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---/py/ctxround.py 1RB1LC_1LA0RD_0LB1LF_1RE1LC_1LC0RB_0LA--- R B 1 orbit 448`
- **No halting class among 22 contexts** (heuristic). Breadth first from the starting context, with every remainder at every context (whether or not the numbers can really produce that sequence of remainders, and only for m large compared with the contexts): 22 contexts expanded, 22 found, to depth 9. None of them halts; the search is not complete (the set of contexts keeps growing), and it says nothing about a halt that needs a context as long as the block itself. 8 contexts longer than 300 cells were not expanded. Command: `python3 holdouts/1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---/py/ctxround.py 1RB1LC_1LA0RD_0LB1LF_1RE1LC_1LC0RB_0LA--- R B 1 bfs 22`

## Pages

- [`pages/holdouts/1RB1LC_1LA0RD_0LB1LF_1RE1LC_1LC0RB_0LA---/explainer.html`](../../pages/holdouts/1RB1LC_1LA0RD_0LB1LF_1RE1LC_1LC0RB_0LA---/explainer.html)
- [`pages/holdouts/1RB1LC_1LA0RD_0LB1LF_1RE1LC_1LC0RB_0LA---/proof-status.html`](../../pages/holdouts/1RB1LC_1LA0RD_0LB1LF_1RE1LC_1LC0RB_0LA---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LC_1LA0RD_0LB1LF_1RE1LC_1LC0RB_0LA---/lean/check.sh
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB1LC_1LC0RF_0LF1LD_0LE---_1RF1LC_1LE0RA`](../1RB1LC_1LC0RF_0LF1LD_0LE---_1RF1LC_1LE0RA/README.md): rename A→E, B→F, C→C, D→A, E→B, F→D; it is this table started in state D
- [`1RB0LC_1LA1RE_1LD1RE_1RE0LA_0RA1RF_0RB---`](../1RB0LC_1LA1RE_1LD1RE_1RE0LA_0RA1RF_0RB---/README.md): rename A→B, B→A, C→E, D→C, E→D, F→F and exchange left and right; it is this table started in state B, in a mirror

<!-- end of related machines -->
