# 1RB0LE_1RC1RB_1RD0RA_0RE---_1LF1LA_1LA1LF

bbchallenge id 58953. One of the six-state holdouts whose halting from blank tape is open.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LE |
| B | 1RC | 1RB |
| C | 1RD | 0RA |
| D | 0RE | --- |
| E | 1LF | 1LA |
| F | 1LA | 1LF |

## What it does

**Sample point**: the head in A at the left end. The tape is then a list of blocks `1^k 0` with k odd and **every 0
single**: k = 1 mod 4 in the left part, k = 1 or 3 mod 4 further right. Example at step 100,542 (each block as its k):

    9 1 5 1 1 1 9 1 5 1 9 1 5 1 1 1 21 1 1 1 5 1 5 1 1 1 1 1 1 1 17 1 1 1 5 1 1 1 1 1 1 1 5 7 1 3 1 5 1 5 1 5 15 ...

**Sweeps**: a bouncer. Leftward, F runs over 1s; at a 0 it fills it and A/E turn each `11` into `01` until the next 0.
Rightward, B runs over 1s and A/B/C turn `0101` into `1110`. Each sweep rewrites the blocks from their neighbours,
like one step of a cellular automaton: the space-time diagram is full of nested (Sierpinski-like) triangles. Most
sweeps turn back inside the left part; the right part stays frozen until a rare deep sweep reaches the right end (steps
1.9·10^6, 6.4·10^6, 1.9·10^7, 6.1·10^7, 1.9·10^8, 5.8·10^8: about 3.1 times apart, the logarithmic side). The depth of
the sweeps behaves like the carries of a counter. No exact macro rule is known: the block values look chaotic.

**Halting**: D on a 1 is the only halt; D comes only from C on a 0, C only from B on a 0. So it halts iff B meets
`0 0 1`: a double zero inside the tape. In 10^9 steps B read a 0 followed by another 0 only 42 times, all at the blank
right end; the closest call was `B> 0 1 0 0` (6 times).

## Status

Open.

- **Lean, kernel** (`lean/Rules.lean`, from `py/rules.py`): `b_run`, `f_run`, `e_run`, `a_run` (the sweep rules),
  `halt_shape` (`B> 0 0 1` reaches D on a 1 in 2 steps), `halt_after_shape`. `lean/Blank.lean`: no halt in 10^7 steps.
- **Trusted**: no halt in 10^9 steps (triage); the double-zero count (`c/nbhd.c`). Twin: the right-end tapes are identical to those of
  1RB0LF_1RC1RB_1RD0RA_1RE0RE_1LF---_0LD1LA, which takes 1.5 times as many steps (`c/tok.c`, observed).
- **Heuristic**: the sweep picture, frozen right part, deep sweeps 3.1 times apart (`c/samples.c`).
- **Computed, negative**: `bbtools.ctl` K = 2..6 closes but allows halts (its right automaton doubles with K); n-gram
  CPS widths 3..7 fail.

## Notes for later

- The natural conjecture is "every 0 inside the tape stays single". It would prove non-halting. It is not a regular
  invariant at window size 6; it may need the block values mod 4 (left part 1 mod 4) and the counter-like depth.
- Find the exact one-sweep map on the list of block values (a CA rule on k mod 4?).

## Reproduce

```sh
gcc -O2 -o samples holdouts/1RB0LE_1RC1RB_1RD0RA_0RE---_1LF1LA_1LA1LF/c/samples.c && ./samples 1RB0LE_1RC1RB_1RD0RA_0RE---_1LF1LA_1LA1LF 200000 A L 100000 3
gcc -O2 -o nbhd holdouts/1RB0LE_1RC1RB_1RD0RA_0RE---_1LF1LA_1LA1LF/c/nbhd.c && ./nbhd 1RB0LE_1RC1RB_1RD0RA_0RE---_1LF1LA_1LA1LF 1000000000 B 0
python3 holdouts/1RB0LE_1RC1RB_1RD0RA_0RE---_1LF1LA_1LA1LF/py/rules.py > holdouts/1RB0LE_1RC1RB_1RD0RA_0RE---_1LF1LA_1LA1LF/lean/Rules.lean
```

## Deciders tried (F11, 13 November 2026)

None closes. Each reaches a halting configuration in its abstraction, which says nothing about halting.

- n-gram CPS (`tools/c/ngramcps.c`), equal widths on both sides: a halting local configuration is reached with plain up to width 24, history 1 up to width 24, history 2 up to width 24, history 3 up to width 24, LRU history up to width 4 (larger widths ran out of the 150 s or 60 million configuration budget).
- n-gram CPS with every cell tagged by its position mod p: fails for p = 2 up to width 20, p = 3 up to width 20, p = 4 up to width 20, p = 6 up to width 20.
- n-gram CPS where each side also carries the state of a small automaton that has read that side from the far end (every automaton with up to 3 states on both sides, or 4 states on one side), with position mod 1..4 and widths 4, 6, 8: no closed set without a halt in all 120 parameter sets.
- Run-length windows (the K nearest runs of equal macro cells on each side, run lengths kept exactly below T and mod M above): fails for all 72 parameter sets (cells of 1 to 4 bits, K = 2, 4, 6, T = 2, 4, M = 1, 2, 4).
- Two-automaton closed tape language by SAT (a deterministic automaton reading each side inward, n states each, CaDiCaL): no solution for n = 2..8; n = 9 not finished in 150 s.

## Where a halt can come from

`lean/Route.lean` (kernel, written by `py/route.py`): `halt_route`, two steps before any halt the machine is in one
of: B with 0 under the head, 0 right, 1 two right.

## Pages

- [`pages/holdouts/1RB0LE_1RC1RB_1RD0RA_0RE---_1LF1LA_1LA1LF/explainer.html`](../../pages/holdouts/1RB0LE_1RC1RB_1RD0RA_0RE---_1LF1LA_1LA1LF/explainer.html)
- [`pages/holdouts/1RB0LE_1RC1RB_1RD0RA_0RE---_1LF1LA_1LA1LF/proof-status.html`](../../pages/holdouts/1RB0LE_1RC1RB_1RD0RA_0RE---_1LF1LA_1LA1LF/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LE_1RC1RB_1RD0RA_0RE---_1LF1LA_1LA1LF/lean/check.sh
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB1RA_1LC0RF_1LD1LC_1LE0LB_0LF---_1RA1RB`](../1RB1RA_1LC0RF_1LD1LC_1LE0LB_0LF---_1RA1RB/README.md): rename A→B, B→C, C→D, D→E, E→F, F→A and exchange left and right; it is this table started in state F, in a mirror
- [`1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF`](../1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF/README.md): rename A→E, B→F, C→A, D→B, E→C, F→D; it is this table started in state C
- [`1RB1RC_1RC1RB_1LD0RA_1LE1LD_1LF0LC_0LA---`](../1RB1RC_1RC1RB_1LD0RA_1LE1LD_1LF0LC_0LA---/README.md): rename A→C, B→D, C→E, D→F, E→A, F→B and exchange left and right; it is this table started in state E, in a mirror

**Same tapes at another pace (observed, not proved).** Leave the states aside and compare only the tape and the place of the head. Then a large part of the first 10^7 configurations of this machine are configurations of the machines below, in the same order and up to the end of the run. The steps at which they occur differ, the tables are not renamings of each other, and equal tapes with different states may be continued differently, so this does not tie the halting questions together.

- [`1RB0LF_1RC1RB_1RD0RA_1RE0RE_1LF---_0LD1LA`](../1RB0LF_1RC1RB_1RD0RA_1RE0RE_1LF---_0LD1LA/README.md): 4,986,200 configurations, the last at step 6,657,506 here and step 10,000,000 there

<!-- end of related machines -->
