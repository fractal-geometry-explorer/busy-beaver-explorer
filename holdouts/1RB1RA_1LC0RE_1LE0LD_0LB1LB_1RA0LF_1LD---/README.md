# 1RB1RA_1LC0RE_1LE0LD_0LB1LB_1RA0LF_1LD---

bbchallenge id 152108. Halting from blank tape is open. The tape is a few large blocks of `1110` separated by short defects, rewritten as `10011110` by the sweeps.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RA |
| B | 1LC | 0RE |
| C | 1LE | 0LD |
| D | 0LB | 1LB |
| E | 1RA | 0LF |
| F | 1LD | --- |

## What it does

With `u = 1110` and `w = 10011110`, at step 4,797,529,835 (head in E at the right end) the tape is

    u^3608 1^5 u^2 1^3 u^11238 1^3 u^2 1^2 u^2 1^2 0 u^1167 1^7 u^2 1^374 u^4 1^6 u^526 1^8 u^2 1 u^2 1^3 u^783 1^2 0 u^3 1^2 0^2 E>

and at the next left extension the same blocks read `w^1804 ... w^5618 ... w^583 ...` (the sweeps rewrite the tape
eight cells at a time; those sweeps are the Lean rules). The large blocks change irregularly: 888, 1502, 22, 120, 286 at step
1.25·10^8; 2000, 5064, 646, 983 at 1.36·10^9. The width grows like sqrt(t) (19,664 at step 3.95·10^8, 69,788 at
4.80·10^9).

## What is proved

- Lean, kernel (`lean/Rules.lean`, from `py/rules.py`): the sweep rules

    L A> (1)^n R -> L (1)^n A> R
    L A> (01001111)^n R -> L (01110111)^n A> R
    L A> (10100111)^n R -> L (10111011)^n A> R
    L (10100111)^n B> 0 R -> L B> 0 (01001111)^n R
    L A> (11010011)^n R -> L (11011101)^n A> R
    L (11010011)^n C> 1 R -> L C> 1 (10100111)^n R
    L (11101001)^n D> 10 R -> L D> 10 (10100111)^n R
    L 10 E> (00111101)^n R -> L (01110111)^n 10 E> R

- Lean (`lean/Blank.lean`, generated): the halting configurations, no halt in 10^4 / 10^7 steps.

Everything under "What it does" is observation from simulation, not proof.

## Open

Halting. How a round trip changes the blocks and defects is not known.

## For later

- Follow one round trip at the level of blocks and defects, and look for the defect that carries information.

## Reproduce

```sh
tools/c/tokrun 1RB1RA_1LC0RE_1LE0LD_0LB1LB_1RA0LF_1LD--- 6000000000 w=10011110,u=1110 LR 100000
python3 holdouts/1RB1RA_1LC0RE_1LE0LD_0LB1LB_1RA0LF_1LD---/py/rules.py > holdouts/1RB1RA_1LC0RE_1LE0LD_0LB1LB_1RA0LF_1LD---/lean/Rules.lean
. /etc/profile.d/lean.sh && holdouts/1RB1RA_1LC0RE_1LE0LD_0LB1LB_1RA0LF_1LD---/lean/check.sh
```

## Deciders tried (F11, 13 November 2026)

None closes. Each reaches a halting configuration in its abstraction, which says nothing about halting.

- n-gram CPS (`tools/c/ngramcps.c`), equal widths on both sides: a halting local configuration is reached with plain up to width 22, history 1 up to width 20, history 2 up to width 20, history 3 up to width 18, LRU history up to width 4 (larger widths ran out of the 150 s or 60 million configuration budget).
- n-gram CPS with every cell tagged by its position mod p: fails for p = 2 up to width 20, p = 3 up to width 16, p = 4 up to width 16, p = 6 up to width 16.
- n-gram CPS where each side also carries the state of a small automaton that has read that side from the far end (every automaton with up to 3 states on both sides, or 4 states on one side), with position mod 1..4 and widths 4, 6, 8: no closed set without a halt in all 120 parameter sets.
- Run-length windows (the K nearest runs of equal macro cells on each side, run lengths kept exactly below T and mod M above): fails for all 72 parameter sets (cells of 1 to 4 bits, K = 2, 4, 6, T = 2, 4, M = 1, 2, 4).
- Two-automaton closed tape language by SAT (a deterministic automaton reading each side inward, n states each, CaDiCaL): no solution for n = 2..7; n = 8 not finished in 150 s.

## Where a halt can come from

`lean/Route.lean` (kernel, written by `py/route.py`): `halt_route`, two steps before any halt the machine is in one
of: C with 1 two left, 1 left, 0 under the head.

## Pages

- [`pages/holdouts/1RB1RA_1LC0RE_1LE0LD_0LB1LB_1RA0LF_1LD---/explainer.html`](../../pages/holdouts/1RB1RA_1LC0RE_1LE0LD_0LB1LB_1RA0LF_1LD---/explainer.html)
- [`pages/holdouts/1RB1RA_1LC0RE_1LE0LD_0LB1LB_1RA0LF_1LD---/proof-status.html`](../../pages/holdouts/1RB1RA_1LC0RE_1LE0LD_0LB1LB_1RA0LF_1LD---/proof-status.html)

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0LF_1RC1RB_1LD0RA_1LA0LE_0LC1LC_1LE---`](../1RB0LF_1RC1RB_1LD0RA_1LA0LE_0LC1LC_1LE---/README.md): rename A→B, B→C, C→D, D→E, E→A, F→F; it is this table started in state E
- [`1RB---_0RC1RC_1RD0LE_1RE0RB_1LF0RA_1LC1LF`](../1RB---_0RC1RC_1RD0LE_1RE0RB_1LF0RA_1LC1LF/README.md): rename A→F, B→C, C→D, D→B, E→E, F→A and exchange left and right; it is this table started in state F, in a mirror

<!-- end of related machines -->
