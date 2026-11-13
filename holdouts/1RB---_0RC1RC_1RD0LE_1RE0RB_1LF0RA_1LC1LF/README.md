# 1RB---_0RC1RC_1RD0LE_1RE0RB_1LF0RA_1LC1LF

bbchallenge id 168752. One of the six-state holdouts whose halting from blank tape is open (group G10). Family: **bouncer over 0111 blocks with a slowly consumed left side (chaotic)**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | --- |
| B | 0RC | 1RC |
| C | 1RD | 0LE |
| D | 1RE | 0RB |
| E | 1LF | 0RA |
| F | 1LC | 1LF |

## What it does

At the left end the tape reads as runs of the word `a = 0111`, solid runs of 1s and short junctions. Each visit to the left end takes two a's from the first run (and the last run grows by four), so between rewrites the left part is a counter; when the first run is used up the junctions merge and new runs form, with no visible pattern. The right end grows by exactly 3 cells per sweep (bursts of 3 new cells every ~2·width steps); the left end moves out 248 times in 10^9 steps, by 2 to 6 cells.

```
the tape at successive visits to the left end (a = 0111):
step 195,355,840  F a 1^4 a^66 1^10 a^4 1^1099 a^2 1^4 a^2 1^5 a^1472 1^3 a^2 1^5 a^1540
step 195,568,274  F a 1^4 a^64 1^10 a^4 1^1099 a^2 1^4 a^2 1^5 a^1472 1^3 a^2 1^5 a^1544
step 195,780,828  F a 1^4 a^62 1^10 a^4 1^1099 a^2 1^4 a^2 1^5 a^1472 1^3 a^2 1^5 a^1548
```

## Halting

The machine halts on A reading 1 (A1 undefined). `bbtools.ctl` finds closed tape languages (windows of 2 to 6 cells) that cover the run but still allow halts, with only a local constraint near the head: at K = 6 the cells left of the head read (outward) `011001`, `011010`, `011101` or `011110`. Nothing confines a halt to an edge.

## Status

**Open.** Lean: only the generated `lean/Blank.lean` (halting configurations; no halt in 10^4 steps by the kernel, 10^7 by `native_decide`).
Deciders tried without success: `bbtools.ctl` with windows K = 2..6 (no closed language without halts), `ngramcps`
with widths 2..6, plain and with `-H 2`, `-H 3`, `-U`.

## For later

- Find the rewrite rules at the left end as maps on the block list (run lengths of `a` and of `1`), as was done
  for 1RB1RF_1LC0LB; the per-visit rule (two a's off the first run) is the place to start, with `bbtools.cycles` at
  sample points at the left end.

## Deciders tried (F11, 13 November 2026)

None closes. Each reaches a halting configuration in its abstraction, which says nothing about halting.

- n-gram CPS (`tools/c/ngramcps.c`), equal widths on both sides: a halting local configuration is reached with plain up to width 22, history 1 up to width 20, history 2 up to width 20, history 3 up to width 18, LRU history up to width 3 (larger widths ran out of the 150 s or 60 million configuration budget).
- n-gram CPS with every cell tagged by its position mod p: fails for p = 2 up to width 20, p = 3 up to width 20, p = 4 up to width 16, p = 6 up to width 16.
- n-gram CPS where each side also carries the state of a small automaton that has read that side from the far end (every automaton with up to 3 states on both sides, or 4 states on one side), with position mod 1..4 and widths 4, 6, 8: no closed set without a halt in all 120 parameter sets.
- Run-length windows (the K nearest runs of equal macro cells on each side, run lengths kept exactly below T and mod M above): fails for all 72 parameter sets (cells of 1 to 4 bits, K = 2, 4, 6, T = 2, 4, M = 1, 2, 4).
- Two-automaton closed tape language by SAT (a deterministic automaton reading each side inward, n states each, CaDiCaL): no solution for n = 2..8; n = 9 not finished in 150 s.

## Where a halt can come from

`lean/Route.lean` (kernel, written by `py/route.py`): `halt_route`, two steps before any halt the machine is in one
of: D with 0 under the head, 1 right, 1 two right.

## Pages

- [`pages/holdouts/1RB---_0RC1RC_1RD0LE_1RE0RB_1LF0RA_1LC1LF/explainer.html`](../../pages/holdouts/1RB---_0RC1RC_1RD0LE_1RE0RB_1LF0RA_1LC1LF/explainer.html)
- [`pages/holdouts/1RB---_0RC1RC_1RD0LE_1RE0RB_1LF0RA_1LC1LF/proof-status.html`](../../pages/holdouts/1RB---_0RC1RC_1RD0LE_1RE0RB_1LF0RA_1LC1LF/proof-status.html)

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0LF_1RC1RB_1LD0RA_1LA0LE_0LC1LC_1LE---`](../1RB0LF_1RC1RB_1LD0RA_1LA0LE_0LC1LC_1LE---/README.md): rename A→F, B→E, C→C, D→D, E→A, F→B and exchange left and right; it is this table started in state E, in a mirror
- [`1RB1RA_1LC0RE_1LE0LD_0LB1LB_1RA0LF_1LD---`](../1RB1RA_1LC0RE_1LE0LD_0LB1LB_1RA0LF_1LD---/README.md): rename A→F, B→D, C→B, D→C, E→E, F→A and exchange left and right; it is this table started in state F, in a mirror

<!-- end of related machines -->
