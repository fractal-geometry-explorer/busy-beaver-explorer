# 1RB1RE_1LC1RC_0RF1LD_1LE0LB_1LB0RA_---1RA

bbchallenge id 8805. One of the six-state holdouts whose halting from blank tape is open (group G10). Family: **bouncer over 11110 blocks with travelling defects (chaotic)**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RE |
| B | 1LC | 1RC |
| C | 0RF | 1LD |
| D | 1LE | 0LB |
| E | 1LB | 0RA |
| F | --- | 1RA |

## What it does

The tape reads as runs of the word `c = 11110` with defects `1 b` (= `1110`) and `1 d` (= `1111110`). The defects travel with the sweeps and change; a long run `c^28` shrinks by two words every few sweeps. The left end grows fast (bursts of 1 to 7 cells), the right end slowly (4,604 bursts in 10^9 steps).

```
the tape at the left end (b = 110, c = 11110, d = 111110):
step 32,055  E 0 1 b 1 d 1 d c^4 1 b c^4 1 b c^28 1 b c^3 1^3
step 33,737  B 0^2 b c 1 b c^2 1 b c^5 1 b c^4 1 b c^28 1 b c 1^4
step 42,500  B 0^2 b c 1 b c^4 1 d 1 b 1 d 1 d 1 d 1 d 1 d 1 d c^4 1 b c^4 1 b c^26 1^2
step 43,987  D 0 b^2 d c^2 1 b c^3 1 d 1 d 1 b c^2 1 b c^2 1 b c^4 1 d 1 d c^2 1 d 1 d c^24 1^4
```

## Halting

The only halting transition is F0. Lean (kernel) proves that it fires only with blank tape from the head on: the machine halts iff F reaches the blank region at the right (`lean/Edge.lean`).

## Status

**Open.** Lean (kernel): `lean/Edge.lean` with `lean/EdgeCert.lean` (a closed tape language of windows of 3 cells from `bbtools.ctl`): every halt is in state F with blank tape from the head on (`halt_at_edge`, `halts_iff_edge`), and past the head two 0s in a row occur only in the blank region (`right_no_double_zero`). Plus the generated `lean/Blank.lean`.
Deciders tried without success: `bbtools.ctl` with windows K = 2..6 (no closed language without halts), `ngramcps`
with widths 2..6, plain and with `-H 2`, `-H 3`, `-U`.

## For later

- Look for the defect dynamics on the word `c = 11110`: how defects move per sweep and when they are created,
  possibly as a counter in the lengths of the c-runs.

## Deciders tried (F11, 13 November 2026)

None closes. Each reaches a halting configuration in its abstraction, which says nothing about halting.

- n-gram CPS (`tools/c/ngramcps.c`), equal widths on both sides: a halting local configuration is reached with plain up to width 24, history 1 up to width 24, history 2 up to width 24, history 3 up to width 24, LRU history up to width 10 (larger widths ran out of the 150 s or 60 million configuration budget).
- n-gram CPS with every cell tagged by its position mod p: fails for p = 2 up to width 20, p = 3 up to width 20, p = 4 up to width 20, p = 6 up to width 20.
- n-gram CPS where each side also carries the state of a small automaton that has read that side from the far end (every automaton with up to 3 states on both sides, or 4 states on one side), with position mod 1..4 and widths 4, 6, 8: no closed set without a halt in all 120 parameter sets.
- Run-length windows (the K nearest runs of equal macro cells on each side, run lengths kept exactly below T and mod M above): fails for all 72 parameter sets (cells of 1 to 4 bits, K = 2, 4, 6, T = 2, 4, M = 1, 2, 4).
- Two-automaton closed tape language by SAT (a deterministic automaton reading each side inward, n states each, CaDiCaL): no solution for n = 2..10; n = 11 not finished in 150 s.

## Where a halt can come from

`lean/Route.lean` (kernel, written by `py/route.py`): `halt_route`, two steps before any halt the machine is in one
of: B with 1 under the head, 0 right, 0 two right.

## Pages

- [`pages/holdouts/1RB1RE_1LC1RC_0RF1LD_1LE0LB_1LB0RA_---1RA/explainer.html`](../../pages/holdouts/1RB1RE_1LC1RC_0RF1LD_1LE0LB_1LB0RA_---1RA/explainer.html)
- [`pages/holdouts/1RB1RE_1LC1RC_0RF1LD_1LE0LB_1LB0RA_---1RA/proof-status.html`](../../pages/holdouts/1RB1RE_1LC1RC_0RF1LD_1LE0LB_1LB0RA_---1RA/proof-status.html)
