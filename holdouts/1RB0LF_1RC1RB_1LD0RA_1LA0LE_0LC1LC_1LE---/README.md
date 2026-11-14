# 1RB0LF_1RC1RB_1LD0RA_1LA0LE_0LC1LC_1LE---

bbchallenge id 12600. A BB(6) holdout, group G10 (one side of the tape grows like the square root of the step count, the other more slowly). Analysed by hand from the generated folder.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LF |
| B | 1RC | 1RB |
| C | 1LD | 0RA |
| D | 1LA | 0LE |
| E | 0LC | 1LC |
| F | 1LE | --- |

## What it does

**One background, two forms.** After a sweep to the right the tape repeats `0111`; a sweep to the left turns
each `01110111` into `01001111`, and the next rightward sweep turns it back. The four shift rules of these sweeps
are proved (`lean/Rules.lean`).

**A few defects.** Two consecutive end turns:

```
step 394,721,780  right end  (1110)^3460 1^8 0 1^3 0 1^6 (0111)^200 1^17 (0111)^1206 110 1^3 0 1^7 0 1^3 0 1^6 (0111)^74 (1110)^3 1100
step 394,821,133  left end   0 (01001111)^1731 1^5 0100 1^7 (01001111)^100 1^17 (01001111)^603 110100 1^8 0100 1^7 (01001111)^36 ...
```

Four to six short defects (`1^8 0 1^3 0 1^6`, `1^17`, ...) separate long, uneven domains (3460, 200, 1206, 74 copies
here; 1676, 6498, 10, 552, 1018 at step 1.5·10^9). At the left end a block `1^N` grows by about one cell per sweep
while the domain next to it shrinks.

## Halting

F1 is the only halting transition, reached as `1 A>1`. It cannot happen inside a domain; whether a defect ever
produces it is open.

## What is proved

- `lean/Blank.lean` (generated): the halting configurations; no halt in 10^4 steps (kernel) and 10^7 (`native_decide`).
- `lean/Rules.lean` (from `py/rules.py`, kernel): the four sweep rules over the background (`b_right`, `c_right`, `d_left`, `c_left`).
- Computed (`tools/c/triage.c`): no halt in 10^9 steps.

Everything else on this page is heuristic: read off runs of up to 2·10^9 steps (`tools/c/tokrun.c`), not proved.

## For later

- Write each defect type as a rule for a full sweep (in both directions), to see how far it moves and how it changes
  the domains next to it; with that the run could be accelerated far beyond 10^9 steps.

## Reproduce

```sh
python3 holdouts/1RB0LF_1RC1RB_1LD0RA_1LA0LE_0LC1LC_1LE---/py/rules.py | diff - holdouts/1RB0LF_1RC1RB_1LD0RA_1LA0LE_0LC1LC_1LE---/lean/Rules.lean   # the rules file is current
gcc -O2 -o tokrun tools/c/tokrun.c
./tokrun 1RB0LF_1RC1RB_1LD0RA_1LA0LE_0LC1LC_1LE--- 400000000 x=0 LR 2000 | tail -4   # the tape each time the head extends it (x is a 0)
```

## Deciders tried (F11, 13 November 2026)

None closes. Each reaches a halting configuration in its abstraction, which says nothing about halting.

- n-gram CPS (`tools/c/ngramcps.c`), equal widths on both sides: a halting local configuration is reached with plain up to width 22, history 1 up to width 22, history 2 up to width 20, history 3 up to width 18, LRU history up to width 3 (larger widths ran out of the 150 s or 60 million configuration budget).
- n-gram CPS with every cell tagged by its position mod p: fails for p = 2 up to width 16, p = 3 up to width 16, p = 4 up to width 16, p = 6 up to width 16.
- n-gram CPS where each side also carries the state of a small automaton that has read that side from the far end (every automaton with up to 3 states on both sides, or 4 states on one side), with position mod 1..4 and widths 4, 6, 8: no closed set without a halt in all 120 parameter sets.
- Run-length windows (the K nearest runs of equal macro cells on each side, run lengths kept exactly below T and mod M above): fails for all 72 parameter sets (cells of 1 to 4 bits, K = 2, 4, 6, T = 2, 4, M = 1, 2, 4).
- Two-automaton closed tape language by SAT (a deterministic automaton reading each side inward, n states each, CaDiCaL): no solution for n = 2..7; n = 8 not finished in 150 s.

## Where a halt can come from

`lean/Route.lean` (kernel, written by `py/route.py`): `halt_route`, two steps before any halt the machine is in one
of: D with 1 two left, 1 left, 0 under the head.

## Pages

- [`pages/holdouts/1RB0LF_1RC1RB_1LD0RA_1LA0LE_0LC1LC_1LE---/explainer.html`](../../pages/holdouts/1RB0LF_1RC1RB_1LD0RA_1LA0LE_0LC1LC_1LE---/explainer.html)
- [`pages/holdouts/1RB0LF_1RC1RB_1LD0RA_1LA0LE_0LC1LC_1LE---/proof-status.html`](../../pages/holdouts/1RB0LF_1RC1RB_1LD0RA_1LA0LE_0LC1LC_1LE---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LF_1RC1RB_1LD0RA_1LA0LE_0LC1LC_1LE---/lean/check.sh
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB1RA_1LC0RE_1LE0LD_0LB1LB_1RA0LF_1LD---`](../1RB1RA_1LC0RE_1LE0LD_0LB1LB_1RA0LF_1LD---/README.md): rename A→E, B→A, C→B, D→C, E→D, F→F; it is this table started in state B
- [`1RB---_0RC1RC_1RD0LE_1RE0RB_1LF0RA_1LC1LF`](../1RB---_0RC1RC_1RD0LE_1RE0RB_1LF0RA_1LC1LF/README.md): rename A→E, B→F, C→C, D→D, E→B, F→A and exchange left and right; it is this table started in state F, in a mirror

<!-- end of related machines -->
