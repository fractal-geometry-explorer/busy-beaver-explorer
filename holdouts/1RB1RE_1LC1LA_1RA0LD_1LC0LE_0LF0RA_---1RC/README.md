# 1RB1RE_1LC1LA_1RA0LD_1LC0LE_0LF0RA_---1RC

bbchallenge id 132695. One of the six-state holdouts whose halting from blank tape is open. (group G07).
Family: **counter that overflows at the left end**. Decision: **open**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RE |
| B | 1LC | 1LA |
| C | 1RA | 0LD |
| D | 1LC | 0LE |
| E | 0LF | 0RA |
| F | --- | 1RC |

## What it does

Read the tape as runs of 1s separated by single 0s, left to right; `u` is a run of length 1 (cells `10`).
The tape is `P C u^N`: a short prefix P, a **counter region** C of short odd runs, and a block of N units that
grows by one at every visit of the right end in state A. Between two such visits the head walks left across the
units into C, rewrites it a little near its right edge, and walks back. The rewrites are carries:

    (1, 3) -> (5)          every other visit
    (3, 3) -> (7)          every 4th
    (3, 1, 5) -> (7, 3)    every 8th
    (7, 3) -> (11)         every 8th
    ...                    the k-th deepest kind every 2^k-th visit

(counts over the first 8,000 visits, `c/tok.c` and direct runs), so C behaves like a **binary counter** of the visits,
written with odd runs; its width stays fixed while it counts (123 cells from step ~10^4 to 5·10^11).

When the counter **overflows**, the carry runs all the way to the left end of the tape, where the head arrives in
state D (D0 -> 1LC, C0 -> 1RA: it bounces back). This has happened eight times, at steps 3, 28, 91, 309, 450, 1,252,
7,545 and **506,587,790,058**. The last overflow also rewrote the 410,921 units into a new, much wider counter region
(the tape went from about 0.8·10^6 cells of mostly units to 273,969 run-length tokens of short runs), so the next
overflow is far away: in the old counter the carry depth grew by about 7 cells per doubling of the visits, so a
region of ~8·10^5 cells needs on the order of 2^(10^5) visits.

## Where it can halt

The halting transition is F0, reached only as E0 -> 0LF. A closed tape language from windows of 4 cells
(`lean/EdgeCert.lean`, checked in `lean/Edge.lean`) proves that **it halts from blank tape exactly when F reads a 0
with only blank tape to its left** (`halts_iff_edge`), i.e. when the head comes off the left end in state E instead
of D. The head reaches the left end only at an overflow of the counter, so each overflow is one chance to halt; the
eight seen so far arrived in D.

## Status

Open.

- **Kernel:** `step_none_iff`, `blank_runs_kernel` (`lean/Blank.lean`); `halts_iff_edge` (`lean/Edge.lean`, the
  left-side version of the shared CTL halting lemma, proved there). **native_decide:** `blank_runs_native` (10^7 steps).
- **Trusted computation:** `c/tok.c`, an exact run-length simulator (it agrees with `tools/c/tmrun.c` on the number
  of 1s at step 10,000,208,949), runs 10^16 steps: 5.8·10^7 visits of the right end, no halt; the head reads a 0 with
  only blank tape to its left only at the eight overflows above, each time in state D.
- **Heuristic:** the counter picture (carry frequencies halving, fixed width between overflows). The next overflow,
  the next chance to halt, is estimated at ~2^(10^5) visits (~10^(6·10^4) steps), far beyond any simulation.
- **Open:** whether the head ever leaves the left end in state E. That needs the counter's encoding (which runs
  stand for which binary digits) and what an overflow does to the prefix.

## Third pass: the epoch after the overflow at step 7,545

Written as runs of 1s (single 0s between them; `u` = a run of length 1 at the right end), the visits of the right
end in state A after the overflow at step 7,545 read

    4 1 5 1 1 1 1 1 3 1 1 1 1 5  (1,3)^k  ACTIVE  u^N

with a fixed 14-run prefix, a reservoir of k copies of the pair (1,3) made by the overflow from the old units, and an
active counter region that grows leftwards into the reservoir (k = 14 at visit 56; 10, 5, 4, 4, 2, 1, 1, 0 at visits
2^6 .. 2^13). After the reservoir is used up the active region keeps one growing long run (21, 25, 27, 31, 33 at
visits 2^12 .. 2^16), so its carries get slower; the next overflow came at step 506,587,790,058. The active region
counts with odd runs and carries like `(1,3) -> 5`, `(3,1,5) -> (7,3)`, `(7,3) -> 11`, `(9,3) -> 13`, `(15,3) -> 19` (the full run lists
are printed by a run-length dump of each visit, e.g. `./tok ... A R 1`). This is a more intricate numeral system than
a fixed-width binary counter (the run lengths themselves grow), and it was not decoded in this pass.

## Next steps

Decode the active region of the epoch after step 7,545 first (it is small: about 80 cells, 2^16 visits up to step
1.3*10^10), as a rewriting system on run lengths; then check that it explains the overflow at 5*10^11 and the shape of
the counter region it left behind. Then decode the counter: find the value V(C) with V' = V + 1 at each visit (the carry rules above suggest one), then
compute the configuration at the next overflow symbolically and see whether the head arrives in E.

## Pages

- [`pages/holdouts/1RB1RE_1LC1LA_1RA0LD_1LC0LE_0LF0RA_---1RC/explainer.html`](../../pages/holdouts/1RB1RE_1LC1LA_1RA0LD_1LC0LE_0LF0RA_---1RC/explainer.html)
- [`pages/holdouts/1RB1RE_1LC1LA_1RA0LD_1LC0LE_0LF0RA_---1RC/proof-status.html`](../../pages/holdouts/1RB1RE_1LC1LA_1RA0LD_1LC0LE_0LF0RA_---1RC/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RE_1LC1LA_1RA0LD_1LC0LE_0LF0RA_---1RC/lean/check.sh
(cd tools/py && python3 -m bbtools.ctl 1RB1RE_1LC1LA_1RA0LD_1LC0LE_0LF0RA_---1RC 4 lean H132695 Blank) | diff - holdouts/1RB1RE_1LC1LA_1RA0LD_1LC0LE_0LF0RA_---1RC/lean/EdgeCert.lean
gcc -O2 -o tok holdouts/1RB1RE_1LC1LA_1RA0LD_1LC0LE_0LF0RA_---1RC/c/tok.c
./tok 1RB1RE_1LC1LA_1RA0LD_1LC0LE_0LF0RA_---1RC 1e16 A R 100000      # the tape every 10^5 visits of the right end, ~3 min
./tok 1RB1RE_1LC1LA_1RA0LD_1LC0LE_0LF0RA_---1RC 1e16 D L 1           # every time D reads a 0 with only blank to its left (the overflows)
```
