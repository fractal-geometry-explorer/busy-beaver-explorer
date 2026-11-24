# 1RB1LD_0RC0RF_1LC0LA_0LE1LD_1LA---_0RB0LF

bbchallenge id 68273. An abacus of a few blocks of 1s: each sweep right deals a block out a third to the left and two thirds to the right, re-dealing while the remainder is 1 (a base-3 cascade); the block lengths evolve chaotically.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LD |
| B | 0RC | 0RF |
| C | 1LC | 0LA |
| D | 0LE | 1LD |
| E | 1LA | --- |
| F | 0RB | 0LF |

## What it does

The tape is a few blocks of 1s. At the right end (head in state C) the blocks are separated by `00`, with at most
one `00000`; at the left end (head in state D) every separator is a single 0 and a short block `2` sits at the far
right. A *pass* is a sweep left and a sweep right.

**The sweep left** adds one to every block but the last long one, closes the separators to single 0s, and cuts
the block after a `00000` (always a multiple of 3, n = 3t) into t + 1 and 2t + 2:

    R  14 . 345 ___ 693 _ 1          (. = 00, ___ = 00000, _ = 0)
    L  15 _ 346 _ 232 _ 464 _ 2
    R  123 . 161 . 261 . 526 _ 1     ->   L  124 _ 162 _ 262 _ 526 _ 2

**The sweep right deals the blocks out, a third to the left and two thirds to the right.** The tape near the head
is `1^(k+1) 000 F> 1^n 0 1^m`: a finished block, the block being dealt and the next block. One *deal* takes three
ones from the dealt block, gives one to the finished block and two to the next one (Lean: `deal`, 4n + 23 steps;
`deals` does j of them at once, by induction). Inside a deal a single 0 travels right through the block, three
steps a cell (`c_shift`). When fewer than three ones are left, the remainder decides:

- **remainder 1**: the finished block is dealt again: `116 000 F> 1 0 930` becomes `1 000 F> 115 0 932`, so the
  block is cut by 3 again (n -> about n/3), as long as the remainder stays 1;
- **remainder 2**: the finished block is closed (it keeps a `00` separator) and the next block is dealt;
- **remainder 0**: the separator disappears and the two blocks merge.

So a block is divided by 3 over and over while the remainder is 1: a base-3 cascade, the ternary counterpart of
the 2-adic halving of its F10 sibling 1RB1RD_0RC0RD_0LD1LE_1LC0RB_1LF---_1LA0LE. For example the left block 348 of
`348 _ 700 _ 2` is dealt as 346, then 115, then 38 (remainders 1, 1, 2) and ends as 14; the rest goes right,
700 -> 1034. The sweep ends at the right with a final 1, the last separator sometimes `00000`:

    12,164,477   2 . 13 . 1009
    12,902,116   347 . 700
    13,724,275   14 . 345 ___ 693
    14,048,610   14 . 345 . 231 . 464
    14,720,069   123 . 161 . 261 . 526

The counts of the remainder cases have not been put together into an exact pass map yet; the lengths look chaotic
because the number of re-deals is a base-3 valuation. The ones grow slowly (6,891 at 3e9 steps).

## Status

Open. Kernel: the halting configurations, no halt in 10^4 steps (10^7 native), the travelling-0 rule `c_shift`,
the deal `deal` and j deals at once (`Deal.lean`, `deals`). Halting needs E to read a 1. CTL (K = 2..5) and
NGramCPS (widths 2-8, -H, -U) fail.

## For later

Write the exact pass map from the three remainder cases (as was done for the sibling, whose map is
`py/passmap.py` there), check it against the simulator, and look for the analogue of the sibling's restarts: the
sibling halts only through a restart whose buffer is 2 mod 3, and this machine's halting transition E1 is likely
reached the same way, when a cascade runs out of room.

## Reproduce

```sh
./tmrun 1RB1LD_0RC0RF_1LC0LA_0LE1LD_1LA---_0RB0LF 3000000000 at C R 100000
. /etc/profile.d/lean.sh && holdouts/1RB1LD_0RC0RF_1LC0LA_0LE1LD_1LA---_0RB0LF/lean/check.sh
python3 holdouts/1RB1LD_0RC0RF_1LC0LA_0LE1LD_1LA---_0RB0LF/lean/rules.py > /tmp/Rules.lean   # regenerates Rules.lean
```

## Pages

- [`pages/holdouts/1RB1LD_0RC0RF_1LC0LA_0LE1LD_1LA---_0RB0LF/explainer.html`](../../pages/holdouts/1RB1LD_0RC0RF_1LC0LA_0LE1LD_1LA---_0RB0LF/explainer.html)
- [`pages/holdouts/1RB1LD_0RC0RF_1LC0LA_0LE1LD_1LA---_0RB0LF/proof-status.html`](../../pages/holdouts/1RB1LD_0RC0RF_1LC0LA_0LE1LD_1LA---_0RB0LF/proof-status.html)

## Accelerated run

Trusted computation: `tools/c/rleaccel.cpp` (compiled port of `tools/py/bbtools/rleaccel.py`, checked against it by
`tools/tests/test_rleaccel_cpp.py`), blocks of 6, runs from blank tape without a halt to 2.89·10^14 machine steps (exact; tape:
346,326 cells). It ran about 30 minutes, resumed from a checkpoint after interruptions, so its macro count
(16,560,000,000) differs from an uninterrupted run's. Command: `g++ -O2 -o rleaccel tools/c/rleaccel.cpp && timeout 1800 ./rleaccel 1RB1LD_0RC0RF_1LC0LA_0LE1LD_1LA---_0RB0LF 6 1000000000000000 run.ck 300`.
