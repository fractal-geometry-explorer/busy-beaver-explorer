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

The lengths look chaotic because the number of re-deals is a base-3 valuation. The ones grow slowly (6,891 at
3e9 steps).

## The event map (26 November 2026)

**Proved in Lean** (`lean/EventMap.lean`, `visit_sound`; see "The map in Lean" below), after being computed and
checked against the machine. `py/passmap.py` is the map; `c/events.c`, `c/onestep.c` and `c/passrun.c` are the
tools around it.

**States.** Stop the machine each time the head, in state D, stands on the blank cell left of every 1. The tape is
then a list of blocks of 1s with single 0s between them: `L [l0, l1, ..., lk]`. From blank tape the map starts at
`L [7, 2]`, step 66. There are only 2,412 such visits and right-end turns in the first 3·10^9 steps.

**One left-end visit.** Read the list from the left with a running value `cur`, first `cur = l0`, and write
`cur = 3j + r`. Blocks past the end of the list count as 0.

| remainder | what happens | the list becomes |
|---|---|---|
| r = 1 | the block keeps j + 1, the next block gets 2j and is dealt in turn | `..., j + 1,` then go on with `cur = l(i+1) + 2j` |
| r = 2 | the block keeps j − 1 and the visit ends | `..., j − 1, l(i+1) + 2j + 5, rest` |
| r = 0 | the block keeps j, the block after next gets 2, the visit ends | `..., j, l(i+1) + 2j, l(i+2) + 2, rest` |

At the end the first block of the new list gets one more. If that makes it 0 (the list began with a 2), the block
vanishes and the block after next gets 2 more: `[2, b, c, ...]` becomes `[b + 5, c + 2, ...]`. Example:
`[16, 77, 91, 182, 2]` becomes `[7, 29, 149, 184, 2]`: 16 = 3·5 + 1 keeps 6, and one more at the end; 77 + 10 = 87
= 3·29 keeps 29; 91 + 58 = 149; 182 + 2. This is `visit` in `py/passmap.py`.

When the dealing runs past the last block, the head turns at the right end of the tape, once or several times in a
row, and new blocks appear there; `step` in `py/passmap.py` follows these turns one by one (states `Ri` and
`Riii`). The outcome is the same three rules with 0 for the missing blocks: `[100, 123]` becomes `[35, 63, 126, 2]`.

**Checks.** The map gives every one of the 2,406 events of the first 3·10^9 steps from step 66 on
(`passmap.py check`). Of every list of 2 to 5 blocks below 10 and 60,000 random lists (126,420 lists), 118,645 are
inside the map's domain and all agree with the machine, turn by turn and as one `visit` (`passmap.py test`); the
other 7,775 are outside it.

**The map in Lean.** `lean/EventMap.lean` defines `visit` (the table above, blocks past the end counting as 0;
`none` when a value after the first is 2, 3 or 5) and proves, by Lean's kernel alone:

- `visit_sound`: if `visit l = some l'`, the machine goes from the left end with blocks `l` to the left end with
  blocks `l'`, in one step or more;
- `start`: from blank tape the machine is at `[7, 2]` after 66 steps;
- `not_halts_of_run`: if the map can be applied for ever from `[7, 2]`, the machine does not halt;
- `visitHalts_sound`, `halts_of_reach`: when the dealing meets a later value 5 (`[4, 3, ...]`, `[7, 1, ...]`,
  `[1, 5, ...]`, `[4, 2, 3, ...]`), the machine halts: the head comes back in state E onto a 1. So if the map from
  `[7, 2]` reaches such a list, the machine halts from blank tape.

The proof follows the machine through three kinds of configuration: dealing (`1^(k+1) 000 F> 1^n 0 1^m`, with
`deals`), between two blocks (`0000 1^c 0 C>`, the block being entered had c + 2 ones) and on the way back
(`D> 0` with the finished blocks, each `0 1^a 0`, to the left). `lean/rules.py` generates the 21 rule statements
between them (each remainder, the vanishing first block, the way back, the halt at 5), some in several versions
for small blocks; the hand-written part chains them and does the arithmetic. `passmap.py lean` compares the Lean
definition with `visit` on the 126,420 test lists: they agree on all 118,645 inside the domain and both give no
answer on the rest.

**The domain, and where the machine halts.** The rules need room. The map answers only if no value `cur` after the
first is 1, 2, 3 or 5, and the value at the last block, if the dealing gets there, is not 4 or 7 either. From lists
outside this domain the machine was run directly (`passmap.py off`, 8,569 lists):

| the first bad value | what the machine does |
|---|---|
| a later `cur` = 5 | halts, every time (3,777 lists); proved in Lean (`visitHalts_sound`) |
| a later `cur` = 3, a block after it | halts, every time (2,209) |
| a later `cur` = 1, a block after it | halts in 446 lists, goes on in 551 |
| a later `cur` = 2 | never halts (1,055): the two blocks merge |
| `cur` = 1 or 3 at the last block | does not halt (148) |
| `cur` = 4 or 7 at the last block | halts (383) |

Since `cur = l(i) + 2j` with j from the block before, a bad value needs **two small neighbours at the left end**:
the first block 1, 4 or 7 and the second block at most 5 (or three small blocks in a row). The typical case is
`[4, 3, ...]` or `[4, 1, ...]`: 4 keeps 2 and gives 2, the next value is 5 or 3, and the machine halts.

**Does the run get there?** The first block is cut by 3 at every visit, so it is 1, 4 or 7 all the time (9.3·10^7
times between events 2^31 and 2^32). The second block is large by then, because every r = 0 or r = 2 visit adds
two thirds of the first block to it; it stays small only through a long row of r = 1 visits. `c/passrun.c` runs
the map on 64-bit counts and prints, for each doubling of the event count, how small the second block was at
those moments:

| events | ones on the tape | smallest second block | second block ≤ 50 | ≤ 100 | ≤ 200 |
|---|---|---|---|---|---|
| 2^24 to 2^25 | 9.8·10^7 | 20 | 1 | 17 | 98 |
| 2^26 to 2^27 | 3.9·10^8 | 46 | 1 | 16 | 104 |
| 2^28 to 2^29 | 1.6·10^9 | 29 | 3 | 22 | 109 |
| 2^30 to 2^31 | 6.3·10^9 | 54 | 0 | 18 | 127 |
| 2^31 to 2^32 | 1.3·10^10 | 46 | 1 | 14 | 112 |
| 2^32 to 2^33 | 2.5·10^10 | 40 | 1 | 17 | 119 |
| 2^33 to 2^34 | 5.1·10^10 | 28 | 3 | 20 | 161 |
| 2^34 to 2^35 | 1.0·10^11 | 36 | 1 | 10 | 83 |
| 2^35 to 2^36 | 2.0·10^11 | 41 | 2 | 16 | 138 |
| 2^36 to 2^37 | 4.0·10^11 | 40 | 1 | 19 | 123 |
| 2^37 to 2^38 | 8.1·10^11 | 58 | 0 | 12 | 137 |

In 1.1·10^12 events (2^40; 3.2·10^12 ones on the tape, 9 blocks) the map never leaves its domain, so the machine
does not halt in that time (the map is proved in Lean; the run of it is a C program on 64-bit counts, 5.7·10^7
events a second, 5.4 hours). The run was made in stretches, resumed from saved lists; the counts of the last two
doublings are incomplete for that reason and are not in the table. But the near misses do not thin out: each doubling of the event count
brings about 20 second blocks below 100 and about 2 below 50, the same in every row from 2^13 on. Reading the
counts as a power law (about 20·(x/100)^2.3 states with second block ≤ x per doubling) gives of the order of
0.01 halting lists per doubling. That is a guess from a fit, not a bound, but it is not a sum that converges:
**the machine looks more likely to halt than not, and far beyond any run**: an even chance of a halt needs
something like 2^70 events or more, and the ones on the tape grow by 2.9 per event.

**Not done.** The step count of an event (so the run is stated in events, not steps); the exact rules outside
the domain other than the halt at 5 (only the table above). After a later value 3 with a block after it, the
machine starts a left-end visit of its own on the blocks to the right, the finished blocks staying behind `000`;
the same rules hold there until that inner first block is down to 2, and what happens then is not decoded. A
later value 2 merges two blocks.

## Status

Open; the event map above suggests a halt, far beyond any run. Kernel: the halting configurations, no halt in 10^4 steps (10^7 native), the travelling-0 rule `c_shift`,
the deal `deal` and j deals at once (`Deal.lean`, `deals`), **the event map** (`EventMap.lean`: `visit_sound`,
`start`, `not_halts_of_run`) and the halt at a later value 5 (`visitHalts_sound`, `halts_of_reach`). Halting needs E to read a 1. CTL (K = 2..5) and
NGramCPS (widths 2-8, -H, -U) fail.

## For later

The event map and the halt at a later value 5 are proved. Left: the other rows of the table (a later value 3,
2 or 1) as Lean rules, so that "the machine halts iff the map reaches a list of the table" becomes a theorem. A
halt hunt by iteration is hopeless at the measured rate (each event is already one step of the map, and the
blocks' base-3 digits are used up one visit at a time); a way to jump over whole cascades of the first block
would be needed.

## Reproduce

```sh
./tmrun 1RB1LD_0RC0RF_1LC0LA_0LE1LD_1LA---_0RB0LF 3000000000 at C R 100000
. /etc/profile.d/lean.sh && holdouts/1RB1LD_0RC0RF_1LC0LA_0LE1LD_1LA---_0RB0LF/lean/check.sh
python3 holdouts/1RB1LD_0RC0RF_1LC0LA_0LE1LD_1LA---_0RB0LF/lean/rules.py > /tmp/Rules.lean   # regenerates Rules.lean
cd holdouts/1RB1LD_0RC0RF_1LC0LA_0LE1LD_1LA---_0RB0LF
gcc -O2 -o events c/events.c && gcc -O2 -o onestep c/onestep.c && gcc -O2 -o passrun c/passrun.c
./events 3000000000 > events.txt && python3 py/passmap.py check events.txt   # ~1 min
python3 py/passmap.py test ./onestep && python3 py/passmap.py off ./onestep   # ~3 min
python3 py/passmap.py lean                                                    # the Lean definition against visit
./passrun 7e10                                                                # ~20 min; 1.1e12 takes 5.4 hours
```

## Pages

- [`pages/holdouts/1RB1LD_0RC0RF_1LC0LA_0LE1LD_1LA---_0RB0LF/explainer.html`](../../pages/holdouts/1RB1LD_0RC0RF_1LC0LA_0LE1LD_1LA---_0RB0LF/explainer.html)
- [`pages/holdouts/1RB1LD_0RC0RF_1LC0LA_0LE1LD_1LA---_0RB0LF/proof-status.html`](../../pages/holdouts/1RB1LD_0RC0RF_1LC0LA_0LE1LD_1LA---_0RB0LF/proof-status.html)

## Accelerated run

Trusted computation: `tools/c/rleaccel.cpp` (compiled port of `tools/py/bbtools/rleaccel.py`, checked against it by
`tools/tests/test_rleaccel_cpp.py`), blocks of 6, runs from blank tape without a halt to 2.89·10^14 machine steps (exact; tape:
346,326 cells). It ran about 30 minutes, resumed from a checkpoint after interruptions, so its macro count
(16,560,000,000) differs from an uninterrupted run's. Command: `g++ -O2 -o rleaccel tools/c/rleaccel.cpp && timeout 1800 ./rleaccel 1RB1LD_0RC0RF_1LC0LA_0LE1LD_1LA---_0RB0LF 6 1000000000000000 run.ck 300`.
