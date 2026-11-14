# 1RB1RA_0LC0RF_1LD1LC_1RE1LB_---0RA_1RF0RD

bbchallenge id 81504. A BB(6) holdout whose halting from blank tape is open. Family: **unary visit counter fed to an irregular word** (mirror-image sibling: [`1RB1RA_1LC1RE_---0LD_1LE1LD_0RA0LF_1LF0LB`](../1RB1RA_1LC1RE_---0LD_1LE1LD_0RA0LF_1LF0LB/README.md)). Decision: **open**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RA |
| B | 0LC | 0RF |
| C | 1LD | 1LC |
| D | 1RE | 1LB |
| E | --- | 0RA |
| F | 1RF | 0RD |

## What it does

The tape is an irregular word W (a few thousand cells, fixed on the left: 344 cells left of the start) followed by
a long run of 1s, `0^inf W 0 1^n`, and every visit of the right end is in B on the blank cell after the run.

**The run is a visit counter** (proved in Lean, `lean/Rules.lean`): from a visit the head writes a 0, walks down
the run in C (`descend`, 2n + 1 steps) and works on W; when it comes back to the foot of the run in A it climbs it
and adds a 1 at the top (`climb`), which is the next visit. So the run grows by one per visit, apart from what W
eats from its foot: in the exact simulation (`py/runwatch.py`) the run got shorter (by 1 to 6 cells) at 2,634 of
the first 31,803 visits, while W grew to about 2,000 cells; at 2·10^10 steps (C, 144,695 visits, all in B) the run is
up to 137,905 cells long and W about 6,500.

**Where it can halt.** `lean/Edge.lean` (`halts_iff_edge`, from a closed tape language with windows of 3 cells):
the machine halts iff E reaches the blank region at the right. E is entered only from D reading 0 (`1RE`), and the
only state that crosses a run of 1s to the right is A (B and F eat the 1s they step on, two at most, and D turns
back on a 1). So a halt needs W to eat the whole run first. The run grows by one each visit while W eats about one
cell in fifteen: on current evidence the run outgrows W for ever, but W's dynamics are irregular and not decoded.

## Dedicated pass: the run as a number, 3·10^7 visits

**The word W never sees how long the run is.** A climb (`A` at the foot of `1^n`) costs 2n + 3 steps, makes the run
`1^(n+1)` and puts the head, in C, on the cell left of it; everything else the machine does happens in W and in the
first cells of the run (B and F turn the 1s they step on into cells of W: W *eats* the run from its foot). So the
machine is W's own dynamics on the tape `W 1^∞` plus one number n: +1 at each climb, −1 for each cell eaten, and by
`halts_iff_edge` **it halts iff n is exhausted**, that is iff W eats the whole run between two climbs.
`c/runsim.c` simulates exactly that (W cell by cell, the run as a number; step counts checked against its own
cell-by-cell mode), about 3·10^4 times faster than the plain machine at the end of the run below:

| visits (climbs) | steps | run n | W (cells) | deepest excursion since the last line |
|---|---|---|---|---|
| 1,048,576 | 1,053,865,261,445 | 1,006,004 | 42,917 | 1,199 |
| 8,388,608 | 67,562,353,555,001 | 8,058,709 | 330,244 | 1,100 |
| 16,777,216 | 270,398,614,654,351 | 16,115,171 | 662,390 | 1,201 |
| 30,000,000 | 864,573,494,721,963 | 28,822,306 | 1,178,039 | 1,202 |

No halt in 3·10^7 visits, 8.6·10^14 steps. The run gains 0.961 cells a visit, W 0.039. The work is local: the head
goes at most 1,202 cells below the foot (8-15 cells in 32% of the visits, 16-31 in 30%, 32-63 in 20%, 64-127 in
12%, 128-255 in 5%, 256-511 in 1.1%, more in 0.05%), and the left half of W is never read again (between visits
16,777,216 and 30,000,000 the lowest cell read is 661,691 of 1.18 million). Cells eaten per visit, over all visits:

| eaten | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| visits | 20,447,390 | 7,173,847 | 521,295 | 867,859 | 535,318 | 51,199 | 256,841 | 127,019 | 12,916 | 5,776 | 344 | 162 | 22 | 3 | 9 |

**Heuristic.** A halt at visit v needs about v cells eaten in one excursion. The number eaten has a geometric tail
(roughly a factor of 10 or more for every 2 more cells from 8 on), so the chance is of the order 10^(-v/2) at visit v, and
the sum over v ≥ 3·10^7 is nothing: the machine almost certainly never halts. A proof needs a bound on what one
excursion can eat. No bound independent of the tape exists (the maximum grows slowly with the number of visits),
and a potential argument "W holds fuel that each climb refills by at most one" does not work with a simple fuel: a
linear program over the counts of all windows of 3 to 6 cells of W at 20,000 visits has no solution.

**The sibling.** `1RB1RA_1LC1RE_---0LD_1LE1LD_0RA0LF_1LF0LB` is this machine reflected, with the states renamed, started in this machine's state C; its
word W is the same at every visit and its run is one cell shorter (see its README, `py/sibling.py` there).

## Status

* **Lean (kernel)**: `lean/Edge.lean`, `halts_iff_edge`: the machine halts from blank tape iff E reaches the blank
  region at the right (closed tape language from windows of 3 cells, `lean/EdgeCert.lean`, generated by
  `python3 -m bbtools.ctl 1RB1RA_0LC0RF_1LD1LC_1RE1LB_---0RA_1RF0RD 3 lean H81504 Blank`).
* **Lean (kernel)**: `lean/Rules.lean` (from `py/rules.py`): `descend`, `climb` (and odd-length versions) for
  every run length and every tape left of it.
* Lean (`lean/Blank.lean`): no halt in 10^4 steps (kernel), 10^7 (`native_decide`).
* **Trusted**: `py/blocksim.py` crosses the run at once (checked against the C simulator at every visit to
  3·10^6 steps, `py/bscheck.py`); 2·10^10 steps without a halt (`c/wallstat.c`: 144,695 right-end extensions, all in B).
* **Trusted**: `c/runsim.c` (the run as a number; agrees with its cell-by-cell mode): no halt in 3·10^7 visits =
  864,573,494,721,963 steps; the statistics of the dedicated pass above.
* **Heuristic**: it never halts (geometric tail of the number of cells eaten per visit).
* **Open**: W's dynamics, and so whether it ever eats the run.

## Next steps

* Decode W: it changes only near the foot of the run (the head enters it from the run in C and leaves in A), so its
  evolution is a sequence of local rewrites; find them (blocksim traces of each excursion) and the rate at which W
  eats the run.
* If W's growth is a bouncer-like linear process with a bounded appetite, non-halting follows from the Lean rules
  above and `halts_iff_edge`.

## Pages

- [`pages/holdouts/1RB1RA_0LC0RF_1LD1LC_1RE1LB_---0RA_1RF0RD/explainer.html`](../../pages/holdouts/1RB1RA_0LC0RF_1LD1LC_1RE1LB_---0RA_1RF0RD/explainer.html)
- [`pages/holdouts/1RB1RA_0LC0RF_1LD1LC_1RE1LB_---0RA_1RF0RD/proof-status.html`](../../pages/holdouts/1RB1RA_0LC0RF_1LD1LC_1RE1LB_---0RA_1RF0RD/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RA_0LC0RF_1LD1LC_1RE1LB_---0RA_1RF0RD/lean/check.sh
cd holdouts/1RB1RA_0LC0RF_1LD1LC_1RE1LB_---0RA_1RF0RD/py && python3 rules.py > ../lean/Rules.lean && python3 runwatch.py 60 5000
gcc -O2 -o /tmp/runsim ../c/runsim.c && /tmp/runsim 1RB1RA_0LC0RF_1LD1LC_1RE1LB_---0RA_1RF0RD A C 1000000        # 10^6 visits, 10^12 steps, 20 s
/tmp/runsim 1RB1RA_0LC0RF_1LD1LC_1RE1LB_---0RA_1RF0RD A C 20000 0 0 | grep 'visit 20000'; /tmp/runsim 1RB1RA_0LC0RF_1LD1LC_1RE1LB_---0RA_1RF0RD A C 20000 0 1 | grep 'visit 20000'   # jump = cell by cell
cd ../../../tools/py && python3 -m bbtools.ctl 1RB1RA_0LC0RF_1LD1LC_1RE1LB_---0RA_1RF0RD 3 lean H81504 Blank | diff - ../../holdouts/1RB1RA_0LC0RF_1LD1LC_1RE1LB_---0RA_1RF0RD/lean/EdgeCert.lean
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB1RA_1LC1RE_---0LD_1LE1LD_0RA0LF_1LF0LB`](../1RB1RA_1LC1RE_---0LD_1LE1LD_0RA0LF_1LF0LB/README.md): rename A→D, B→E, C→A, D→B, E→C, F→F and exchange left and right; it is this table started in state C, in a mirror

<!-- end of related machines -->
