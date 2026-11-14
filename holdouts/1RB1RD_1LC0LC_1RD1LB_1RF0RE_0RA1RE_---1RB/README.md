# 1RB1RD_1LC0LC_1RD1LB_1RF0RE_0RA1RE_---1RB

bbchallenge id 148224. One of the six-state holdouts whose halting from blank tape is open (group G07).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RD |
| B | 1LC | 0LC |
| C | 1RD | 1LB |
| D | 1RF | 0RE |
| E | 0RA | 1RE |
| F | --- | 1RB |

## What it does

The same mechanism as 1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---0RC (that README has the shared description and tools),
with longer words. A *visit* is a step at which the head extends the tape to the left in state B; the tape, read
rightwards from the head, is then

    B>0  111  (011111)^n  R  0^inf

a block of 6-cell words that grows, and a region `R` that is transformed by a map independent of `n` (up to the
phase of the block, which has period 3: the length of `R` cycles through three values 2 apart). `R` is a list of
runs of 1s of odd length separated by single 0s:

* a **near zone** next to the block, a few dozen cells of runs of lengths 1, 3, 5, 7, ..., which changes at
  nearly every visit and behaves like a chaotic counter;
* a **reservoir** of runs of exactly five 1s (`111110` words), which the near zone eats slowly: about 7 cells for
  each doubling of the number of visits;
* a **far zone** at the fixed end. Unlike in the sibling machines, the head reaches it long before the reservoir is
  used up: now and then a sweep crosses the whole reservoir, shifts it and changes the far zone. In the 300,000 visits
  after 8,400 this happened 16 times, at visits 8406, 8445, 8454, 8736, 9142, 9621, 10678, 10686, 10902, 16800, 27549,
  57888, 158742, 170205, 268341 and 272566, i.e. more and more rarely.

So there are two counters, one at each end of the reservoir (this is the tracker's "family of five-run tapes").
An **event** is a sweep that comes home in the wrong state: the block becomes fresh reservoir and `n` restarts.
Events so far: after visits 33 (`R` from 35 to 92 cells) and 8,347 (`R` from 95 to 16,724 cells, a reservoir of 2,758
words, at about step 1.2e8). With 16,600 cells of reservoir and 7 cells per doubling the next event is about
2^2400 visits away (the tracker's "2^2800 records" is the same estimate with a slightly smaller rate).

The halting transition is F0, reached only as `D>0 0` moving right: D must find two 0s in a row, and inside the tape
all 0s are single. In the models the halts are at the far end.

## Status

Open (cryptid-like).

- **Kernel / native_decide:** `lean/Blank.lean`.
- **Computed (trusted):** `resetsim` (in `holdouts/1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---0RC/c/`) with `PREFIX=111`
  and the block cut to 10 words agrees with the true run at all of the first 9,000 visits (events at 33 and 8,347);
  from visit 8,400 it runs 4e6 visits (about 3e13 steps) without a halt. `rvis` (same folder) records the depth of
  each sweep: the crossings listed above.
- **Heuristic:** the rate of 7 cells per doubling and the 2^2400 estimate. With the block cut to 2 words at every
  visit from the start (so that reservoirs stay short and events come quickly) the run halts after 24,517 visits
  (after 5,727 if the cut ignores the block's phase); with 3, 4 or 5 words there is no halt in 2e7 visits. So events
  can halt in this family; whether the real ones do depends on the state of both zones when the reservoir runs out.
- **Not proved:** that halts happen only at the far end (`py/fctl.py` of the `..._1RA1RF_---1RD` sibling finds no
  closed language for this machine with parity windows up to 8 cells).
- **Open:** the law of the two zones, and whether an event halts.

```sh
gcc -O2 -o resetsim holdouts/1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---0RC/c/resetsim.c -I tools/c
PREFIX=111 ./resetsim 1RB1RD_1LC0LC_1RD1LB_1RF0RE_0RA1RE_---1RB L B 011111 10 1 9000 check
PREFIX=111 T0=8400 ./resetsim 1RB1RD_1LC0LC_1RD1LB_1RF0RE_0RA1RE_---1RB L B 011111 10 1 4000000
gcc -O2 -o rvis holdouts/1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---0RC/c/rvis.c
./rvis 1RB1RD_1LC0LC_1RD1LB_1RF0RE_0RA1RE_---1RB L B 111 011111 10 3 8400 300000 60 | awk '$3 > 10000'   # crossings
./rvis 1RB1RD_1LC0LC_1RD1LB_1RF0RE_0RA1RE_---1RB L B 111 011111 2 3 1 20000000 0 | tail -1              # small block
```

## Next steps

Describe the far zone's rule at a crossing (it is hit only 16 times in 300,000 visits, so its law may be simple) and
the near zone's rule in terms of run lengths; the event happens when the two meet.

## Pages

- [`pages/holdouts/1RB1RD_1LC0LC_1RD1LB_1RF0RE_0RA1RE_---1RB/explainer.html`](../../pages/holdouts/1RB1RD_1LC0LC_1RD1LB_1RF0RE_0RA1RE_---1RB/explainer.html)
- [`pages/holdouts/1RB1RD_1LC0LC_1RD1LB_1RF0RE_0RA1RE_---1RB/proof-status.html`](../../pages/holdouts/1RB1RD_1LC0LC_1RD1LB_1RF0RE_0RA1RE_---1RB/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RD_1LC0LC_1RD1LB_1RF0RE_0RA1RE_---1RB/lean/check.sh
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA`](../1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA/README.md): rename A→E, B→A, C→B, D→C, E→D, F→F and exchange left and right; it is this table started in state B, in a mirror

<!-- end of related machines -->
