# 1RB1RD_1LC0RD_0LE1RD_1RA0RB_---1LF_1RA0LF

bbchallenge id 71111. One of the six-state holdouts whose halting from blank tape is open (group G07).
Family: **bouncer feeding a cascade of unary counters (Collatz-like)**. Decision: **open** (no halt in the first 9.53·10^2780 steps, exact accelerated simulation).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RD |
| B | 1LC | 0RD |
| C | 0LE | 1RD |
| D | 1RA | 0RB |
| E | --- | 1LF |
| F | 1RA | 0LF |

## What it does

The tape has three parts (an *event* below is the head reaching a new cell at the left end; it does so in state F):

    prefix | bulk (00000001010)^n | counter list  (101)^c1 sep (101)^c2 sep (101)^c3 sep ...

* The **prefix** (about 60 cells at the left end) goes through a fixed dance of 160 events.
* The **bulk** is a run of one 11-cell word. The head crosses it to the right in B, 53 steps a word, turning
  `01010000000` into `01111111111`, and comes back in F, 19 steps a word, leaving `10100000000` (Lean:
  `bulk_right`, `bulk_left`, for every length and every tape around).
* The **list** is a row of unary counters `(101)^c` separated by short words (`001010000`, `0000`, `00`, ...).

**The linear regime.** For long stretches every period of 160 events does the same thing:

    bulk + 14 words        c1 - 6        c2 + 4        c3 + 4          (14*11 + 3*(4 + 4 - 6) = 160 cells)

for instance (`py/counters.py`, events 160,000 to 161,280: bulk, then the list with each `(101)^c` written as c)

    14033   01011 51 001010000  78 001010000 27 00 32 001010000 1693 00101000000 2
    14047   01011 45 001010000  82 001010000 31 00 32 001010000 1693 00101000000 2
    ...
    14145   01011  3 001010000 110 001010000 59 00 32 001010000 1693 00101000000 2

**The reorganisation.** When the first counter is used up the head works through the front of the list for a few
periods, the separators change and the next counter becomes the first one:

    14158   0000010100 114 001010000 65 00 32 001010000 1693 00101000000 2
    14173   01011 106 001010000 68 00 32 001010000 1698 00101000000 2

So the counters form a cascade: each one is drained into its two right neighbours (6 out, 8 in), and what the deep
counters receive depends on the residues of the counters above them at the moment they run out, as in a
Collatz-type map on several numbers. The regimes get longer and longer (the first counter at event 1.6·10^6 is
4,550 and takes 758 periods); the number of regimes up to event N grows like log N (about 73 regimes for every
factor of 10 in N).

**Where it can halt.** The halting transition E0 is reached only as B0 -> 1LC, C0 -> 0LE, E0 with two 0s left of
B, and B gets there only from D1 -> 0RB after B1 -> 0RD. So **the machine halts iff B reads a 1 that is followed by
`1 0`** (five steps later). Crossing a counter, B and D alternate over `101 101`, where B always reads `1 0 1`; a
halt needs a counter boundary to come up in the wrong phase.

## Exact accelerated simulation

Two programs in `c/`, neither specific to this machine:

* `accsim.c` keeps the tape as two stacks of cells and runs of words. When the head arrives at a run it simulates
  one word; if it arrives at the next word in the same state with the same cells behind it (the cells it read),
  every further word is crossed the same way and the whole run is crossed at once (also when the state comes back
  only every 2, 3 or 4 words). This is a proof by induction done at run time, the same statement as the Lean shift
  rules. With `accel=0` it is a plain simulator.
* `accbig.c` adds jumps over the linear regime and big integers. Every 160 events it samples the tape (the head is at
  the left end, so the sample is the whole tape). If 14 consecutive samples have the same items and state, every run
  count moves by a constant and the step count per period moves by a constant, it applies k periods at once, k as
  large as keeps every shrinking count at least 64 words: counts `c + k d`, steps `k D + b k(k-1)/2`. (Between two
  samples the machine touches a long run only by crossing it with a shift rule of period at most 4 words, so 12
  consecutive periods cover every residue of every count, or by reading at most 88 cells into it.)

Validation (`py/validate.py` repeats the small ones):

| compared | at | steps |
|---|---|---|
| plain = shift rules | event 2^16 | 862,346,648 |
| shift rules = cycle jumps (172 jumps) | event 2^30 | 227,917,881,554,541,656 |
| cycle jumps with big counts = a second implementation with 64-bit counts and jumps capped at 2^40 periods | event 3,664,347,573,759,331,520 | 2,650,260,827,707,083,500,593,764,707,198,611,370 |

**Result.** `accbig 1RB1RD_1LC0RD_0LE1RD_1RA0RB_---1LF_1RA0LF 160 100000 3 11` goes through 100,000 cycle jumps (linear regimes) without a halt: it stops at event
6.94·10^1390, after 9.53·10^2780 steps (the exact numbers, 1,391 and 2,781 digits, are in `c/accbig_run.txt`). The machine does not halt
in its first 9.53·10^2780 steps.

## Status

Open.

* **Kernel**: the halting configurations and 10^4 steps (`lean/Blank.lean`; 10^7 by `native_decide`); the three
  long crossings `bulk_right`, `bulk_left`, `list_left` for every length (`lean/Shifts.lean`, from `py/rules.py`).
* **Trusted**: no halt in the first 9.53·10^2780 steps (`c/accbig.c`, validated as above; the cycle jumps rest on the
  argument in the header of that file, not on a machine-checked proof); the linear regime and the halting
  criterion above.
* **Heuristic**: nothing. The reorganisations are Collatz-like; 100,000 of them passed without the halting pattern, which
  says that a halt, if possible at all, needs a rare combination of residues.
* **Open**: whether it halts.

## Next steps

* Write the reorganisation as an exact map on (separators, counters): the cases are finite (the separators are a
  handful of words, the counters enter through their residues mod 6 and through comparisons), and `accbig` gives
  every case with `VERB=1` and `TRACE`-like dumps. With the map, either an invariant (a set of list shapes closed
  under the map that never shows `B>110`) proves non-halting, or the halting case can be searched for directly.
* A Lean proof of the linear regime: one period for symbolic c1, c2, c3 with `bbtools.symtm` (the three crossings are
  already theorems).

## Pages

- [`pages/holdouts/1RB1RD_1LC0RD_0LE1RD_1RA0RB_---1LF_1RA0LF/explainer.html`](../../pages/holdouts/1RB1RD_1LC0RD_0LE1RD_1RA0RB_---1LF_1RA0LF/explainer.html)
- [`pages/holdouts/1RB1RD_1LC0RD_0LE1RD_1RA0RB_---1LF_1RA0LF/proof-status.html`](../../pages/holdouts/1RB1RD_1LC0RD_0LE1RD_1RA0RB_---1LF_1RA0LF/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RD_1LC0RD_0LE1RD_1RA0RB_---1LF_1RA0LF/lean/check.sh
cd holdouts/1RB1RD_1LC0RD_0LE1RD_1RA0RB_---1LF_1RA0LF
python3 py/rules.py | diff - lean/Shifts.lean
python3 py/validate.py                                   # plain = shift rules = cycle jumps, a minute
gcc -O2 -o /tmp/accbig c/accbig.c && /tmp/accbig 1RB1RD_1LC0RD_0LE1RD_1RA0RB_---1LF_1RA0LF 160 1000 3 11          # 1,000 regimes, 40 s
/tmp/accbig 1RB1RD_1LC0RD_0LE1RD_1RA0RB_---1LF_1RA0LF 160 100000 3 11                            # the run of c/accbig_run.txt, about 100 minutes
gcc -O2 -o /tmp/accsim c/accsim.c && python3 py/counters.py /tmp/accsim 160000 160 161700 all     # the counter list
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0RC_1RC1RA_1LD0RA_0LE1RA_---1LF_1RB0LF`](../1RB0RC_1RC1RA_1LD0RA_0LE1RA_---1LF_1RB0LF/README.md): rename A→B, B→C, C→D, D→A, E→E, F→F; it is this table started in state D

<!-- end of related machines -->
