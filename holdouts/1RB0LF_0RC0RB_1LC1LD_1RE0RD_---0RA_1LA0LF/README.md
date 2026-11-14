# 1RB0LF_0RC0RB_1LC1LD_1RE0RD_---0RA_1LA0LF

bbchallenge id 147837, a six-state holdout of group G05 (growth class fixed/sqrt). **Open.** The tape is a sea of
`1010...` carrying a dozen *particles* (short defects) that the head pushes around like a counter with carries;
halting needs a *D-run*, which in the first 10^9 steps happened only four times, all at the right end of the tape.
Its twin `1RB0RA_1LC0RA_0LD0LC_1RD1RE_1LF0LE_---0LB` (bbchallenge id 29825) has the same table mirrored and starts in another state: it
runs the same tape with one extra 1 at the far wall, a different run and a separate question (see
[its folder](../1RB0RA_1LC0RA_0LD0LC_1RD1RE_1LF0LE_---0LB/README.md)).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LF |
| B | 0RC | 0RB |
| C | 1LC | 1LD |
| D | 1RE | 0RD |
| E | --- | 0RA |
| F | 1LA | 0LF |

## What it does

**The sea and its junctions.** Almost all of the tape alternates, `1010...`. Call a *junction* a place where two
equal cells touch (`00` or `11`). Moving left, F and A complement every cell they pass (`F1 -> 0`, `F0 -> 1` then
`A1 -> 0`, ...) until A finds a 0 next to a 0; moving right through the sea, the C/D zigzag (`C1 -> 1LD`,
`D0 -> 1RE`, `E1 -> 0RA`, `A0 -> 1RB`, `B1 -> 0RB`, `B0 -> 0RC`) complements it too. Complementing does not move
junctions, so **a pass of the head over the sea changes nothing that matters; only the junctions are information.**
Junctions come in small clusters, the *particles*; between them lie long stretches of sea.

**The particles** (names are the gaps between the junctions of the cluster, as `py/particles.py` prints them):

| particle | cells | moves per cycle when reached |
|---|---|---|
| left gadget `3.4.1.2` | `0 0 1 0 0 1 0 1 1 1 0` at the left end | 8 cells left (the tape grows by 8) |
| `o` | a single `00` | 4 left |
| P = `4.1` | `0 0 1 0 1 1` | 12 left (when it is the last particle reached) |
| Q = `4.T1` | `0 0 1 0 1 1 (1011)^k`: P followed by a *train* of the sea `1110` | 8 left, the train grows by 2 words |
| R = `3` / `1.4.1.1.1` | alternates between two forms | 4 left |
| trains `T...` | stretches of the second sea `(1110)^k` with defects | 8 left |

**The left gadget is a 2-bit counter.** The head comes back to the left end four times per *cycle*: three short
trips (22, 34, 22 steps) that only flip the gadget, and one deep trip that runs right through the sea until it is
turned back by a particle. Each left-end visit adds 2 cells, so the tape grows by 8 cells per cycle at the left.

**A cycle, exactly** (`cycleP`, kernel-checked for all x, y): with P the first particle,

    0^inf F> 0 0 1 0 0 1 0 1 1 1 0 0 1 (0101)^(x+4) 0 0 1 0 1 1 (1010)^y R
      --(40x + 330 steps)-->
    0^inf F> 0 0 1 0 0 1 0 1 1 1 0 0 1 (0101)^(x+3) 0 0 1 0 1 1 (1010)^(y+3) R

The deep trip stops at P, which jumps 12 cells left: the sea in front of it loses 4 cells, the sea behind it gains
12. After about x more cycles P reaches the gadget; the collision makes new particles and the next deep trips go
further. When the first particles are `o`, Q and R instead, a cycle moves `o` and R 4 cells and Q 8 cells left and
adds two `1011` words to Q's train (a six-parameter rule that `bbtools.symtm` also proves, but whose Lean proof takes
about six minutes to check, so it is not in `lean/`).

**The emergent behaviour: a counter of particles.** As in a counter, the first particle is hit every cycle, the
next ones only when the first is used up, and a deep trip that gets past every particle reaches the right end of
the tape (the *wall*, `... 1^6 0 1^4`), where it grows the wall. The number of particles stays small (11 to 15 at
every sample of the first 10^9 steps) while the seas between them grow, so the tape length grows like the square
root of the step count. Trips that reach the wall are rare (`c/deep.c`, the rightmost cell the head
reaches in each doubling of the step count): the head reached the wall (cells 42 to 56) between 1·10^6 and 8·10^6
steps, then not again until a trip between 2.1·10^9 and 4.3·10^9 steps grew the tape to cell 84, and once more
between 8.6·10^9 and 1.7·10^10; in the other doublings up to 6.9·10^10 it stayed left of cell −2.

**Where it could halt.** It halts on `E0`. E is entered only from `D0`; D from `C1` (moving left: then the cell E
reads is the 1 C just wrote) or from `D1`. So **two steps before a halt D reads a 1** (`halt_needs_drun`, kernel):
the head must be in a *D-run*, D erasing a block of 1s to the right, which then stops on `0 0`. D-runs need C to
meet `1 1` moving left, which the sea and the particles never show it: in the first 10^9 steps there were exactly
four D-runs, at steps 130, 309, 2,306,898 and 2,380,763, all of them the wall's block `1^6` being erased when a
trip reached the right end (each time the block after it, `1^4` or `1^5`, saved the machine). So halting is a
question about the rare trips that carry all the way to the wall, and about the wall they find there.

## Status and evidence

**Lean, kernel** (`lean/Halt.lean`): `halt_needs_drun`: two steps before a halt the head is D reading a 1.
**Lean, kernel** (`lean/Rules.lean`, written by `py/gen_rules.py` with `bbtools.symtm.prove`): `cycleP` (one cycle
of the gadget with P first, 40x + 330 steps, for every x, y and every tape R right of it).
**Lean** (`lean/Blank.lean`, generated): `step_none_iff`, no halt in 10^4 steps (kernel), 10^7 (`native_decide`).

**Computed (trusted)**: the direct C simulator finds no halt in the first 10^11 steps; `c/drun.c` lists every
D-run of the first 10^9 steps (the four above); `c/deep.c` gives the deepest point of the trips per doubling of
the step count; `c/twin.c` runs this machine and its twin side by side for 10^9 steps (see below).

**Heuristic**: the particle picture (`py/particles.py`, the displacements per cycle in the table) is read off
samples; it is not proved that the particle set stays finite-like or that D-runs happen only at the wall.

**Open**: whether a trip ever reaches the wall in a shape where the D-run ends on `0 0`.

## The twin

`1RB0RA_1LC0RA_0LD0LC_1RD1RE_1LF0LE_---0LB` is this machine with left and right swapped and the states renamed
(its A, B, C, D, E, F are this machine's F, A, B, C, D, E), started in this machine's state F. Its first step
writes a 1 and moves into this machine's state A, so from step 1 on it runs this machine from a tape with one extra
1 next to the start. `c/twin.c` runs both: at each of the 32,539 left-end records of the first 10^9 steps the two
tapes are equal except for one extra 1 at the end of the wall, and the step counts differ by 56 (constant since
step 4,194,242, the last time a trip reached the wall). So the two machines do the same thing; they could differ
only in a trip to the wall, where the twin's last block is one longer.

## Reproduce

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LF_0RC0RB_1LC1LD_1RE0RD_---0RA_1LA0LF/lean/check.sh
python3 holdouts/1RB0LF_0RC0RB_1LC1LD_1RE0RD_---0RA_1LA0LF/py/gen_rules.py > Rules.lean   # regenerate the rules
cd holdouts/1RB0LF_0RC0RB_1LC1LD_1RE0RD_---0RA_1LA0LF
gcc -O2 -o snap c/snap.c && ./snap 1RB0LF_0RC0RB_1LC1LD_1RE0RD_---0RA_1LA0LF 3000000 4 > s.txt && python3 py/particles.py s.txt
gcc -O2 -o drun c/drun.c && ./drun 1RB0LF_0RC0RB_1LC1LD_1RE0RD_---0RA_1LA0LF 1000000000      # the D-runs
gcc -O2 -o deep c/deep.c && ./deep 1RB0LF_0RC0RB_1LC1LD_1RE0RD_---0RA_1LA0LF 1000000000      # how deep the trips go
gcc -O2 -o twin c/twin.c && ./twin 1000000000                                                  # against the twin
```

## Deciders tried (F11, 13 November 2026)

None closes. Each reaches a halting configuration in its abstraction, which says nothing about halting.

- n-gram CPS (`tools/c/ngramcps.c`), equal widths on both sides: a halting local configuration is reached with plain up to width 14, history 1 up to width 12, history 2 up to width 10, history 3 up to width 10, LRU history up to width 2 (larger widths ran out of the 150 s or 60 million configuration budget).
- n-gram CPS with every cell tagged by its position mod p: fails for p = 2 up to width 12, p = 3 up to width 12, p = 4 up to width 12, p = 6 up to width 12.
- n-gram CPS where each side also carries the state of a small automaton that has read that side from the far end (every automaton with up to 3 states on both sides, or 4 states on one side), with position mod 1..4 and widths 4, 6, 8: no closed set without a halt in all 120 parameter sets.
- Run-length windows (the K nearest runs of equal macro cells on each side, run lengths kept exactly below T and mod M above): fails for all 72 parameter sets (cells of 1 to 4 bits, K = 2, 4, 6, T = 2, 4, M = 1, 2, 4).
- Two-automaton closed tape language by SAT (a deterministic automaton reading each side inward, n states each, CaDiCaL): no solution for n = 2..7; n = 8 not finished in 150 s.

## Where a halt can come from

`lean/Route.lean` (kernel, written by `py/route.py`): `halt_route`, two steps before any halt the machine is in one
of: D with 1 under the head, 0 right, 0 two right.

## Pages

- [`pages/holdouts/1RB0LF_0RC0RB_1LC1LD_1RE0RD_---0RA_1LA0LF/explainer.html`](../../pages/holdouts/1RB0LF_0RC0RB_1LC1LD_1RE0RD_---0RA_1LA0LF/explainer.html)
- [`pages/holdouts/1RB0LF_0RC0RB_1LC1LD_1RE0RD_---0RA_1LA0LF/proof-status.html`](../../pages/holdouts/1RB0LF_0RC0RB_1LC1LD_1RE0RD_---0RA_1LA0LF/proof-status.html)

## For later

A decision needs the particle dynamics as an exact macro machine: the list of particles with the seas between them,
the rule for a deep trip (which particles it passes, how each moves, where it turns), and the collision rules. The
cycle rule in `lean/Rules.lean` is the first entry of that table. With it, the question becomes whether the
rare trips that reach the wall ever find it in a halting shape, which may be a counter-like or Collatz-like
question in its own right.

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0RA_1LC0RA_0LD0LC_1RD1RE_1LF0LE_---0LB`](../1RB0RA_1LC0RA_0LD0LC_1RD1RE_1LF0LE_---0LB/README.md): rename A→B, B→C, C→D, D→E, E→F, F→A and exchange left and right; it is this table started in state F, in a mirror

<!-- end of related machines -->
