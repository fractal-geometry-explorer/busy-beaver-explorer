# 1RB1LD_0RC1RC_1RD0RE_0LA0LF_0RF---_1RA1LA

bbchallenge id 179721. One of the six-state holdouts whose halting from blank tape is open.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LD |
| B | 0RC | 1RC |
| C | 1RD | 0RE |
| D | 0LA | 0LF |
| E | 0RF | --- |
| F | 1RA | 1LA |

## What it does

Almost all of the tape is the word `110` repeated. The head is a **bouncer** with a **front**: the front starts at
the right end of the tape and walks left through the block of `110` units; on every sweep the head runs from the
front to the right end and back (right in a zigzag of states A B C E F, 13 steps per 3 cells; left fast, A D F
turning `111` into `101`). At the front it eats the last units of the untouched block and leaves a block of ones.

There are two kinds of phase and the run alternates them strictly:

- **growth**: two sweeps eat four units and leave 18 ones, and each sweep adds 3 cells at the right end;
- **stall**: two sweeps eat four units and leave 12 ones; the right end does not move.

The rules, proved in Lean for all values (`L` is anything left of the units, `j` counts triples of ones):

```
growth:  L (110)^(n+4) (111)^j 11 001 A> 0^inf    ->  L (110)^n (111)^(j+6) 11 001 A> 0^inf     in 32j+186 steps
stall:   L (110)^(n+4) (111)^j 11 0111 D> 0^inf   ->  L (110)^n (111)^(j+4) 11 0111 D> 0^inf    in 32j+124 steps
```

When the front reaches the left end it runs into the **zone**: fewer than 50 cells holding phase defects (walls
like `1110`, runs of ones). The head rewrites the zone, a left pass turns the ones back into `110` units, and the
next phase starts at the right end. A growth phase turns k units into about 1.5k; a stall phase keeps the length.
So each round (growth + stall) multiplies the length by about 3/2, minus a few cells taken by the zone, and costs a
number of steps proportional to the square of the length. That is the triage shape: the right side grows like the
square root of the step count, the zone (which creeps left by one or two cells a round) like its logarithm.

Lengths at the stall-phase starts (direct simulation): 252, 372, 546, 817, 1221, 1824, 2731, 4087, 6114, 9162, 13727,
20592, 30881, 46319, 69474, 104203.

## Does it halt?

The machine stops only in E reading 1: the right-moving zigzag comes out of C on a 1 and finds a second 1 where the
3-periodic tape has its 0. Inside the body that cannot happen (the phase rules above cover it), so a halt can only
come from the zone. The zone's successor depends on how the front arrives, i.e. on the residue of the length: the
same zone word (`1110 (110)^5 1110`) has led to different successors at lengths 371 and 69,473. It is a
Collatz-like problem whose map has not been extracted. **Open.**

## Closed-set attempt (13 November 2026)

Same method as for id 31480 (big count free, remainders only, finite set of nodes). **It does not close, and no
halting class was found.**

- Checkpoint: the start of a growth phase, `0^inf Z (110)^n 01 A> 0^inf`, Z the zone. `c/round.c` runs one round
  (growth + stall) from such a tape.
- The next zone and the next length depend on (Z, n mod 8), and `n' = (3n + k)/2` with k between -28 and 23 in the
  cases seen (checked for n = 240..287 on the first zones).
- With every residue allowed the zones are unbounded: a zone is walls (`1110`, runs of ones) around inner segments
  `(110)^k`, and a round rescales the inner segments too (k = 8 becomes 11, 15, 16 or 22 for n even, and is absorbed
  into the body for n odd). `py/zones_bfs.py`: 1,513 zones x 8 residues without a halt and without closing; with
  inner segments of 4 or more units replaced by a wildcard, 3,900 templates and 14,500 unexplored when stopped.
- So the real run keeps its zone under 50 cells only because of the particular residues it meets; the map on
  (zone, n mod 8) with n -> 3n/2 is a Collatz-like problem on a growing structure. The n-gram and run-length
  pushdown closures of `../1RB1RD_1RC1LD_0LA1RA_1LE0RC_---1LF_0LA0LB/c/pds.cpp` report false halts at every size tried.

## For later

Stopped at: the bulk phases are proved; the zone is described only empirically. Next steps:

1. Decode the zone transitions: `c/phases.c` + `py/phases.py` give the zone at each phase start; the zone visits are
   short (the head stays within the first ~60 cells), so `(zone word, arrival state of the front)` -> `(next zone
   word)` is a finite table that can be built by direct simulation of the zone alone from each arrival
   configuration, for both phases. The arrival state is the parity of the front (it alternates between `... 1^5 0
   1^m` and `... 1^m` every sweep), i.e. on a residue of the number of units; find which residue decides it.
2. With that table, write the round map (zone, length) -> (zone', length') and iterate it (much faster than
   `py/fastsim.py`), look for the halting zone pattern and estimate how likely it is.
3. Then prove the zone transitions with `bbtools.symtm` (each is a finite run with the body as a repeat) and chain
   them with `lean/Phase.lean` into a one-round theorem.

## Status

Open. Lean, kernel only: `lean/Rules.lean` (`growth_two_sweeps`, `stall_two_sweeps`, generated by `py/gen_rules.py`),
`lean/Phase.lean` (`growth_phase`, `stall_phase`: any number of sweeps, by induction). `lean/Blank.lean`: the halting
configurations (`step_none_iff`), no halt in 10,000 steps by the kernel, in 10,000,000 by `native_decide`. C
(`tools/c/triage.c`): no halt in 10^9 steps; `c/phases.c`: no halt in 1.5·10^10 steps (32 phases). `py/fastsim.py`
(macro simulator with unproved linear-cycle jumps): no halt to about 6·10^15 steps, length 7·10^7.

## Pages

- [`pages/holdouts/1RB1LD_0RC1RC_1RD0RE_0LA0LF_0RF---_1RA1LA/explainer.html`](../../pages/holdouts/1RB1LD_0RC1RC_1RD0RE_0LA0LF_0RF---_1RA1LA/explainer.html)
- [`pages/holdouts/1RB1LD_0RC1RC_1RD0RE_0LA0LF_0RF---_1RA1LA/proof-status.html`](../../pages/holdouts/1RB1LD_0RC1RC_1RD0RE_0LA0LF_0RF---_1RA1LA/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LD_0RC1RC_1RD0RE_0LA0LF_0RF---_1RA1LA/lean/check.sh
PYTHONPATH=tools/py python3 holdouts/1RB1LD_0RC1RC_1RD0RE_0LA0LF_0RF---_1RA1LA/py/gen_rules.py   # regenerates lean/Rules.lean
```
