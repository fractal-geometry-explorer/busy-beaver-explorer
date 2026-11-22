# 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE

bbchallenge id 56722. One of the six-state holdouts whose halting from blank tape is open. Family: Counter on the left feeding a growing region on the right (exp/power; structure not yet found).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RA |
| B | 1LC | 0RD |
| C | 1LD | 1LB |
| D | 1LE | 0LF |
| E | 0RA | --- |
| F | 0LB | 1RE |

**Verdict.** **The question is open.** No halt in the first 10^12 steps (C simulator); the macro configuration and its rules are not yet known, so there is no map to analyse and no heuristic for halting beyond the localisation of the halt below.

## What it does

Left of the start the tape is blocks of an odd number of 1s separated by double 0s; it grows like the logarithm of the
step count. Right of the start the tape is a long stretch of the words `1 0` and `1 1 0`, mostly `(1 0)^n`, growing like a
power of the step count (exponent about 0.68).

New this round: the right end grows by exactly 3 cells at 15,386 of the 15,470 visits in 2·10^9 steps. Between visits
the head turns back at a point that drifts right by about 29 cells per visit, so the swept zone shrinks; 3,478 times
the turning point jumps far left and a new phase starts.

## What is established

**Proved in Lean, kernel only:**

- **The halting configurations.** The machine stops exactly when it reads the symbol of a halting transition (E1); the generated statement covers every configuration. (`step_none_iff`, `lean/Blank.lean`)
- **PR 93's macro rules on this machine.** 8 of the rules of DeepMind's busycoq PR 93 engine as they hold here, for every count, including the changed collision, collisionD and collide (`lean/EngineRules.lean`; see [PR 93's engine on this table](#pr-93s-engine-on-this-table-22-november-2026)).
- **No halt in the first 10,000 steps.** The list simulator of the shared library, proved to agree with the machine's semantics, runs 10,000 steps from blank tape without a halt, evaluated by Lean's kernel. (`blank_runs_kernel`, `lean/Blank.lean`)
- **The eat visit of the right-end bouncer, for all counts.** `L 1^(a+3) (01011)^b (011)^c 0 D> 0^inf` reaches `L 1^a (01011)^b (011)^(c+2) 0 D> 0^inf` in 20b + 10c + 25 steps, for every a, b, c and every tape L (never read); k such visits in a row take k(20b + 10c + 15) + 10k² steps. (`eat_visit`, `eat_iter`, `lean/VisitRules.lean`, written by `py/visit_rules.py`; see [the right end](#the-right-end-a-bouncer-over-long-blocks-lead-18-22-november-2026))
- **One round of the right-end bouncer, for every chamber.** For every list of S-blocks between a wall and the right end, a long visit uses up three 1s of the wall, leaves the blocks unchanged and grows the last block (by 3 in regime I, where a short visit follows, and by 1 in regime II); k rounds in a row likewise; also at a wall of exactly three 1s. (`round_I`, `short_I`, `rounds_I`, `round_II`, `round_I3`, `round_II3`, `lean/RoundRules.lean`, written by `py/round_rules.py`; see [round by round](#round-by-round-walls-blocks-and-two-right-ends-22-november-2026))

**Proved in Lean with `native_decide`:**

- **No halt in the first 10^7 steps.** The same run, evaluated by compiled code. (`blank_runs_native`, `lean/Blank.lean`)

**Trusted computation (C/Python, not Lean):**

- **No halt in the first 10^10 steps.** The C simulator `tools/c/tmrun.c` runs 10^10 steps from blank tape without a halt; at the end the tape holds 94,290 ones. (`tmrun 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE 10000000000`)
- **No halt in the first 10^9 steps.** The C simulator `tools/c/triage.c` runs 10^9 steps without a halt; at the end 44,635 cells have been visited and 19,460 of them hold a 1. (`holdouts/triage.json`)
- **Where a halt can be.** A closed tape language of windows of 5 cells (`tools/py/bbtools/ctl.py`, closure checked by the script, not by Lean) contains every configuration reachable from blank tape, and its only halting configurations have E reading a 1 with at least four 1s right of the head (`E>1 1 1 1 1`). In the run so far the right region has shown no runs of five 1s, so a halt would have to happen inside a long block of 1s, as in the left region. (`python3 -m bbtools.ctl 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE 5`)
- **Not decided by n-gram CPS up to width 14.** The n-gram Closed Position Set decider (`tools/c/ngramcps.c`) with equal widths 4, 6, 8, 10, 12 and 14, plain and with the fixed-length (1) and LRU history augmentations, either reaches a halting local configuration (UNKNOWN) or stops at 3·10^7 local configurations: it does not prove non-halting at these settings. (`ngramcps MACHINE N [-H 1 | -U] -m 30000000`)
- **The halting route is never approached inside the tape.** A halt needs C reading 0 with 0 on its left and 1 beyond (`halt_route`). In the first 10^10 steps C reads a 0 574,777 times; the cell on its left is 0 only 1,883 times, all at the left end of the visited tape (blank beyond, so no halt), and never inside, where the cell on its left was always 1. (`c/route_census.c`: `./route_census 10000000000`)
- **Exact macro simulator.** `c/mm2.cpp` simulates blocks of K cells with two-block windows, so that sweeps which step back one cell per copy of a word still cross a whole run of equal blocks at once; nothing is extrapolated. With K = 15 its whole tape, state and head equal a direct simulator's at 1e6, 1e8 and 3·10^9 steps (and with K = 30 at six points up to 3·10^9), and on average it runs 2 to 4 times faster than direct simulation up to 3·10^11 steps. (`./mm2 MACHINE 15 LOG10MAX`)
- **The right end grows by three cells per visit.** Counting a visit as the head reaching the right end after having been more than 50 cells to its left, the first 2·10^9 steps have 15,470 visits; at 15,386 of them the right end has grown by exactly 3 cells since the previous visit (57 times by 6, the rest by 0, 1 or 5). The head turns back at a point that drifts to the right by about 29 cells per visit, so the zone it sweeps shrinks, and every so often (3,478 times) the turning point jumps far to the left and a new phase starts. Visits get further apart as the right region grows, which gives the power-law growth. (`c/rvisits.c`: `./rvisits MACHINE 2000000000 50`)

**Heuristic:**

- **Growth shape: exp/power.** Left of the start, the visited part of the tape grows like the logarithm of the step count: each new cell costs a roughly constant factor more time, the signature of a *counter* or of a Collatz-like map whose values are written on the tape (fitted exponent 0.062). Right of the start it grows like a power of the step count other than 1/2 (fitted exponent 0.677). (`tools/py/bbtools/triage.py`)
- **The two regions.** Left: `C>0 1 0^2 1^3 0^2 1^9 0^2 1 0^2 1 0^2 1^357 0^2 ...`, blocks of odd length separated by `0^2`, a few of them long (one of them has 205, 357 and 421 ones at three of the last left records before 10^9). Right: words `1 0` and `1 1 0`, with long stretches `(1 0)^n`. (`tmrun 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE 1000000000 records 100000`)

- **One digit list in two encodings, then long blocks.** At a left-end visit the tape left of the start is a list of digits `1 (11)^n 00` (605 of them at 2.0·10^9 steps, 589 with n ≤ 6, 5 other words, and one large digit, n = 302; 675 digits and n = 354 at 2.6·10^9). The list continues right of the start for several thousand cells (about 8,700 at 2.9·10^8 steps), written with single 0s (words `1`, `11`) while the head is on the right. Beyond it the right end holds a few long periodic blocks that turn into one another in phases: `(100)^m` (read `(110)^m` after a right sweep), `(10110)^n` / `(00111)^n`, `1^k`, `(10)^k`, and short-lived blocks of period 13, 19 and 39. There are no halving chains like those of 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1LF. (scratch tools, see [the right end](#the-right-end-a-bouncer-over-long-blocks-lead-18-22-november-2026))
- **Most visits cross the digit list.** In 1,475 sampled intervals between right-end visits (every 7th visit, 10^8 to 9·10^8 steps) the head turned back in the left half of the visited tape 950 times; only the eat phase and a few others stay among the long blocks. So there is no closed visit-to-visit map yet: it would have to include the digit list.

**Open:**

- **Does it halt from blank tape?.** Not known. The macro configuration family has not been found; the right-end phases are understood only in part (the eat visit above).

## The proved neighbour (round 6)

The community tracker says: "The same table from another start is proved in busycoq. That proof fails or runs out
of memory from these starts." What we found, and what we tried:

- **Which machine.** `1RB0RF_0LC---_1LD1LC_1RE0LA_1RA1RD_0RD1LB`, proved non-halting in busycoq (`verify/CTLv2.v`,
  lemma `nonhalt17`, by `CPS_LRU 100000001 400000 400000 8 3200 2 6 0 0`). It is this table with left and right
  exchanged, started in this machine's state D (its states A, B, C, D, E, F are D, E, A, B, C, F here).
- **How the start differs** (Lean, kernel: `neighbour_start` in `lean/Neighbour.lean`). From blank tape in state D,
  three steps lead to state A on blank tape with a single 1 on the cell to its left. So the proved machine is this
  machine started on the tape `1 A>0` instead of `A>0`. The table is identical; every entry is used by both.
- **The neighbour's proof, reproduced** (trusted C++, `c/cpslru.cpp`, our own implementation of the search). The
  proof is a closed tape language: blocks of 8 cells; each side of the head summarised by its 2 nearest blocks and
  the list of up to 6 different blocks seen beyond; a set of such abstract configurations that contains the
  neighbour's configuration after some number of steps, is closed under the machine, and has no halt in it. For
  start D our search finds one with 4,091 abstract configurations from the configuration after 10^6+1 steps (about 4,035
  on the mirrored machine as busycoq states it, also from 10^7+1 and 10^8+1). From blank tape, or after 10^5
  steps, it does not close within 300,000 summaries: the neighbour's run has to settle first.
- **The same search from this machine's run** (trusted C++). After 10^8+1 steps with the neighbour's parameters,
  after 10^9+1 and 10^10+1 steps with ten parameter sets (blocks of 1 to 16 cells), and after 10^11+1 steps with
  two: never closed (more than 300,000 summaries or 6,000,000 abstract configurations; with blocks of one cell a
  halting abstract configuration is reached, which decides nothing).
- **What that rules out.** A closed set is the smallest one containing its start. If one of this machine's
  configurations at those four times were inside the neighbour's language, its closure would stay inside the
  neighbour's 4,091 configurations. It does not, so this run has not entered the part of the tape space the
  neighbour's theorem covers, up to 10^11 steps. It does not show that no closed language exists for this machine.
- **Why the runs differ** (observed). After 10^8 steps the neighbour's tape is long regular stretches (`1 0 0`
  repeated, and the 22-cell word `1^5 0 1 0^2 1^5 0^2 1 0^2 1 0^2` repeated); this machine's tape still has
  irregular blocks of 1s (one of 97) next to an irregular region of words `1 0` and `1 1 0`.
- **Other starts.** Two more holdouts are this table from the remaining starts:
  `1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1LD` (state B, mirrored) and `1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE1LC`
  (state C, mirrored). The same search from starts B and C, after 10^8+1 and 10^9+1 steps with parameters 8,2,6
  and 8,1,6, does not close either (`cpslru MACHINE 1000000001 300000 B - 8,2,6,0 8,1,6,0`, and `C`).

No proof was transferred. The decision stays open.

## The right end: a bouncer over long blocks (lead 18, 22 November 2026)

Lead 18 of the 22 November list asked to retarget lead 17's halving-chain engine (being built for
1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1LF) to this machine and to 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB0LF.
Neither needs it: 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB0LF already has an exact engine from busycoq PR 93 that has
run past 10^1336 steps, and this machine has no halving chains. What it has instead:

- **The digit list.** At left-end visits the tape left of the start is a list of digits `D n = 1 (11)^n 00`, PR 93's
  digit word, but irregular: 605 digits left of the start at 2.0·10^9 steps, almost all small, and one large one
  that grows (n = 302, then 354 at 2.6·10^9). The list goes on right of the start for several thousand cells, written
  with single 0s while the head is on the right.
- **The long blocks.** Right of the digit list the tape holds a few periodic blocks with counts in the thousands. In
  item notation at three times: `(1)^3396 (01011)^1379 H (001)^1403` (3.3·10^8 steps),
  `(10110)^201 (10)^3823 ~7 (110)^1274` (2.8·10^8), `(01011)^1229 (011)^5939 H` (4.8·10^8; H is the head). The block at the right end,
  `(100)^m` or `(110)^m` depending on the last sweep, takes the 3 cells the right end gains per visit (the count
  above), and every so often it is converted into the other blocks.
- **The eat phase, proved.** When the tape right of the list is `1^(a+3) (01011)^b (011)^c 0` and the head is in D
  on the blank cell after it, the head sweeps left over `(011)^c` (turning it into `(001)^c`) and `(01011)^b`,
  turns inside the block of 1s after eating three of them, and comes back, restoring `(011)^c` and appending two
  more copies. Lean proves the visit for all counts (`eat_visit`) and k visits in a row (`eat_iter`:
  k(20b + 10c + 15) + 10k² steps). In the run one such phase has b = 1,379 and a going from about 5,000 at 3.1·10^8
  steps to 171 at 3.84·10^8; 100 visits from step 304,257,913 take 2,892,500 steps, exactly as
  `eat_iter` says.
- **Other visits.** A catalogue of 1,475 sampled visits (symbolic simulation with `tools/py/bbtools/symtm.py` from
  each visit to the next, big runs made variables) found the eat rule and a handful of rules specific to one
  phase; 950 of the 1,475 intervals turned back in the left half of the tape, inside the digit list. Those visits
  depend on the digit list, so a visit-to-visit map has to carry it.
- **The halting route.** By `halt_route` (Route.lean) a halt needs C reading 0 with `1 0` on its left. C is entered
  only from B reading 0 (B0 = 1LC), and B reads a 0 coming from the right, so this is the leftward sweep in B
  stepping onto a 0 that has two more 0s and then a 1 on its left (`1 0 0 B<0`). The census (`c/route_census.c`)
  shows that inside the tape, in 10^10 steps, C read a 0 only with a 1 next to it: whenever B steps left onto a 0,
  at most one more 0 lies before the next 1.

Next steps: decode the digit list's update rule (it is PR 93's counter with the collision changed, see below) so that
the long visits become a map; with the eat phase that would give a visit-level accelerator. `c/mm2.cpp` is exact but
gains only a factor of 2 to 4 because the digit list does not compress.

## Round by round: walls, blocks and two right ends (22 November 2026)

Decoding how the irregular digit list changes from one right-end visit to the next. At rest (each time the head
reaches a new rightmost cell) the tape right of the left-end digits is almost entirely made of S-blocks
`S_n = 1 (01)^(n+1)`, the digits of the list. What is not an S-block is one of three things: a **wall**, a run of
4 or more 1s; a run of exactly three 1s; or a leftover `D_0 = 100`. A visit only ever works on the part of the tape
right of the rightmost such feature (the *chamber*), and what it does is fixed by that feature:

- **Sweeps.** The left sweep turns each S-block into the D-block `D_n = 1 (11)^n 00` of the same length
  (`sweep_left`: `L S_n <C 1 R` reaches `L <C 1 D_n R` in 2n+5 steps); the right sweep turns it back
  (`sweep_right`: `L 1 B> 1 0 0 D_n R` reaches `L S_n 1 B> 1 0 0 R` in 8n+5 steps). So the blocks of the chamber
  come back unchanged.
- **Wall turn.** At a wall the sweep turns and uses up three 1s (`wall_turn`: `L 1^(k+3) <C 1 D_n R` reaches
  `L 1^k S_n 1 B> 1 0 0 R`). A wall of exactly three 1s, `0 111 (01)^(m+1)`, becomes `00 1 (01)^m`
  (`wall3_turn`); that is where the leftover `100`s come from. A wall of length 1 or 2 mod 3 dissolves into ordinary
  block boundaries when it runs out, and the chamber merges with the one on its left.
- **Two right ends.** In regime I the last block is followed by a gadget `101100 (110)^c`: a long visit makes the
  last block S_(n+3) and the gadget `101101`, and the next visit is a short one that turns inside the gadget and
  adds one `110` (`round_I`, `short_I`; seen around 2.8·10^8 steps, with n near 3,770). In regime II the tape ends
  `S_n (011)^c 0`, every visit is long, the last block grows by one and two copies of `011` are added (`round_II`;
  this is the eat visit of `VisitRules.lean` with a general chamber).

`lean/RoundRules.lean` (written by `py/round_rules.py`: nine single-block rules by `tools/py/bbtools/symtm.py`,
then induction over the list of blocks) proves these rounds for **every** chamber: `round_I`, `short_I`,
`roundpair_I` and `rounds_I` (k rounds in a row: the wall loses 3k ones, the last block gains 3k, the gadget k copies
of 110), `round_II`, and `round_I3` / `round_II3` for a wall of three 1s.

Checked against the run with `py/round_check.py` (tapes from `c/vdump.c`), every consecutive pair of visits in three
windows:

| window (steps) | visits | wall | wall of 3 | short | leftover 100 | predicted exactly |
|---|---|---|---|---|---|---|
| 1·10^8 – 2·10^8 | 1,423 | 575 | 228 | 324 | 295 | 1,127 |
| 2.8·10^8 – 4.2·10^8 | 2,492 | 2,085 | 112 | 129 | 165 | 2,326 |
| 4·10^9 – 4.05·10^9 | 230 | 92 | 62 | 0 | 76 | 154 |

Every visit at a wall, a wall of three or the gadget is predicted cell for cell (3,607 of 4,145, 87%); the two
visits left over are regime changes. **The one case without a rule is a visit that meets a leftover `100`.** There
the left sweep is reflected early (`S_(m+1) 100 <C 1` turns into `S_m 0101 11 A>`, state A instead of the right
sweep's B), and the A run glues the D-blocks it passes into long runs of 1s: these are the new walls (lengths like
15, 22, 27 and 34 at 2.8·10^8 steps) that the following rounds wear down three at a time. So the digit list is a
stack of walls, each worn down by the visits that reach it, and the leftover 100s left when a wall of length 0 mod 3
runs out are what rebuild new walls. A halt needs `1 0 0 B<0` (three 0s met by the left sweep); at rest the only
00s are the leftover 100s (D-blocks exist only during a sweep), so the question is now whether a visit at a leftover
100 can ever put a third 0 next to one.

Next steps: the rule for a visit at a leftover 100 (it depends on how many D-blocks the A run reaches and glues),
which would make the whole list a map.

## Reproduce

From the repository root:

```sh
. /etc/profile.d/lean.sh      # after scripts/setup-lean.sh
holdouts/1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE/lean/check.sh
gcc -O2 -o triage tools/c/triage.c && ./triage 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE 1000000000
gcc -O2 -o tmrun tools/c/tmrun.c && ./tmrun 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE 10000000000
cd tools/py && python3 -m bbtools.ctl 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE 5
gcc -O2 -o rvisits holdouts/1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE/c/rvisits.c && ./rvisits 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE 2000000000 50
python3 holdouts/1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE/py/visit_rules.py   # rewrites lean/VisitRules.lean
python3 holdouts/1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE/py/round_rules.py   # rewrites lean/RoundRules.lean
gcc -O2 -o vdump holdouts/1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE/c/vdump.c && ./vdump 280000000 420000000 1 > vd.txt
python3 holdouts/1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE/py/round_check.py vd.txt   # 2,326 of 2,492 visits exact
gcc -O2 -o route_census holdouts/1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE/c/route_census.c && ./route_census 10000000000
g++ -O2 -std=c++17 -o mm2 holdouts/1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE/c/mm2.cpp && ./mm2 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE 15 12
g++ -O2 -std=c++17 -o cpslru holdouts/1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE/c/cpslru.cpp
./cpslru 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE 1000001 300000 D - 8,2,6,0          # the neighbour's start: CLOSED
./cpslru 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE 1000000001 300000 A - 8,2,6,0 8,1,6,0   # this machine: toobig
```

## Deciders tried (F11, 13 November 2026)

None closes. Each reaches a halting configuration in its abstraction, which says nothing about halting.

- n-gram CPS (`tools/c/ngramcps.c`), equal widths on both sides: a halting local configuration is reached with plain up to width 15, history 1 up to width 14, history 2 up to width 12, history 3 up to width 11, LRU history up to width 4 (larger widths ran out of the 150 s or 60 million configuration budget).
- n-gram CPS with every cell tagged by its position mod p: fails for p = 2 up to width 12, p = 3 up to width 12, p = 4 up to width 12, p = 6 up to width 12.
- n-gram CPS where each side also carries the state of a small automaton that has read that side from the far end (every automaton with up to 3 states on both sides, or 4 states on one side), with position mod 1..4 and widths 4, 6, 8: no closed set without a halt in all 120 parameter sets.
- Run-length windows (the K nearest runs of equal macro cells on each side, run lengths kept exactly below T and mod M above): fails for all 72 parameter sets (cells of 1 to 4 bits, K = 2, 4, 6, T = 2, 4, M = 1, 2, 4).
- Two-automaton closed tape language by SAT (a deterministic automaton reading each side inward, n states each, CaDiCaL): no solution for n = 2..7; n = 8 not finished in 150 s.

## Where a halt can come from

`lean/Route.lean` (kernel, written by `py/route.py`): `halt_route`, two steps before any halt the machine is in one
of: C with 1 two left, 0 left, 0 under the head.

## PR 93's engine on this table (22 November 2026)

**Result: the engine does not carry over.** The question stays open; no halt was found.

- **The table.** Exchange the names E and F, and replace the detour D0 `1LE`, E0 `0RA`, A1 `1RA` by the single step
  `1RA`. The detour ends in the same configuration unless the cell left of D is 1, where the machine halts. The table
  becomes G = `1RB1RA_1LC0RD_1LD1LB_1RA0LE_0LB1RF_0RA---`. That is T4 = `1RB1RA_1LC0RD_1LD1LB_1RA0LE_0LB0LF_0RA---`
  with one transition changed, E1. T4's E1 is `0LF`, which erases the 1 and steps left; G's is `1RF`, which keeps
  it and steps right. T4 is the table of `tools/coq/t4engine`, DeepMind's busycoq PR 93 engine retargeted, which
  proved 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB0LE halts. E is entered only by D1 (`0LE`), so F then reads the 0
  that D has just written and goes on with F0 `0RA`; the halting F1 is never reached that way. **This machine halts
  exactly when G's run from blank tape has D reading 0 with a 1 on its left** (the same fact as `halt_route` below).
- **The rules.** PR 93's engine works with `CfgR l r = l A> 0100 r`, `CfgL l r = l <B 1 r`,
  `CfgJ l r = l <C 100 r` and the digit words `D n = 1 (11)^n 00`. Of its 18 basic rules, 14 hold here unchanged
  (direct simulation, counts up to 4, random tape around). The four that end in `CfgJ` are the ones that pass through
  E1. Here the head turns right at E1 and runs on into the tape beyond the rule: for example, collision
  `CfgL (l 101100) r` reaches A on the first cell of `r`, with `1010111` behind it. Only collide stays local
  (`CfgR l (10 D0 D0 r)` reaches `CfgL l (D1 D1 1 r)`). Lean proves 8 of the rules, the changed ones included
  (`lean/EngineRules.lean`, written by `py/engine_rules.py`). In none of the 18 rules does D read 0 next to a 1.
- **So there is no engine to retarget.** PR 93's engine rests on calls that return to the left within a few digits,
  batched by counting. Here every collision sends the head back to the right, which matches the irregular `10`/`110`
  region on the right of the tape (section above). A new engine would have to start from this machine's own
  structure.
- **Direct run.** The C simulator `tools/c/tmrun.c` runs 10^12 steps from blank tape without a halt; the tape then
  holds 451,383 ones (`tmrun 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE 1000000000000`, about an hour).
- **Accelerated runs.** `rsim.py` (validated against direct simulation at 4 points up to 10^9 steps) reaches only
  2.7·10^9 steps in 10 minutes: its jumps rarely apply. `tools/py/bbtools/rleaccel_rec.py` stalls near 10^8 steps.

The same table from other starts: 1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1LD (start B),
1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE1LC (start C) and the busycoq-proved non-halting
1RB0RF_0LC---_1LD1LC_1RE0LA_1RA1RD_0RD1LB (start D, section above).

## Pages

- [`pages/holdouts/1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE/explainer.html`](../../pages/holdouts/1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE/explainer.html)
- [`pages/holdouts/1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE/proof-status.html`](../../pages/holdouts/1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE/proof-status.html)

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1LD`](../1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1LD/README.md): rename A→E, B→A, C→B, D→C, E→D, F→F and exchange left and right; it is this table started in state B, in a mirror
- [`1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE1LC`](../1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE1LC/README.md): rename A→D, B→E, C→A, D→B, E→C, F→F and exchange left and right; it is this table started in state C, in a mirror

<!-- end of related machines -->
