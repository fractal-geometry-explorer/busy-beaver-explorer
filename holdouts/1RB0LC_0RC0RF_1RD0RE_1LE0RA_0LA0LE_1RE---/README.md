# 1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1RE---

bbchallenge id 69987. One of the six-state holdouts whose halting from blank tape is open. Group G01.
**Family:** Nested block counter (core 1RB0LC_0RC0RB_1LD0RE_0LE?LF_1LA0LB, frames A/B/X). The shared analysis code is in [`holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---`](../1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---/) (`py/`, `c/`).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LC |
| B | 0RC | 0RF |
| C | 1RD | 0RE |
| D | 1LE | 0RA |
| E | 0LA | 0LE |
| F | 1RE | --- |

## What it does

This machine is in **frame B**: its table is the mirror image (L and R exchanged) of the frame-A table `1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LB---` with the states renamed A->D, B->E, C->A, D->B, E->C, F->F, and it starts where that machine would be in state C. So its run from blank tape is, step for step and mirrored, the run of `1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LB---` started in C (checked from the two tables by `frames.py`, and by simulation). Below, states are named as in frame A; the F-transition of the analysis is this machine's B1, the halting state is F.

**Same run, except for two steps at each F-event, as [1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_1LD---](../1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_1LD---/README.md).** The two tables differ in B1 (0RF / 1RF) and F0 (1RE / 1LD); from an F-event they reach the same configuration after the same number of steps, given a 0 next to the cell F reads (true at every F-event of the run), so the runs agree at every step except the two steps of each F-event (8 of the first 10^7 steps, `holdouts/related.json`).

All 14 machines of the family share this five-state core (frame A: `1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_?---`):

| machine | frame | F0 in frame A | D1 | frame-A start | F-events to 10^11 |
|---|---|---|---|---|---|
| [1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---](../1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---/README.md) | A | 0RA | 0LF | A | 13 |
| [1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RB---](../1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RB---/README.md) | A | 0RB | 0LF | A | 7 |
| [1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RE---](../1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RE---/README.md) | A | 0RE | 0LF | A | 8 |
| [1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LB---](../1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LB---/README.md) | A | 1LB | 0LF | A | 8 |
| [1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LC---](../1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LC---/README.md) | A | 1LC | 0LF | A | 5 |
| [1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1RA---](../1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1RA---/README.md) | A | 1RA | 0LF | A | 4 |
| [1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_0LD---](../1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_0LD---/README.md) | B | 0RA | 0LF | C | 13 |
| [1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_0LE---](../1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_0LE---/README.md) | B | 0RB | 0LF | C | 7 |
| [1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_0RA---](../1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_0RA---/README.md) | B | 0LC | 0LF | C | 5 |
| [1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1LD---](../1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1LD---/README.md) | B | 1RA | 0LF | C | 4 |
| [1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1RA---](../1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1RA---/README.md) | B | 1LC | 0LF | C | 5 |
| **1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1RE---** | B | 1LB | 0LF | C | 8 |
| [1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_1LD---](../1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_1LD---/README.md) | B | 1RA | 1LF | C | 8 |
| [1RB---_0LC0LB_1RF0LD_1RE0RB_1LB0RC_0RD1RA](../1RB---_0LC0LB_1RF0LD_1RE0RB_1LB0RC_0RD1RA/README.md) | X | 1LB | 1LF | F | 6 |

Related holdouts with the same core but a different D1 or F0 (another group): `1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0LC---`, `1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0LE---`, `1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LA---`, `1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_1LB---`, `1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_0RC---`, `1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_0LA---`.

### Blocks and rounds

In frame A, away from rare moments, the tape is a list of blocks `(10)^b` separated by single 1s. At an *event*
the head is in state A on a 0 right after moving left, and the tape is

    0^inf (1000)^q  tail  A> 0 (10)^b_j 1 (10)^b_(j+1) 1 ... (10)^b_k 1 0^inf

where the blocks left of the head are *spread* as `(1000)^q` and the tail is in one of five phases
`10, 1, 1001, 101, 11`. A *round* runs right over the plain blocks (B: six steps per `1010`, which becomes
`0100`) and back (E, A, C, D: four steps per `1000`). A round on blocks j..k contains five rounds on blocks
j+1..k, so the blocks form a nested counter in base 5. A round on the last m blocks advances the tail one phase and
changes the blocks by (u is about half a block value, the theorems state the exact offsets)

| m | change | steps | proved |
|---|---|---|---|
| 1 | (+2) | 10u+59 (+53 from phase 1) | Lean kernel (`round_m1_p*`) |
| 2 | (-4, +12) | 10u0+50u1+485 (+469 from phase 1) | Lean kernel (`round_m2_p*`) |
| 3 | (-4, -18, +60) | 10u0+50u1+250u2+8455 (+8439 from phase 1) | Lean kernel (`go_spec`, `go_closed`) |
| m | (-4, -18, -90, ..., -18·5^(m-3), +12·5^(m-2)) | about sum 5^i b_i | Lean kernel, every m (`go_spec`, `go_closed`) |

(from phase 1 of the tail the first block gets 2 more). After five phases a `1000` of the spread block on the left is
used up: that is how the deeper block counts down.

Checking consecutive events of the run against this rule (`c/family.c events` + `py/check_rounds.py`): 9,922 events in 10^8 steps; transitions: same 4,779, same* 1,559, down 1,944, up1 1,279, up2 256, up3 45, up4 11, up5 1, X 47.
`same`/`same*` is one round, `upN` a round after which N more blocks are visible, `down` a block finished; the
exceptions `X` are the left end, the birth of a new last block, the merges after a block runs out, and F-events.

### Visits: the run as a map on block lists

A *visit* starts when the head, in state A after a move left, reads the 0 in front of plain blocks

    A> 0 (10)^b1 1 (10)^b2 1 ... (10)^bk 1 0^inf

and ends when the head first steps left of that cell. It never reads the tape on its left, so its result depends
only on the list l = [b1, ..., bk]: an exit state, a short prefix and a new list. In `lean/Family.lean` (generated
by `holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---/py/gen_family_lean.py` from the template `py/family_generic.lean`; all frame A, then carried to this
machine by the conjugacy) the pieces are:

- seven tape rules proved by bbtools.symtm for all counts: PUSH `(2k+3)::(c+1)::R` spreads the first block
  (6k+15 steps), TURN `[2k+1] -> [2k+2]` (10k+14), TAIL1..TAIL4 move the tail of the spread block one phase
  (first block +3, +1, +1, +1; 9, 15, 15, 15 steps), POP folds a spread block of phase 5 back into the plain block
  2q+2 (4q+9), BIRTH `[2k+4] -> [2k+2, 8]` (10k+188);
- `go n l`, `goT n l`, `clean n l`: the recursion `go (b::c::bs) = (b-5) :: go l4` with `l0 = (c+1)::bs`,
  `l1 = bump3 (go l0)`, `l2..l4 = bump1 (go ...)`, and `go [b] = [b+1]`; `clean` (decidable) asks every spread block
  to be odd and >= 7 and every second block nonempty;
- **`go_spec`** (induction on the depth n, every left context L):
  `steps (goT n l) (L, 0 enc l, A) = some (L, 1 0 enc (go n l), E)` for every clean l;
- **`go_closed`** / `visit_closed`: if b1 is odd >= 7, the later blocks even, the last >= 2 and block i >= 2 +
  18·5^(i-2) for the middle ones, the visit is clean and gives (b1-5, b2-18, b3-90, ..., bk + 12·5^(k-2)) (a single
  odd block: b1+1); the step count is sum 5^(i+1) b_i + K_k with K = 9, 265, 4245, 91645, ... (`py/cf.py`, checked
  against the recursion, trusted);
- `round1..round4` (a visit and then a tail phase: the round rule of the table above), `birth`, `fevent`,
  `fevent_reads_zero`; `halts_iff` and `visit` for this machine's own table.

Every other visit (a small or even first block, a block that runs out and merges, the left end) is not a closed rule
yet but is still a function of the list. `py/hybrid.py` runs the machine as this map: clean visits by the closed
form, every other visit by the exact run-length simulator, recursively (visits inside visits) and memoised. Against
the direct run (`data/trajectory.json`, 100,000,012,844 steps) it reproduces all 19
left-end events and all 8 F-events exactly.
It then runs to **1.4·10^100 steps** in 17 s (`data/hybrid.json`): 256 left-end
events, 128 F-events, no halt.
The list grows to about 40 blocks, block i of size about 5^i; most visits are clean.

### The left end

Each return of the head to the left end of the tape starts a round on the whole list and adds 3 cells on the left.
The block lists at these moments (from `data/trajectory.json`, 100,000,012,844 steps):

| step | cells left of start | blocks |
|---|---|---|
| 3 | 3 | `[1]` |
| 22 | 6 | `[4]` |
| 215 | 9 | `[4, 8]` |
| 1,241 | 13 | `[32]` |
| 1,574 | 16 | `[32, 8]` |
| 5,775 | 19 | `[28, 16, 44]` |
| 224,326 | 22 | `[22, 114, 502]` |
| 379,165 | 25 | `[22, 96, 412, 296]` |
| 2,003,732 | 28 | `[22, 78, 318, 832, 524]` |
| 11,569,851 | 31 | `[22, 60, 228, 380, 2978]` |
| 63,682,358 | 34 | `[22, 42, 136, 1022, 5946, 1370]` |
| 211,329,995 | 37 | `[22, 24, 46, 572, 3694, 11234]` |
| 706,424,290 | 40 | `[22, 346, 2488, 5204, 20096]` |
| 827,760,155 | 43 | `[22, 328, 2398, 4754, 17846, 7496]` |
| 1,856,912,248 | 46 | `[22, 310, 2308, 4304, 15592, 21232, 12524]` |
| 25,534,637,563 | 49 | `[22, 292, 2218, 3854, 13342, 149800]` |
| 29,293,100,816 | 52 | `[22, 274, 2128, 3404, 11092, 138550, 37496]` |
| 52,072,794,321 | 55 | `[22, 256, 2038, 2954, 8842, 127298, 137570]` |
| 99,172,296,662 | 58 | `[22, 238, 1948, 2504, 6592, 116048, 81320, 187496]` |

Between left-end events b2 drops by 18, b3 by 90, b4 by about 450 (the closed form seen from the top: the
first block at the left end is even, so the top-level visit itself is unclean and simulated), while the last block
is born or grows; when a block runs out the list shortens and the neighbours merge. Values such as 296, 524, 1136, 37496 recur across the family: they are
fixed outcomes of a block being born.

### The halting condition

F is entered only by D1 = 0LF (frame A). F1 halts; F0 = 1LB (frame A) continues. In 100,000,012,844 steps there are
8 F-events, at steps 40,899, 85,789, 186,779, 5,488,816, 58,562,180, 58,883,038, 88,992,586, 47,968,870,404; in the 1.4·10^100 steps of the exact map there are 128,
all reading 0, with surroundings `010001000100[F]001010101010` (110x); `010001000100[F]001010110101` (18x).

Every one of them is the same mechanism: an unclean visit exits in state C (prefix `0`) onto the 0 of a phase-1 tail
`10`; C0 = 1LD writes 1 and moves onto the tail's 1, D1 enters F one cell further left, and F reads the last cell of a
`1000` (or of the `100` in front of the spread block). `fevent` and `fevent_reads_zero` prove that this cell is 0
for every q and every tape around, so this kind of F-event can never halt. A halt needs another kind: a visit that
exits into F itself, or a C exit onto a different tail. Started from random block lists the machine does halt (about
one F-entry in 150; `[15, 31, 17, 59, 31]` halts after 63,153 steps, `py/random_lists.py`), so whether the blank-tape
run stays clean is a real question.

## What is established

| level | claim | where |
|---|---|---|
| kernel | **The halting configurations.** The machine stops exactly when it reads the symbol of a halting transition (F1); the generated statement covers every configuration. | `step_none_iff`, `lean/Blank.lean` |
| kernel | **No halt in the first 10,000 steps.** The list simulator of the shared library, proved to agree with the machine's semantics, runs 10,000 steps from blank tape without a halt, evaluated by Lean's kernel. | `blank_runs_kernel`, `lean/Blank.lean` |
| native | **No halt in the first 10^7 steps.** The same run, evaluated by compiled code. | `blank_runs_native`, `lean/Blank.lean` |
| trusted | **No halt in the first 10^9 steps.** The C simulator `tools/c/triage.c` runs 10^9 steps without a halt; at the end 79,557 cells have been visited and 24,018 of them hold a 1. | `holdouts/triage.json` |
| trusted | **One of 14 machines with the same five-state core.** States A to E of every machine of the family are the core 1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_?--- (in frame A); the machines differ in F0 and the start state, and some are mirror images. This one is the mirror image of `1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LB---`, renamed, started in its state C. | `holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---/py/frames.py`, `py/conjugacy_steps.py` |
| trusted | **Same run, except for two steps at each F-event, as 1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_1LD---.** The two tables differ in B1 (0RF / 1RF) and F0 (1RE / 1LD); from an F-event they reach the same configuration after the same number of steps, given a 0 next to the cell F reads (true at every F-event of the run), so the runs agree at every step except the two steps of each F-event (8 of the first 10^7 steps, `holdouts/related.json`). Checked on tape snapshots to 2·10^8 steps. | `holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---/c/family.c snapshot` |
| kernel | **The visit rule for every depth.** A *visit* starts with the head in state A on the 0 in front of plain blocks `(10)^b1 1 (10)^b2 1 … 1` and ends when it first steps left of that cell; it never reads the tape on its left. `go_spec` proves, by induction on the depth n and for every left context, that a *clean* visit (a decidable condition: every block it spreads is odd and ≥ 7, every second block nonempty) turns the list l into `go n l` in exactly `goT n l` steps, where `go` is the recursion: spread b1, five visits to [b2+1, b3, …] with the tail bumps +3, +1, +1, +1 between them, then b1−5. It is built from seven rules (PUSH, TURN, TAIL1–4, POP) proved by bbtools.symtm for all counts. | `go_spec`, `push` … `pop`, `lean/Family.lean` |
| kernel | **Its closed form.** `go_closed`: if b1 is odd and ≥ 7 and the later blocks are even, the last ≥ 2 and block i (i = 2..k−1) ≥ 2 + 18·5^i−2, then the visit is clean and gives (b1−5, b2−18, b3−90, …, bk−1−18·5^k−3, bk+12·5^k−2) (a single odd block gains 1); `visit_closed` states it on the tape. With the tail bump after the visit this is the measured round rule (−4, −18, …, +12·5^m−2) for every m. | `go_closed`, `visit_closed`, `lean/Family.lean`; closed step count in `holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---/py/cf.py` (trusted) |
| kernel | **Rounds, births and the F-event.** `round1`–`round4`: a clean visit followed by one phase of the tail on its left. `birth`: a visit to a single even block [2k+4] gives [2k+2, 8] in 10k+188 steps (where new blocks come from). `fevent` and `fevent_reads_zero`: the only way into F seen in the runs (a C exit onto the 0 of a phase-1 tail, then C0, D1) makes F read the last cell of a `1000` or of `100`, which is 0 for every q and every tape around. | `round1` … `birth`, `fevent_reads_zero`, `lean/Family.lean` |
| kernel | **The rules hold for this machine's own table.** The rules are proved on the frame-A table `FA.trans`. This machine is its mirror image: the map `img` (mirror the tape, rename the states) sends every frame-A step to a step of this machine (`step_img`, `steps_img`); `halts_iff` says that this machine halts from blank tape iff the frame-A table halts from blank in state C, and `visit` restates `go_spec` for this machine. | `halts_iff`, `visit`, `lean/Family.lean` |
| kernel | **The round rule on one and two blocks (first pass).** Eight theorems on the machine's own table: a round on the last block changes it by +2 (+4 from phase 1), on the last two by (−4, +12), for each phase, with exact step counts. Now special cases of the rules above. | `round_m1_p1` … `round_m2_p4`, `lean/Rules.lean` |
| trusted | **The events follow the round rule.** Listing every event (A turning right with plain blocks on its right) and comparing consecutive ones: 9,922 events in 10^8 steps; transitions: same 4,779, same* 1,559, down 1,944, up1 1,279, up2 256, up3 45, up4 11, up5 1, X 47. The few exceptions (X) are the left end, the birth of a new last block, the merge after a block runs out, and the F-events. | `holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---/c/family.c events`, `holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---/py/check_rounds.py` |
| trusted | **No halt in the first 10^11 steps.** The exact run-length simulator (macro steps over `(10)^n`, `(1000)^n`, checked against plain simulation) runs 100,000,012,844 steps from blank tape without a halt. It meets 19 left-end events and 8 F-events (first at step 40,899), and at every F-event the cell F reads is 0. | `data/trajectory.json`, `holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---/py/trajectory.py` |
| trusted | **The whole run as an exact map on block lists.** `hybrid.py` runs the machine as a map on block lists: clean visits by the closed form (a theorem), every other visit (small or even first blocks, merges after a block runs out, births, the left end) by the exact run-length simulator, recursively and memoised. It is exact, not a model: against `data/trajectory.json` (100,000,012,844 steps of the machine) it reproduces all 19 left-end events (step and block list) and all 8 F-events (step and cell read). | `holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---/py/hybrid.py`, `holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---/py/hybrid_run.py`, `data/hybrid.json` |
| trusted | **No halt in the first 1.4·10^100 steps.** The exact map runs 1.4·10^100 steps (17 s): 256 left-end events, 128 F-events, every one reading 0 and every one of the proved kind (`010001000100[F]001010101010` (110×); `010001000100[F]001010110101` (18×)). The block list grows to about 40 blocks, block i of size about 5^i. | `data/hybrid.json` |
| heuristic | **Where a halt would have to come from.** F is entered only by D1 (D reads a 1 during the left sweep, where a spread block is turned back), and halts only when it then reads a 1. In this run every F-event has the same clean context (`010001000100[F]0010101` (8×)). Random block lists do reach a halting F-event (about 1 in 150 F-entries; e.g. `[15, 31, 17, 59, 31]` halts after 63,153 steps), so the halt is reachable in principle; whether the blank-tape run ever produces such a list is the open part. F-events get rarer as the blocks grow (the top-level round time grows about fivefold per block). | `holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---/py/random_lists.py` |
| open | **Does it halt from blank tape?.** Not known. The visit rule is proved for every depth, its closed form, births and the F-event too; what is missing is a proof that the unclean visits of the blank-tape run (merges, small first blocks, the left end) always end in a C exit of the proved kind and never in an F exit onto a 1, that is an invariant on the block lists reached from blank tape. | README.md, Further work |
| heuristic | **Growth shape: exp/sqrt.** Left of the start, the visited part of the tape grows like the square root of the step count, the signature of a head sweeping back and forth across the whole tape and adding a cell or a few at the end of each sweep (a *bouncer*-like shape) (fitted exponent 0.499). Right of the start it grows like the logarithm of the step count: each new cell costs a roughly constant factor more time, the signature of a *counter* or of a Collatz-like map whose values are written on the tape (fitted exponent 0.057). | `tools/py/bbtools/triage.py` |

## Reproduce

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1RE---/lean/check.sh          # Blank.lean + Rules.lean + Family.lean
python3 holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---/py/gen_family_lean.py 1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1RE--- H69987 > holdouts/1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1RE---/lean/Family.lean
python3 holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---/py/cf.py                                       # closed form vs the recursion
python3 holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---/py/hybrid_run.py 1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1RE--- 1e100                     # exact block-list map, checked against trajectory.json
cd tools/py && python3 ../../holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---/py/gen_lean.py 1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1RE--- H69987 > ../../holdouts/1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1RE---/lean/Rules.lean
python3 holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---/py/frames.py                                   # the 14 tables are conjugate as claimed
python3 holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---/py/conjugacy_steps.py 1e6                      # and the runs agree step by step
python3 holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---/py/trajectory.py 1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1RE--- 1e11 holdouts/1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1RE---/data/trajectory.json
cc -O2 -o family holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---/c/family.c
./family events 1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LB---:C 1e8 > ev.txt && python3 holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---/py/check_rounds.py ev.txt
./family enter 1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1RE--- 1e9 F                                 # the F-events, with the cells around them
```

## Further work

- Done in the second pass: the round rule for every depth (`go_spec`), its closed form (`go_closed`), births and the
  F-event in Lean; the exact block-list map (`hybrid.py`).
- Write the unclean visits as closed rules too (merge `[3, y, ...]` exits C with `[y-1, ...]`; visits with an even
  or small first block; the left end with first block 6 or 8). There are many cases, because an unclean visit
  contains clean and unclean visits at every depth.
- Nonhalting needs an invariant on the reachable block lists showing that every unclean visit ends with a B, A or C
  exit and every C exit lands on a phase-1 tail (the proved harmless F-event), never an F exit onto a 1. The list
  entries are large and grow like 5^i, so a parity/size invariant per depth is the natural candidate; none has been
  found yet.
- The closed step count (`cf.steps`) is checked against `goT` in Python, not proved in Lean.

<!-- F05 -->

## Family F05: one core, forty machines

This machine is one of 40 holdouts with the same five states. In frame A all of them are `1RB0LC_0RC0RB_1LD0RE_0LE?LF_1LA0LB_??---`: they differ in D1 (0LF or 1LF), in F0 and in the start state. This one is the mirror image of `1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LB---` with the states renamed A->D, B->E, C->A, D->B, E->C, F->F (frame B), started in that table's state C. `lean/Family.lean` proves it (`step_img`, `halts_iff`: the machine halts from blank tape iff `1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LB---` halts from blank tape in state C).

Shared by all 40 and proved in Lean on each machine's own frame-A table (`lean/Family.lean`, written by `holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---/py/gen_family_lean.py`):

- `go_spec`: the visit rule for every depth (a clean visit to [b1, ..., bk] makes five visits to the list without b1);
- `go_closed`, `visit_closed`: its closed form (b1-5, b2-18, b3-90, ..., bk+12·5^(k-2));
- `visit_conserves` (new): a clean visit conserves, for the blocks after the first and before the last, the residue of block i modulo 18·5^(i-2) and the drift b(i+1) - 5·b(i);
- `birth`, `fevent`, `fevent_reads_zero`: the birth of a block, and the harmless entry into F.

**Run (trusted).** The exact block-list map (`holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---/py/f05_run.py`, `hybrid.py`) reaches step 5.4·10^200 without a halt: 520 returns to the left end, 292 entries into F, all reading 0, tape around the head `010001000100[F]001010101010` (241x); `010001000100[F]001010110101` (51x). Its F-events agree with the plain simulation on the first 3e+09 steps (7 F-events). Summary and the first 80 left-end block lists: `data/f05_run.json`.

**Drifts (observed, at left-end events only).** Smallest |b(i+1) - 5·b(i)| after step 10^20: 1596384; after step 10^100: 1596384. Halting would need a drift near 0 at the moment its block runs out (two exceptional events close together); nothing proved excludes that, so the question stays open.

The (D1, F0) variants and their machines (runs marked with the same letter had the same block list at their last left-end event, observed):

| D1 | F0 | machine | frame | frame-A start | same run | exact block-list map |
|---|---|---|---|---|---|---|
| 0LF | 0LC | [`1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_0RA---`](../1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_0RA---/README.md) | B | C |  | no halt in 10^200 steps, 214 F-events, all reading 0 |
| 0LF | 0LC | [`1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0LC---`](../1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0LC---/README.md) | A | A |  | no halt in 10^200 steps, 199 F-events, all reading 0 |
| 0LF | 0LC | [`1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0RD---`](../1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0RD---/README.md) | G | E |  | no halt in 10^200 steps, 223 F-events, all reading 0 |
| 0LF | 0LE | [`1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0LE---`](../1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0LE---/README.md) | A | A |  | no halt in 10^200 steps, 214 F-events, all reading 0 |
| 0LF | 0LE | [`1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_0RC---`](../1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_0RC---/README.md) | B | C |  | no halt in 10^200 steps, 251 F-events, all reading 0 |
| 0LF | 0LE | [`1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0RA---`](../1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0RA---/README.md) | G | E |  | no halt in 10^200 steps, 232 F-events, all reading 0 |
| 0LF | 0RA | [`1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---`](../1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---/README.md) | A | A |  | no halt in 10^200 steps, 278 F-events, all reading 0 |
| 0LF | 0RA | [`1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_0LD---`](../1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_0LD---/README.md) | B | C |  | no halt in 10^200 steps, 278 F-events, all reading 0 |
| 0LF | 0RA | [`1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0LB---`](../1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0LB---/README.md) | G | E |  | no halt in 10^200 steps, 245 F-events, all reading 0 |
| 0LF | 0RB | [`1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RB---`](../1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RB---/README.md) | A | A |  | no halt in 10^200 steps, 200 F-events, all reading 0 |
| 0LF | 0RB | [`1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_0LE---`](../1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_0LE---/README.md) | B | C |  | no halt in 10^200 steps, 200 F-events, all reading 0 |
| 0LF | 0RB | [`1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0LC---`](../1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0LC---/README.md) | G | E |  | no halt in 10^200 steps, 184 F-events, all reading 0 |
| 0LF | 0RE | [`1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RE---`](../1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RE---/README.md) | A | A |  | no halt in 10^200 steps, 292 F-events, all reading 0 |
| 0LF | 0RE | [`1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0LA---`](../1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0LA---/README.md) | G | E |  | no halt in 10^200 steps, 265 F-events, all reading 0 |
| 0LF | 1LA | [`1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LA---`](../1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LA---/README.md) | A | A |  | no halt in 10^200 steps, 214 F-events, all reading 0 |
| 0LF | 1LB | [`1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LB---`](../1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LB---/README.md) | A | A |  | no halt in 10^200 steps, 292 F-events, all reading 0 |
| 0LF | 1LB | **`1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1RE---`** | B | C | a | no halt in 10^200 steps, 292 F-events, all reading 0 |
| 0LF | 1LB | [`1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_1RC---`](../1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_1RC---/README.md) | G | E |  | no halt in 10^200 steps, 265 F-events, all reading 0 |
| 0LF | 1LC | [`1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LC---`](../1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LC---/README.md) | A | A |  | no halt in 10^200 steps, 192 F-events, all reading 0 |
| 0LF | 1LC | [`1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1RA---`](../1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1RA---/README.md) | B | C |  | no halt in 10^200 steps, 192 F-events, all reading 0 |
| 0LF | 1LC | [`1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_1RD---`](../1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_1RD---/README.md) | G | E |  | no halt in 10^200 steps, 197 F-events, all reading 0 |
| 0LF | 1RA | [`1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1RA---`](../1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1RA---/README.md) | A | A |  | no halt in 10^200 steps, 240 F-events, all reading 0 |
| 0LF | 1RA | [`1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1LD---`](../1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1LD---/README.md) | B | C |  | no halt in 10^200 steps, 240 F-events, all reading 0 |
| 0LF | 1RA | [`1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_1LB---`](../1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_1LB---/README.md) | G | E |  | no halt in 10^200 steps, 287 F-events, all reading 0 |
| 1LF | 0LB | [`1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_0LB---`](../1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_0LB---/README.md) | A | A |  | no halt in 10^200 steps, 209 F-events, all reading 0 |
| 1LF | 0LB | [`1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_0RE---`](../1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_0RE---/README.md) | B | C |  | no halt in 10^200 steps, 192 F-events, all reading 0 |
| 1LF | 0LB | [`1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA1RF_0RC---`](../1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA1RF_0RC---/README.md) | G | E |  | no halt in 10^200 steps, 211 F-events, all reading 0 |
| 1LF | 0LD | [`1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_0LD---`](../1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_0LD---/README.md) | A | A |  | no halt in 10^22 steps, 21 F-events, all reading 0 |
| 1LF | 0LD | [`1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_0RB---`](../1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_0RB---/README.md) | B | C |  | no halt in 10^22 steps, 21 F-events, all reading 0 |
| 1LF | 0LD | [`1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA1RF_0RE---`](../1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA1RF_0RE---/README.md) | G | E |  | not run |
| 1LF | 0RC | [`1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_0LA---`](../1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_0LA---/README.md) | B | C |  | no halt in 10^200 steps, 251 F-events, all reading 0 |
| 1LF | 0RC | [`1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA1RF_0LD---`](../1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA1RF_0LD---/README.md) | G | E |  | no halt in 10^200 steps, 232 F-events, all reading 0 |
| 1LF | 0RE | [`1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_0RE---`](../1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_0RE---/README.md) | A | A |  | no halt in 10^200 steps, 193 F-events, all reading 0 |
| 1LF | 1LB | [`1RB---_0LC0LB_1RF0LD_1RE0RB_1LB0RC_0RD1RA`](../1RB---_0LC0LB_1RF0LD_1RE0RB_1LB0RC_0RD1RA/README.md) | X | F |  | no halt in 10^200 steps, 206 F-events, all reading 0 |
| 1LF | 1LB | [`1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_1LB---`](../1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_1LB---/README.md) | A | A |  | no halt in 10^200 steps, 193 F-events, all reading 0 |
| 1LF | 1LB | [`1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_1RE---`](../1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_1RE---/README.md) | B | C |  | no halt in 10^200 steps, 193 F-events, all reading 0 |
| 1LF | 1LD | [`1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_1LD---`](../1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_1LD---/README.md) | A | A |  | no halt in 10^200 steps, 209 F-events, all reading 0 |
| 1LF | 1LD | [`1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_1RB---`](../1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_1RB---/README.md) | B | C |  | no halt in 10^200 steps, 192 F-events, all reading 0 |
| 1LF | 1LD | [`1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA1RF_1RE---`](../1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA1RF_1RE---/README.md) | G | E |  | no halt in 10^200 steps, 211 F-events, all reading 0 |
| 1LF | 1RA | [`1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_1LD---`](../1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_1LD---/README.md) | B | C | a | no halt in 10^200 steps, 292 F-events, all reading 0 |

<!-- end F05 -->

## Pages

- [`pages/holdouts/1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1RE---/explainer.html`](../../pages/holdouts/1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1RE---/explainer.html)
- [`pages/holdouts/1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1RE---/proof-status.html`](../../pages/holdouts/1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1RE---/proof-status.html)

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Almost the same run as [`1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_1LD---`](../1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_1LD---/README.md) (observed, not proved).** Tape and head are the same at all but 8 of the first 10^7 steps from blank tape. The two runs part 4 times, each time for a step or two and by one cell, first at step 40,899 and last at step 5,488,817, and come together again. The tables differ and are not renamings of each other. While the runs agree, the states pair up as A–A, B–B, C–C, D–D, E–E (this machine first).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_1RC---`](../1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_1RC---/README.md): rename A→D, B→E, C→A, D→B, E→C, F→F; it is this table started in state C
- [`1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LB---`](../1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LB---/README.md): rename A→C, B→D, C→E, D→A, E→B, F→F and exchange left and right; it is this table started in state D, in a mirror

<!-- end of related machines -->
