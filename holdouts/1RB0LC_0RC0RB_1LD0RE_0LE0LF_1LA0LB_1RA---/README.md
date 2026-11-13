# 1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1RA---

bbchallenge id 12989. One of the six-state holdouts whose halting from blank tape is open. Group G01.
**Family:** Nested block counter (core 1RB0LC_0RC0RB_1LD0RE_0LE?LF_1LA0LB, frames A/B/X). The shared analysis code is in [`holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---`](../1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---/) (`py/`, `c/`).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LC |
| B | 0RC | 0RB |
| C | 1LD | 0RE |
| D | 0LE | 0LF |
| E | 1LA | 0LB |
| F | 1RA | --- |

## What it does

This machine is written in **frame A**, the frame the analysis uses: states A to E do all the work, D1 = 0LF is the only way into F, F0 = 1RA is this machine's own transition, and F1 halts.



All 14 machines of the family share this five-state core (frame A: `1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_?---`):

| machine | frame | F0 in frame A | D1 | frame-A start | F-events to 10^11 |
|---|---|---|---|---|---|
| [1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---](../1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---/README.md) | A | 0RA | 0LF | A | 13 |
| [1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RB---](../1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RB---/README.md) | A | 0RB | 0LF | A | 7 |
| [1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RE---](../1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RE---/README.md) | A | 0RE | 0LF | A | 8 |
| [1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LB---](../1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LB---/README.md) | A | 1LB | 0LF | A | 8 |
| [1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LC---](../1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LC---/README.md) | A | 1LC | 0LF | A | 5 |
| **1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1RA---** | A | 1RA | 0LF | A | 4 |
| [1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_0LD---](../1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_0LD---/README.md) | B | 0RA | 0LF | C | 13 |
| [1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_0LE---](../1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_0LE---/README.md) | B | 0RB | 0LF | C | 7 |
| [1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_0RA---](../1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_0RA---/README.md) | B | 0LC | 0LF | C | 5 |
| [1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1LD---](../1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1LD---/README.md) | B | 1RA | 0LF | C | 4 |
| [1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1RA---](../1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1RA---/README.md) | B | 1LC | 0LF | C | 5 |
| [1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1RE---](../1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1RE---/README.md) | B | 1LB | 0LF | C | 8 |
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

Checking consecutive events of the run against this rule (`c/family.c events` + `py/check_rounds.py`): 10,135 events in 10^8 steps; transitions: same 4,878, same* 1,611, down 2,002, up1 1,300, up2 260, up3 51, up4 11, up5 1, X 20.
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
the direct run (`data/trajectory.json`, 100,000,218,995 steps) it reproduces all 12
left-end events and all 4 F-events exactly.
It then runs to **2.4·10^100 steps** in 21 s (`data/hybrid.json`): 286 left-end
events, 120 F-events, no halt.
The list grows to about 40 blocks, block i of size about 5^i; most visits are clean.

### The left end

Each return of the head to the left end of the tape starts a round on the whole list and adds 3 cells on the left.
The block lists at these moments (from `data/trajectory.json`, 100,000,218,995 steps):

| step | cells left of start | blocks |
|---|---|---|
| 9 | 3 | `[2]` |
| 133 | 7 | `[3, 6]` |
| 205 | 11 | `[13]` |
| 284 | 14 | `[16]` |
| 537 | 17 | `[16, 8]` |
| 4,658 | 20 | `[12, 16, 44]` |
| 79,217 | 23 | `[10, 122, 14, 176]` |
| 1,450,904 | 26 | `[10, 100, 24, 592, 632]` |
| 8,680,023 | 29 | `[10, 80, 400, 1768, 1112]` |
| 45,165,480 | 32 | `[10, 62, 310, 1314, 2560, 3824]` |
| 962,233,433 | 35 | `[10, 44, 220, 864, 306, 5320, 24764]` |
| 18,727,998,132 | 38 | `[10, 26, 130, 412, 1838, 7336, 61612, 77924]` |

Between left-end events b2 drops by 18, b3 by 90, b4 by about 450 (the closed form seen from the top: the
first block at the left end is even, so the top-level visit itself is unclean and simulated), while the last block
is born or grows; when a block runs out the list shortens and the neighbours merge. Values such as 296, 524, 1136, 37496 recur across the family: they are
fixed outcomes of a block being born.

### The halting condition

F is entered only by D1 = 0LF (frame A). F1 halts; F0 = 1RA (frame A) continues. In 100,000,218,995 steps there are
4 F-events, at steps 39,734, 841,213, 6,436,652, 94,414,543,771; in the 2.4·10^100 steps of the exact map there are 120,
all reading 0, with surroundings `010001000100[F]001010101010` (81x); `010001000100[F]001010110101` (39x).

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
| trusted | **No halt in the first 10^9 steps.** The C simulator `tools/c/triage.c` runs 10^9 steps without a halt; at the end 66,558 cells have been visited and 28,624 of them hold a 1. | `holdouts/triage.json` |
| trusted | **One of 14 machines with the same five-state core.** States A to E of every machine of the family are the core 1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_?--- (in frame A); the machines differ in F0 and the start state, and some are mirror images. This one is frame A itself. | `holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---/py/frames.py`, `py/conjugacy_steps.py` |
| kernel | **The visit rule for every depth.** A *visit* starts with the head in state A on the 0 in front of plain blocks `(10)^b1 1 (10)^b2 1 … 1` and ends when it first steps left of that cell; it never reads the tape on its left. `go_spec` proves, by induction on the depth n and for every left context, that a *clean* visit (a decidable condition: every block it spreads is odd and ≥ 7, every second block nonempty) turns the list l into `go n l` in exactly `goT n l` steps, where `go` is the recursion: spread b1, five visits to [b2+1, b3, …] with the tail bumps +3, +1, +1, +1 between them, then b1−5. It is built from seven rules (PUSH, TURN, TAIL1–4, POP) proved by bbtools.symtm for all counts. | `go_spec`, `push` … `pop`, `lean/Family.lean` |
| kernel | **Its closed form.** `go_closed`: if b1 is odd and ≥ 7 and the later blocks are even, the last ≥ 2 and block i (i = 2..k−1) ≥ 2 + 18·5^i−2, then the visit is clean and gives (b1−5, b2−18, b3−90, …, bk−1−18·5^k−3, bk+12·5^k−2) (a single odd block gains 1); `visit_closed` states it on the tape. With the tail bump after the visit this is the measured round rule (−4, −18, …, +12·5^m−2) for every m. | `go_closed`, `visit_closed`, `lean/Family.lean`; closed step count in `holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---/py/cf.py` (trusted) |
| kernel | **Rounds, births and the F-event.** `round1`–`round4`: a clean visit followed by one phase of the tail on its left. `birth`: a visit to a single even block [2k+4] gives [2k+2, 8] in 10k+188 steps (where new blocks come from). `fevent` and `fevent_reads_zero`: the only way into F seen in the runs (a C exit onto the 0 of a phase-1 tail, then C0, D1) makes F read the last cell of a `1000` or of `100`, which is 0 for every q and every tape around. | `round1` … `birth`, `fevent_reads_zero`, `lean/Family.lean` |
| kernel | **The rules hold for this machine's own table.** The rules are proved on the frame-A table `FA.trans`. This machine is frame A; `halts_iff` says that this machine halts from blank tape iff the frame-A table halts from blank in state A, and `visit` restates `go_spec` for this machine. | `halts_iff`, `visit`, `lean/Family.lean` |
| kernel | **The round rule on one and two blocks (first pass).** Eight theorems on the machine's own table: a round on the last block changes it by +2 (+4 from phase 1), on the last two by (−4, +12), for each phase, with exact step counts. Now special cases of the rules above. | `round_m1_p1` … `round_m2_p4`, `lean/Rules.lean` |
| trusted | **The events follow the round rule.** Listing every event (A turning right with plain blocks on its right) and comparing consecutive ones: 10,135 events in 10^8 steps; transitions: same 4,878, same* 1,611, down 2,002, up1 1,300, up2 260, up3 51, up4 11, up5 1, X 20. The few exceptions (X) are the left end, the birth of a new last block, the merge after a block runs out, and the F-events. | `holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---/c/family.c events`, `holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---/py/check_rounds.py` |
| trusted | **No halt in the first 10^11 steps.** The exact run-length simulator (macro steps over `(10)^n`, `(1000)^n`, checked against plain simulation) runs 100,000,218,995 steps from blank tape without a halt. It meets 12 left-end events and 4 F-events (first at step 39,734), and at every F-event the cell F reads is 0. | `data/trajectory.json`, `holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---/py/trajectory.py` |
| trusted | **The whole run as an exact map on block lists.** `hybrid.py` runs the machine as a map on block lists: clean visits by the closed form (a theorem), every other visit (small or even first blocks, merges after a block runs out, births, the left end) by the exact run-length simulator, recursively and memoised. It is exact, not a model: against `data/trajectory.json` (100,000,218,995 steps of the machine) it reproduces all 12 left-end events (step and block list) and all 4 F-events (step and cell read). | `holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---/py/hybrid.py`, `holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---/py/hybrid_run.py`, `data/hybrid.json` |
| trusted | **No halt in the first 2.4·10^100 steps.** The exact map runs 2.4·10^100 steps (21 s): 286 left-end events, 120 F-events, every one reading 0 and every one of the proved kind (`010001000100[F]001010101010` (81×); `010001000100[F]001010110101` (39×)). The block list grows to about 40 blocks, block i of size about 5^i. | `data/hybrid.json` |
| heuristic | **Where a halt would have to come from.** F is entered only by D1 (D reads a 1 during the left sweep, where a spread block is turned back), and halts only when it then reads a 1. In this run every F-event has the same clean context (`010001000100[F]0010101` (4×)). Random block lists do reach a halting F-event (about 1 in 150 F-entries; e.g. `[15, 31, 17, 59, 31]` halts after 63,153 steps), so the halt is reachable in principle; whether the blank-tape run ever produces such a list is the open part. F-events get rarer as the blocks grow (the top-level round time grows about fivefold per block). | `holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---/py/random_lists.py` |
| open | **Does it halt from blank tape?.** Not known. The visit rule is proved for every depth, its closed form, births and the F-event too; what is missing is a proof that the unclean visits of the blank-tape run (merges, small first blocks, the left end) always end in a C exit of the proved kind and never in an F exit onto a 1, that is an invariant on the block lists reached from blank tape. | README.md, Further work |
| heuristic | **Growth shape: exp/sqrt.** Left of the start, the visited part of the tape grows like the logarithm of the step count: each new cell costs a roughly constant factor more time, the signature of a *counter* or of a Collatz-like map whose values are written on the tape (fitted exponent 0.031). Right of the start it grows like the square root of the step count, the signature of a head sweeping back and forth across the whole tape and adding a cell or a few at the end of each sweep (a *bouncer*-like shape) (fitted exponent 0.467). | `tools/py/bbtools/triage.py` |

## Reproduce

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1RA---/lean/check.sh          # Blank.lean + Rules.lean + Family.lean
python3 holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---/py/gen_family_lean.py 1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1RA--- H12989 > holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1RA---/lean/Family.lean
python3 holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---/py/cf.py                                       # closed form vs the recursion
python3 holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---/py/hybrid_run.py 1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1RA--- 1e100                     # exact block-list map, checked against trajectory.json
cd tools/py && python3 ../../holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---/py/gen_lean.py 1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1RA--- H12989 > ../../holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1RA---/lean/Rules.lean
python3 holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---/py/frames.py                                   # the 14 tables are conjugate as claimed
python3 holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---/py/conjugacy_steps.py 1e6                      # and the runs agree step by step
python3 holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---/py/trajectory.py 1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1RA--- 1e11 holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1RA---/data/trajectory.json
cc -O2 -o family holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---/c/family.c
./family events 1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1RA---:A 1e8 > ev.txt && python3 holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---/py/check_rounds.py ev.txt
./family enter 1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1RA--- 1e9 F                                 # the F-events, with the cells around them
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

## Pages

- [`pages/holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1RA---/explainer.html`](../../pages/holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1RA---/explainer.html)
- [`pages/holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1RA---/proof-status.html`](../../pages/holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1RA---/proof-status.html)
