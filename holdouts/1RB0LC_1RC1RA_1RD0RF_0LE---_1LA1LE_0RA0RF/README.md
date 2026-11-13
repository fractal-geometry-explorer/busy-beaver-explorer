# 1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA0RF

bbchallenge id 123915 (a3 of the family). One of the six-state holdouts whose halting from blank tape is open.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LC |
| B | 1RC | 1RA |
| C | 1RD | 0RF |
| D | 0LE | --- |
| E | 1LA | 1LE |
| F | 0RA | 0RF |

**Family:** Chaotic Bell: a (100)^n counter and a list of 1-runs of lengths 6k+1, both growing by 5/4 every two epochs.

A chaotic Bell machine: the head sweeps over a counter (100)^n and a list of runs of 1s of lengths 6k+1; every epoch halves the number of runs of each length while moving them one length up, turns the counter into new runs of 7 and rebuilds the counter, and the whole grows by 5/4 every two epochs. It halts only if state B ever reads 0 0 1; not seen in 10^14 steps of an exact accelerated simulation.

## Family

Four G01 machines: `1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA0RF_0LD---` (a1, id 155900), `1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA1RF_0LC---` (a2, id 72859), `1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA0RF` (a3, id 123915) and
`1RB0LE_1RC1RA_1LD0RE_1LA1LD_1LD0RF_0RA---` (a4, id 66704). The shared tools live in the folder of a2 (`holdouts/1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA1RF_0LC---/py`, `c`).

Machines a2, a3 and a4 share one orbit: the list of a3 at its visits of the right end is the list of a2 (82 of the 97 snapshots of a2 up to 10^14 steps are found literally in the run of a3, the simple comparison used does not match the rest, one of which lies beyond the end of the a3 run), each reached after 5/4 of the step count of a2, a ratio that settles to 1.2500 from 10^10 steps on (a3 does the step C0 of a2 by the detour C0 D0 E1).

The community tracker says “Several tables share one chaotic Bell orbit. The interior is chaotic.”

## What it does

After a sweep to the right the tape is a counter `(100)^n` followed by runs of 1s separated by `00` (R-form); almost
all runs have a length 6k+1, sorted into groups (the 7s, the 13s, the 19s, ...), with a few odd runs between the
groups. After a sweep to the left the same list reads: counter `(011)^n`, a run of length v is an alternating stretch
`0101...0` of v cells, `11` between stretches (L-form).

The head goes back and forth over the whole tape. Its right turning point (the front) moves to the right through the
list; behind it the runs are regrouped two by two into units with a timer (a run of 1s that loses 3 cells per round
trip: `bounce_on_1`). A unit made of runs 6j+1 holds the front for about 3(j-1) trips (1 trip for the 7s) and leaves
one run 6j+7.

An epoch has two phases. Phase 1: the head turns at the left end of the tape, each round trip adds 2 to n; when the
front reaches the right end, one left sweep regroups the list. Phase 2: the head turns at the right end of the
counter, each round trip takes 2 from n and makes one new run of 7, with two F-events (B reads `0 1 1 0`) per trip;
when the counter is used up, phase 1 resumes.

Counter and numbers of runs at three successive visits of the right end (a2; a1 has other numbers, the same law):

| step (a2) | n | 7 | 13 | 19 | 25 | 31 | 37 | 43 | 49 | 55 | 61 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 5.37x10^13 | 267238 | 439036 | 53432 | 87820 | 10676 | 17566 | 2135 | 3511 | 426 | 702 | 85 |
| 6.82x10^13 | 1097580 | 133620 | 219517 | 26715 | 43910 | 5337 | 8782 | 1067 | 1755 | 213 | 351 |
| 8.39x10^13 | 333950 | 548791 | 66808 | 109758 | 13357 | 21955 | 2668 | 4390 | 533 | 877 | 106 |

Epoch law (read off the data, heuristic): c7' ~ n/2, c(6j+7)' ~ c(6j+1)/2 (the half or one or two less),
n' ~ (5/2) c7. So over two epochs everything grows by 5/4, the step count by 25/16, and the counts fall by 5 for every
+12 in length. The corrections and the odd runs between the groups follow no visible rule: the chaotic part.

## Halting condition

It halts exactly when state B reads `0 0 1`: B0 C0 put D on a 1 (`b_001_halt` in `lean/Paths.lean`). No other way: D is entered only by C0 (moving right), and C by B0 (moving right) or A1 (moving left; then C0 puts D on the 0 that A has just written, and D0 goes on).

In the first 10^9 steps of a2 state B reads `0 1 1` 20,972 times; in 20,941 of them the cells around are `111101[0]110101`, in 29 `001101[0]110101`, and twice (steps 104 and 1,264) something else; the next cell is always 0. a1 has 20,998 such events with the windows `111100[0]110101` and `001100[0]110101`. So after the first 1,300 steps the F-events seen are all of two harmless kinds; whether that holds for ever is the open question.

Not seen in 10^14 steps. Whether it can happen is open: one would need an invariant for the odd runs between the groups.

## Reproduce

```sh
P=holdouts/1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA1RF_0LC---
python3 $P/py/bell_farrun.py 1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA0RF 1e12                 # exact accelerated run, lists at the right end
gcc -O2 -o /tmp/tapeat $P/c/tapeat.c
python3 $P/py/bell_validate.py 1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA0RF 2e10 50 /tmp/tapeat   # compare with direct simulation
gcc -O2 -o /tmp/nb $P/c/neighbours.c && /tmp/nb 1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA0RF 30000000      # neighbours and other start states that halt
python3 $P/py/gen_paths.py --check                    # lean/Paths.lean of the four machines is up to date
```

`data/far_1e14.json` holds the recorded lists (`"epochs"`: step, then the tape left of the head as run lengths, `7x12` = twelve runs
of 7, `1xN` = the counter).

## Further work

1. Prove the round trips of both phases for all counts (bbtools.symtm can do each sweep; the regrouping sweep is the
   hard one), then the epoch law with its corrections.
2. Understand the odd runs between the groups; only they can produce the halting pattern.
3. The simulator does not compress the runs that pile up at the right end (`66 1 66 1 ...`), which limits it to about
   10^15 steps; nested jumps would go further.

## What is proved, and how firmly

| level | claim | where |
|---|---|---|
| kernel | **The halting configurations.** The machine stops exactly when it reads the symbol of a halting transition (D1); the generated statement covers every configuration. | `step_none_iff`, `lean/Blank.lean` |
| kernel | **No halt in the first 10,000 steps.** The list simulator of the shared library, proved to agree with the machine's semantics, runs 10,000 steps from blank tape without a halt, evaluated by Lean's kernel. | `blank_runs_kernel`, `lean/Blank.lean` |
| native | **No halt in the first 10^7 steps.** The same run, evaluated by compiled code. | `blank_runs_native`, `lean/Blank.lean` |
| trusted | **No halt in the first 10^9 steps.** The C simulator `tools/c/triage.c` runs 10^9 steps without a halt; at the end 33,659 cells have been visited and 22,667 of them hold a 1. | `holdouts/triage.json` |
| heuristic | **Growth shape: exp/sqrt.** Left of the start, the visited part of the tape grows like the square root of the step count, the signature of a head sweeping back and forth across the whole tape and adding a cell or a few at the end of each sweep (a bouncer-like shape) (fitted exponent 0.515). Right of the start it grows like the logarithm of the step count: each new cell costs a roughly constant factor more time, the signature of a counter or of a Collatz-like map whose values are written on the tape (fitted exponent 0.063). | `tools/py/bbtools/triage.py` |
| kernel | **11 shift rules.** For every n, the head crosses n copies of a short word in a fixed number of steps per copy and leaves another word behind (for example the head crossing `(100)^n` or `(1)^n`; these are the sweeps over the counter and the runs). Generated and proved by `bbtools.symtm`, checked by Lean's kernel. | `lean/Rules.lean`, generated by `holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/rules.py` |
| trusted | **No halt in the first 3x10^10 steps.** The lead's direct C simulator (`tools/c/tmrun.c`) runs 3x10^10 steps without a halt. | `tmrun 1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA0RF 30000000000` |
| kernel | **The local paths and the halting path.** Outside the sweeps, the machine does a handful of local things, each proved for every tape around it: A on a 1 bounces (`bounce_on_1`, `bounce_on_0_0`, `bounce_on_0_1`); B reading `0 1 1 0` gives `1 0 0 0` with A on the right (4 steps: B0 C1 F1 F0), and on `0 1 1 1 0`, where a2 halts, it erases and goes on (`fevent_on`) (`fevent`, the F-event, twice per round trip in the second half of an epoch); and B reading `0 0 1` halts: B0 C0 put D on a 1 (`b_001_halt`). By the table this is the only way to halt: D is entered only by C0 (moving right), and C by B0 (moving right) or A1 (moving left; then C0 puts D on the 0 that A has just written, and D0 goes on). | `lean/Paths.lean`, generated by `holdouts/1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA1RF_0LC---/py/gen_paths.py` |
| trusted | **The exact accelerated simulator agrees with direct simulation.** `bell_wsim.py` keeps the tape as repeated words, crosses a repeated word in one move (an exact shift rule found on the fly), and at the left turns looks for a stretch of round trips after which the tape has the same shape with counts changed by constants; it then applies many such stretches at once, with the exact step count. Its tape, state and step count were compared with a plain C simulator at 680 tapes up to 2.02x10^10 steps: all equal. | `holdouts/1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA1RF_0LC---/py/bell_wsim.py`, `py/bell_validate.py`, `c/tapeat.c` |
| trusted | **No halt in the first 10^14 steps.** The accelerated simulator runs 10^14 steps from blank tape without reaching the halting transition; the list at each visit of the right end is recorded. | `holdouts/1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA1RF_0LC---/py/bell_farrun.py`, `holdouts/1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA0RF/data/far_1e14.json` |
| trusted | **The shared orbit.** Machines a2, a3 and a4 share one orbit: the list of a3 at its visits of the right end is the list of a2 (82 of the 97 snapshots of a2 up to 10^14 steps are found literally in the run of a3, the simple comparison used does not match the rest, one of which lies beyond the end of the a3 run), each reached after 5/4 of the step count of a2, a ratio that settles to 1.2500 from 10^10 steps on (a3 does the step C0 of a2 by the detour C0 D0 E1). The reason is in the tables: a4 does with E, F what a2 does with C, E on the bounce of A, a3 replaces the step C0 of a2 by three steps with the same result, and all three turn `B> 0 1 1 0` into `1 0 0 0 A>`. They could part only where B reads `0 1 0` (a2 and a4 differ there: `b_010`), `0 1 1 1` (a2 and a4 halt, a3 goes on) or `0 0 1` (a3 halts); in 10^9 steps of a2 and a4, B never reads `0 1 0` and reads `0 0` only at the blank right end. | `lean/Paths.lean`; `data/far_1e14.json` of the four machines |
| trusted | **Neighbours and other starts.** The community tracker says “Several tables share one chaotic Bell orbit. The interior is chaotic.” (Direct runs of 3x10^7 steps of every table that differs in one transition, and of the six start states.) | `holdouts/1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA1RF_0LC---/c/neighbours.c` |
| heuristic | **The epoch law.** Read off the recorded lists, not proved: with n the counter and c<sub>7</sub>, c<sub>13</sub>, … the numbers of runs, one epoch gives c<sub>7</sub>′ ≈ n/2, c<sub>6j+7</sub>′ ≈ c<sub>6j+1</sub>/2 (the half, or one or two less) and n′ ≈ (5/2)·c<sub>7</sub> (within 10^−4 at 10^14 steps). Hence the two interleaved geometric series in the table of counts, the factor 5 per +12 in length, growth by 5/4 every two epochs and step counts growing by 25/16. Between the groups sit a few odd runs that change from epoch to epoch without a visible rule; they are the chaotic part, and the halting pattern can only arise there. | `data/far_1e14.json` |
| heuristic | **Where B reads 0 1 1.** In the first 10^9 steps of a2 state B reads `0 1 1` 20,972 times; in 20,941 of them the cells around are `111101[0]110101`, in 29 `001101[0]110101`, and twice (steps 104 and 1,264) something else; the next cell is always 0. a1 has 20,998 such events with the windows `111100[0]110101` and `001100[0]110101`. So after the first 1,300 steps the F-events seen are all of two harmless kinds; whether that holds for ever is the open question. | direct C runs (not kept in the repository) |
| open | **Does it halt from blank tape?.** Not known. It halts exactly if B ever reads `0 0 1`. A proof of non-halting needs an invariant for the odd runs between the groups, which no closed rule describes so far; the simulator slows down beyond 10^15 steps because those runs pile up at the right end. |  |

## Lean

`lean/Rules.lean` (shift rules, from the first pass, generated by
`holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/rules.py`) and `lean/Paths.lean` (the local paths and the
halting path, generated by `holdouts/1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA1RF_0LC---/py/gen_paths.py`) are listed in `lean/check.sh` after `Blank.lean`:

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA0RF/lean/check.sh
```

## Pages

- [`pages/holdouts/1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA0RF/explainer.html`](../../pages/holdouts/1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA0RF/explainer.html)
- [`pages/holdouts/1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA0RF/proof-status.html`](../../pages/holdouts/1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA0RF/proof-status.html)
