# 1RB1RF_1LC0RB_1RD0LC_1LE1RA_0RC1LB_---1RE

bbchallenge id 147183. One of the six-state holdouts whose halting from blank tape is open. Family: Counter-like growth on both sides (exp/exp; structure not yet found).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RF |
| B | 1LC | 0RB |
| C | 1RD | 0LC |
| D | 1LE | 1RA |
| E | 0RC | 1LB |
| F | --- | 1RE |

**Verdict.** **The question is open.** No halt in the first 10^10 steps (C simulator); the macro configuration and its rules are not yet known.

## What it does

The tape is blocks of 1s, mostly `1^3` on the left and `1^3` or `1^4` on the right, separated by gaps of one, two,
four or five 0s. Both ends grow like the logarithm of the step count (the left one by 3 cells at a time in every
snapshot seen). The left end is made of the words `1110`, `11100`, `1100` with a marker `0000` travelling along it.

## What is established

**Proved in Lean, kernel only:**

- **The halting configurations.** The machine stops exactly when it reads the symbol of a halting transition (F0); the generated statement covers every configuration. (`step_none_iff`, `lean/Blank.lean`)
- **No halt in the first 10,000 steps.** The list simulator of the shared library, proved to agree with the machine's semantics, runs 10,000 steps from blank tape without a halt, evaluated by Lean's kernel. (`blank_runs_kernel`, `lean/Blank.lean`)

**Proved in Lean with `native_decide`:**

- **No halt in the first 10^7 steps.** The same run, evaluated by compiled code. (`blank_runs_native`, `lean/Blank.lean`)

**Trusted computation (C/Python, not Lean):**

- **No halt in the first 10^10 steps.** The C simulator `tools/c/tmrun.c` runs 10^10 steps from blank tape without a halt; at the end the tape holds 1,224 ones. (`tmrun 1RB1RF_1LC0RB_1RD0LC_1LE1RA_0RC1LB_---1RE 10000000000`)
- **No halt in the first 10^9 steps.** The C simulator `tools/c/triage.c` runs 10^9 steps without a halt; at the end 1,538 cells have been visited and 949 of them hold a 1. (`holdouts/triage.json`)
- **Where a halt can be.** A closed tape language of windows of 5 cells (`tools/py/bbtools/ctl.py`, closure checked by the script, not by Lean) contains every configuration reachable from blank tape, and its only halting configurations have F reading a 0 with three 1s just left of the head (`1 1 1 F>0`). (`python3 -m bbtools.ctl 1RB1RF_1LC0RB_1RD0LC_1LE1RA_0RC1LB_---1RE 5`)
- **Not decided by n-gram CPS up to width 14.** The n-gram Closed Position Set decider (`tools/c/ngramcps.c`) with equal widths 4, 6, 8, 10, 12 and 14, plain and with the fixed-length (1) and LRU history augmentations, either reaches a halting local configuration (UNKNOWN) or stops at 3·10^7 local configurations: it does not prove non-halting at these settings. (`ngramcps MACHINE N [-H 1 | -U] -m 30000000`)

**Heuristic:**

- **Growth shape: exp/exp.** Left of the start, the visited part of the tape grows like the logarithm of the step count: each new cell costs a roughly constant factor more time, the signature of a *counter* or of a Collatz-like map whose values are written on the tape (fitted exponent 0.099). Right of the start it grows like the logarithm of the step count: each new cell costs a roughly constant factor more time, the signature of a *counter* or of a Collatz-like map whose values are written on the tape (fitted exponent 0.089). (`tools/py/bbtools/triage.py`)
- **The blocks.** At the last left records before 10^9: `C>0 0^2 1^3 0^2 1^3 0 1^3 0^2 1^3 0 1^3 0^2 1 0^2 ...`; at the right: `... 1^3 0 1^4 0 1^4 0 1^4 0 1^4 ...`, with gaps of one, two, four or five 0s. Hundreds of blocks, changing at many places between visits to the ends. (`tmrun 1RB1RF_1LC0RB_1RD0LC_1LE1RA_0RC1LB_---1RE 1000000000 records 100000`)
- **The ends grow three cells at a time.** In snapshots of the leftmost 60 cells taken whenever they change (4,922 snapshots in 10^9 steps), the left end moved 176 times, every time by exactly 3 cells. At the 312 visits to the right end (the head arriving after being more than 50 cells away) in 10^9 steps it had grown by 3 cells 294 times. The left end is made of words `1110`, `11100` and `1100`, with a marker `0000` that travels along it; what they encode is not known. (`c/leftsnap.c` (`./leftsnap 1RB1RF_1LC0RB_1RD0LC_1LE1RA_0RC1LB_---1RE 1000000000 60`), `c/rvisits.c` (`./rvisits 1RB1RF_1LC0RB_1RD0LC_1LE1RA_0RC1LB_---1RE 1000000000 50`))

**Open:**

- **Does it halt from blank tape?.** Not known. The macro configuration family has not been found.

## For later

Not known: which words are digits, the carry rule, and whether a carry can ever produce `1 1 1 F>0`. A first
step: snapshot the left 60 cells at each change (`c/leftsnap.c`) and parse them into the words above, as was done
for the counters of 173741 and the 2a/2b twins.

## Reproduce

From the repository root:

```sh
. /etc/profile.d/lean.sh      # after scripts/setup-lean.sh
holdouts/1RB1RF_1LC0RB_1RD0LC_1LE1RA_0RC1LB_---1RE/lean/check.sh
gcc -O2 -o triage tools/c/triage.c && ./triage 1RB1RF_1LC0RB_1RD0LC_1LE1RA_0RC1LB_---1RE 1000000000
gcc -O2 -o tmrun tools/c/tmrun.c && ./tmrun 1RB1RF_1LC0RB_1RD0LC_1LE1RA_0RC1LB_---1RE 10000000000
cd tools/py && python3 -m bbtools.ctl 1RB1RF_1LC0RB_1RD0LC_1LE1RA_0RC1LB_---1RE 5
```

## Family screen (F09, 13 November 2026)

The 22 machines of family F09 were screened in one way, to decide which family each belongs to. `holdouts/1RB0LC_0RC0RF_1RD0LE_1LA1RA_1LC1RB_0RB---/screen/screen.py`
runs the machine from blank tape for 2·10^10 steps and, at the first new leftmost and rightmost cell after each
threshold 10^6·4^k, compresses the tape twice: repeats of a word of at most 40 cells (level 1), then repeats of
groups of such tokens (level 2). A bounded description keeps the number of level-2 tokens bounded while the tape
grows. The long runs use the macro simulator `holdouts/1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA/c/msim.c`, sampled at one record per leading digit of the step count.
Everything in this section is observed in one run; none of it is proved.

| record | step | visited cells | cells in no repeat | repeats | level-2 tokens | largest repeat / tape |
|---|---|---|---|---|---|---|
| left | 272,473,080 | 1,302 | 96 | 65 | 101 | 0.27 |
| right | 272,931,140 | 1,305 | 72 | 58 | 97 | 0.27 |
| left | 1,035,523,665 | 1,551 | 109 | 71 | 112 | 0.23 |
| right | 1,036,761,542 | 1,554 | 90 | 72 | 113 | 0.22 |
| left | 4,104,025,694 | 1,935 | 111 | 78 | 126 | 0.18 |
| right | 4,164,164,597 | 1,938 | 111 | 85 | 132 | 0.18 |
| right | 16,540,838,531 | 2,055 | 102 | 79 | 132 | 0.17 |
| left | 18,077,824,728 | 2,058 | 108 | 84 | 126 | 0.17 |

**Proposed family: F06, block-list counters** (not a bouncer: a counter on a tape that grows like the logarithm of the time).

The tape is short: 1,302 visited cells at 2.7·10^8 steps, 1,551 at 10^9, 1,935 at 4.1·10^9 and 2,058 at 1.8·10^10. Both ends grow like the logarithm of the step count, which is the mark of a counter, not of a bouncer.

The tape is runs of 1s of length 3 (some 6 or 9) separated by one, two or five 0s, with stretches of the words `01110` and `10011` of up to 70 copies; about 100 to 130 level-2 tokens, in proportion to the length. Nothing is periodic on a large scale.

Among the three families offered it is F06 (a counter); by its shape it would sit better with the counters on a logarithmic tape (F02 or F03).

Next step: Read the tape as digits (the gaps of one, two and five 0s) and look for the increment rule; the two sides seem to hold two counters.

## Pages

- [`pages/holdouts/1RB1RF_1LC0RB_1RD0LC_1LE1RA_0RC1LB_---1RE/explainer.html`](../../pages/holdouts/1RB1RF_1LC0RB_1RD0LC_1LE1RA_0RC1LB_---1RE/explainer.html)
- [`pages/holdouts/1RB1RF_1LC0RB_1RD0LC_1LE1RA_0RC1LB_---1RE/proof-status.html`](../../pages/holdouts/1RB1RF_1LC0RB_1RD0LC_1LE1RA_0RC1LB_---1RE/proof-status.html)
