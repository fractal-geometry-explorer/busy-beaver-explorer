# 1RB1LD_1RC0RC_1LD0RE_0LB0LA_0RF1LA_---1RC

bbchallenge id 106785, group G06, family F08 (a counter beside a chaotic edge). One of the six-state holdouts whose halting from blank tape is open.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LD |
| B | 1RC | 0RC |
| C | 1LD | 0RE |
| D | 0LB | 0LA |
| E | 0RF | 1LA |
| F | --- | 1RC |

## What it does

**An irregular generator feeding a rigidly translated stream.** In the first 10^9 steps the left end of the tape is
last extended at step 731,206. After that, the head bounces between a turning point well inside the tape and the right
end. It zigzags tightly, about 3.6 steps per cell, and a round trip takes about 43,000 steps at 10^8. Between
consecutive arrivals at the right end, the tape beyond a boundary near the turning point is the previous tape shifted
right by exactly 2 cells, unchanged. This held for 436 of 436 round trips (`py/check_translation.py`) between steps 10^8 and 1.2·10^8. So the right
part is a conveyor carrying away what the irregular region on the left (the *generator*) produces.

| step | tape width | rigid stream starts at cell |
|---|---|---|
| 10^6 | 1,105 | 777-808 |
| 10^7 | 3,161 | 1,532-1,572 |
| 10^8 | 9,467 | 3,446-3,531 |
| 10^9 | 30,011 | 11,845-11,890 |

## Where the tape changes

The *generator* is much smaller than it looks. `c/activezone.c` compares the tape at the end of each round trip
with the tape at the end of the previous one. Cells left of the trip's turning point are not visited at all; cells
right of a point z are the previous tape shifted right by exactly two cells. Only the window between the turning
point and z is really rewritten, and it is small:

| steps | trips sampled | window: median | 99th percentile | largest | turning point / tape width |
|---|---|---|---|---|---|
| 1.2·10^4 to 2.3·10^8 | 344 | 30 cells | 455 | 627 | 0.37 |
| 1.6·10^10 to 2·10^10 | 344 | 27 cells | 442 | 952 | 0.41 |

(every 20th trip up to 2·10^10 steps; the largest window in all 3,444 samples is 1,054 cells). So the tape is
three parts: an **archive** left of the turning point, which only the turning point's own moves bring back into
play; a small **active window** at the turning point; and the **stream**, which every trip carries two cells
further right without a change. The turning point drifts right, at about 0.4 of the tape's width, so the archive
keeps growing: when the turning point moves left (by up to a few hundred cells) the window reads the archive it
wrote earlier.

The turning point does not drift smoothly. Between consecutive trips it jumps by tens to hundreds of cells either
way (in the trips of the first 10^9 steps: most often −4, −1, −11, +6, +3 cells, and up to about ±400), with no visible
period in the jumps or in the window widths (`c/activezone.c` with EVERY = 1). Its drift to the right is the
average of these jumps.

What a trip into the stream brings back depends mostly on the cells near the window: at X = 4,500 (steps 10^8 to
4·10^8, about 1,950 trips to the right end), the state the head comes back in is a function of the state it left
in and the 28 cells X−8 .. X+19 for all but one of the 779 different such windows (`c/returns.c`, `py/returns.py`).
With fewer cells it is not (9 of 225 windows of 16 cells come back in two ways).

## Lean

`lean/Blank.lean` (generated): the halting configurations and no halt in 10^7 steps. `lean/Rules.lean` (kernel,
written by `py/rules.py`): the halting situations `halt_E` (`E> 0 0`), `halt_C` (`C> 1 0 0`), `halt_B0` and
`halt_B1` (`B> 0 1 0 0`, `B> 1 1 0 0`): F is entered only from E reading a 0, E only from C reading a 1, C only from
B or F, all moving right. The sweep does not run over a repeated word, so the shift rules used for the other
holdouts do not apply directly.

## Status

**Open.** No halt in 2·10^10 steps (`c/activezone.c`, direct simulation). The machine halts only when a rightward run meets two 0s
(`E> 0 0`). Everything rests on the active window, whose rules are unknown.

## For later

- The window as a system of its own: its input is the archive cell it moves onto and what the stream sends back,
  its output the cells it leaves to the archive and to the stream. If what the stream sends back depends only on a
  bounded number of cells next to the window (the observation above), the stream can be cut short as in
  1RB0LC_1LC0RE_1RA1LD_1LA1LC_1RF0RA_---0LA, and the model would run much further.
- The transducer of one sweep across the stream, as rules on short words (the stream is made of words like `10`,
  `1110` and `00110`), proved in Lean with symtm. That would prove the translation.

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LD_1RC0RC_1LD0RE_0LB0LA_0RF1LA_---1RC/lean/check.sh
gcc -O2 -o /tmp/turns holdouts/1RB1LD_1LC0RE_1LA0LD_0LB0LE_0RB0LF_1RE---/c/turns.c
/tmp/turns 1RB1LD_1RC0RC_1LD0RE_0LB0LA_0RF1LA_---1RC 1000000000 100000 0     # visits to the two ends
cd holdouts/1RB1LD_1RC0RC_1LD0RE_0LB0LA_0RF1LA_---1RC && gcc -O2 -o /tmp/arrivals c/arrivals.c
/tmp/arrivals 1RB1LD_1RC0RC_1LD0RE_0LB0LA_0RF1LA_---1RC 120000000 1000 -1000 100000000 | python3 py/check_translation.py
gcc -O3 -o /tmp/activezone c/activezone.c && /tmp/activezone 20000000000 20      # step, width, turning point, z, window
gcc -O3 -o /tmp/returns c/returns.c && /tmp/returns 400000000 100000000 4500 20 | python3 py/returns.py
python3 py/rules.py                                                               # rewrites lean/Rules.lean
```

## Pages

- [`pages/holdouts/1RB1LD_1RC0RC_1LD0RE_0LB0LA_0RF1LA_---1RC/explainer.html`](../../pages/holdouts/1RB1LD_1RC0RC_1LD0RE_0LB0LA_0RF1LA_---1RC/explainer.html)
- [`pages/holdouts/1RB1LD_1RC0RC_1LD0RE_0LB0LA_0RF1LA_---1RC/proof-status.html`](../../pages/holdouts/1RB1LD_1RC0RC_1LD0RE_0LB0LA_0RF1LA_---1RC/proof-status.html)
