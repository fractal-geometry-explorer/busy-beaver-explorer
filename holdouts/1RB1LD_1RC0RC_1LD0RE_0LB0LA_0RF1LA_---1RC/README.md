# 1RB1LD_1RC0RC_1LD0RE_0LB0LA_0RF1LA_---1RC

bbchallenge id 106785. One of the six-state holdouts whose halting from blank tape is open.

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

## Lean

Only the generated files: the halting configurations and no halt in 10^7 steps (`lean/Blank.lean`). The sweep does
not run over a repeated word, so the shift rules used for the other holdouts do not apply directly.

## Status

**Open.** The machine halts only when E reads 0 with a 0 to its right (F reading 0). Everything rests on the
generator, whose rules are unknown.

## For later

- The transducer of one sweep across the stream, as rules on short words (the stream is made of words like `10`,
  `1110` and `00110`), proved in Lean with symtm. That would prove the translation.
- The generator as a map from one round trip to the next.

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LD_1RC0RC_1LD0RE_0LB0LA_0RF1LA_---1RC/lean/check.sh
gcc -O2 -o /tmp/turns holdouts/1RB1LD_1LC0RE_1LA0LD_0LB0LE_0RB0LF_1RE---/c/turns.c
/tmp/turns 1RB1LD_1RC0RC_1LD0RE_0LB0LA_0RF1LA_---1RC 1000000000 100000 0     # visits to the two ends
cd holdouts/1RB1LD_1RC0RC_1LD0RE_0LB0LA_0RF1LA_---1RC && gcc -O2 -o /tmp/arrivals c/arrivals.c
/tmp/arrivals 1RB1LD_1RC0RC_1LD0RE_0LB0LA_0RF1LA_---1RC 120000000 1000 -1000 100000000 | python3 py/check_translation.py
```

## Pages

- [`pages/holdouts/1RB1LD_1RC0RC_1LD0RE_0LB0LA_0RF1LA_---1RC/explainer.html`](../../pages/holdouts/1RB1LD_1RC0RC_1LD0RE_0LB0LA_0RF1LA_---1RC/explainer.html)
- [`pages/holdouts/1RB1LD_1RC0RC_1LD0RE_0LB0LA_0RF1LA_---1RC/proof-status.html`](../../pages/holdouts/1RB1LD_1RC0RC_1LD0RE_0LB0LA_0RF1LA_---1RC/proof-status.html)
