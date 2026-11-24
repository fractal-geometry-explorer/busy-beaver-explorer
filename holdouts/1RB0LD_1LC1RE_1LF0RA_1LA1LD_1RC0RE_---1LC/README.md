# 1RB0LD_1LC1RE_1LF0RA_1LA1LD_1RC0RE_---1LC

bbchallenge id 125234. One of the six-state holdouts whose halting from blank tape is open (group G11, family **10 and 1110 words, two-ended**). The pages are built from [`status.json`](status.json).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LD |
| B | 1LC | 1RE |
| C | 1LF | 0RA |
| D | 1LA | 1LD |
| E | 1RC | 0RE |
| F | --- | 1LC |

## Status

Open. Lean (kernel): halting configurations and bounded runs (`lean/Blank.lean`), the halt from `0 C> 0`
(`halt_ctx`; that every halt passes through it is from the table) and shift rules (`lean/Rules.lean`), 49 event rules
for all sizes (`lean/Events.lean`), the borrow and carry rules of the two counters (`lean/Counter.lean`). C: no halt
in 2·10^10 steps. Accelerated (`tools/py/bbtools/cjump.py`, trusted computation): no halt in 3.75·10^11 steps.

## What it does

An **event** is the head in state E on cell -134 (cells from the start cell; 15,346,830 visits in steps
2.5·10^9-3·10^9; before step ~8.5·10^8 the busiest point was D on cell -108). Two kinds of event dominate:

- short (8 steps): `x 0 0 E> 0 1 1 1` -> `x 1 1 E> 0 1 0 1`;
- long: a run of a+1 ones left of the head becomes `1 1 1 0 0^a` and the `01` words on the right become `0111`
  words (2a+18 steps and up), e.g. `L 1 0 0 1^(a+1) E> 01 0101 1 1^b R` -> `L 1 1 1 0 0^a E> 0111 010 1^b R`.

**Proved**: 49 rules mined from the run (`py/mined.txt`, `py/hand.py` empty), each for every value of its repeat
counts. **Coverage** (3·10^9 steps): 65,868,043 events, 13,872 unmatched (99.98%).

**Where it can halt.** From `0 C> 0` it halts (Lean `halt_ctx`); every halt passes through it (from the table: C0 =
1LF, F0 halts). In 3·10^9 steps it never occurs; `1 C> 0` occurs 25 times (19 before the first event, 6 in uncovered
events, none in a proved rule). It follows (not as a theorem) that a halt would have to come from an uncovered event.

## The two counters

At every visit of the hub turn, A reading 0 at cell -136 from step 9.5·10^8 to step 1.34·10^11 (two cells left of the E event of `Events.lean`), the tape reads as two binary counters back to back:

- **left counter**, lowest digit next to the hub: 2-cell digits `00` (1) and `11` (0), separators `001011` and `110000101110111011`;
- **right counter**, lowest digit next to the hub: 4-cell digits `1011` and `1010`, separators `111010` and `111011`.

Each hub event takes 1 from the left counter and adds 1 to the right counter. Its cost is linear in what changes:
4 steps per left digit changed, 8 per right digit changed, 20 or 140 per separator crossed, plus a constant. `tools/py/bbtools/cjump.py` learns these words and costs from the run (exact
rational fit, accepted only if it predicts every observed event, whole tape and step count) and then jumps whole
stretches of counting at once; it matched direct runs exactly at every check.

**Proved in Lean** (`lean/Counter.lean`, kernel, for every `k`, `j` and every tape beyond the cells shown, written by
`py/rules.py` from 4,000 sampled events):

- `borrow` (4k + 32 steps): `L 00 (11)^k 11 A> 0 1 0 1 0 1 0 1 1 R` -> `L 11 (00)^k 00 A> 0 1 0 1 0 1 0 1 0 R`, the left counter borrowing through `k` digits;
- `carry0` (8j + 84 steps): `L 0 0 A> (a 25-cell stretch) (1010)^j 1 0 1 1 R`, the right counter carrying through `j` digits;
- `carry1` (28j + 92 steps): the same beyond a separator, with the 10-cell word `0101010111` repeated, the right counter carrying through `j` digits;
- `plain` (36 steps): `L 0 0 A> 0 1 0 1 0 1 0 1 0 1 0 1 1 R` -> `L 1 1 A> 0 1 0 1 0 1 0 1 1 1 0 1 0 R`, the most frequent short event.

**Overflows.** When the left counter runs out the hub moves and the counters are laid out again; the accelerator
then simulates directly until it can learn the new layout. Seen so far: the hub turn moved to cells -109 and -136 at steps 1.4·10^8 and 9.5·10^8, and at step 1.34·10^11 to a layout with four alternating turns.

**Accelerated halt hunt.** A 30-minute run of `cjump.py` reached step 375,369,479,393 (3.75·10^11) with 389 cells visited and no halt. After step 1.34·10^11 the hub moves to a layout with four alternating hub turns (cells -215, -203, -197, -173) that the learner does not fit, so the rest of the run is direct.


## Files

- `py/rules.py` writes `lean/Counter.lean` (`tools/py/bbtools/hubrules.py`).
- `py/events.py` writes `lean/Events.lean` and `c/rules.txt`; `py/mined.txt`, `py/hand.py`.
- Batch tools in `../1RB---_1LC1RF_0LE0RD_0RB0LC_1RD0LD_0RC0RA/`: `./evcov M 3000000000 -134 E c/rules.txt 0 0 'C:<00'`.
- `lean/rules.py` writes `lean/Rules.lean`.

## Next steps

Fit the four-turn layout after step 1.34·10^11 (a period-4 hub with the counters further from it), then decode the overflow; the 49 event rules of `lean/Events.lean` and the counter rules of `lean/Counter.lean` cover the counting phase.

## Pages

- [`pages/holdouts/1RB0LD_1LC1RE_1LF0RA_1LA1LD_1RC0RE_---1LC/explainer.html`](../../pages/holdouts/1RB0LD_1LC1RE_1LF0RA_1LA1LD_1RC0RE_---1LC/explainer.html)
- [`pages/holdouts/1RB0LD_1LC1RE_1LF0RA_1LA1LD_1RC0RE_---1LC/proof-status.html`](../../pages/holdouts/1RB0LD_1LC1RE_1LF0RA_1LA1LD_1RC0RE_---1LC/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh      # after scripts/setup-lean.sh
holdouts/1RB0LD_1LC1RE_1LF0RA_1LA1LD_1RC0RE_---1LC/lean/check.sh
gcc -O2 -o tmrun tools/c/tmrun.c && ./tmrun 1RB0LD_1LC1RE_1LF0RA_1LA1LD_1RC0RE_---1LC 20000000000
gcc -O2 -o ctxcount holdouts/1RB---_1LC1RF_0LE0RD_0RB0LC_1RD0LD_0RC0RA/c/ctxcount.c && ./ctxcount 1RB0LD_1LC1RE_1LF0RA_1LA1LD_1RC0RE_---1LC 1e9 C 2 -1
python3 tools/py/bbtools/cjump.py 1RB0LD_1LC1RE_1LF0RA_1LA1LD_1RC0RE_---1LC 1e3000 1800      # accelerated, 30 minutes
python3 holdouts/1RB0LD_1LC1RE_1LF0RA_1LA1LD_1RC0RE_---1LC/py/rules.py                        # writes lean/Counter.lean
```
