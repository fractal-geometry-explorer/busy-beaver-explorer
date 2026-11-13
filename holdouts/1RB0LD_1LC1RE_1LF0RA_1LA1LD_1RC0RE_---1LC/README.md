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
for all sizes (`lean/Events.lean`). C: no halt in 2·10^10 steps.

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

## Files

- `py/events.py` writes `lean/Events.lean` and `c/rules.txt`; `py/mined.txt`, `py/hand.py`.
- Batch tools in `../1RB---_1LC1RF_0LE0RD_0RB0LC_1RD0LD_0RC0RA/`: `./evcov M 3000000000 -134 E c/rules.txt 0 0 'C:<00'`.
- `lean/rules.py` writes `lean/Rules.lean`.

## Next steps

Read the rules as a macro machine (what the run of 1s and the right words count) and decode the uncovered events
(left-end visits, layout changes).

## Pages

- [`pages/holdouts/1RB0LD_1LC1RE_1LF0RA_1LA1LD_1RC0RE_---1LC/explainer.html`](../../pages/holdouts/1RB0LD_1LC1RE_1LF0RA_1LA1LD_1RC0RE_---1LC/explainer.html)
- [`pages/holdouts/1RB0LD_1LC1RE_1LF0RA_1LA1LD_1RC0RE_---1LC/proof-status.html`](../../pages/holdouts/1RB0LD_1LC1RE_1LF0RA_1LA1LD_1RC0RE_---1LC/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh      # after scripts/setup-lean.sh
holdouts/1RB0LD_1LC1RE_1LF0RA_1LA1LD_1RC0RE_---1LC/lean/check.sh
gcc -O2 -o tmrun tools/c/tmrun.c && ./tmrun 1RB0LD_1LC1RE_1LF0RA_1LA1LD_1RC0RE_---1LC 20000000000
gcc -O2 -o ctxcount holdouts/1RB---_1LC1RF_0LE0RD_0RB0LC_1RD0LD_0RC0RA/c/ctxcount.c && ./ctxcount 1RB0LD_1LC1RE_1LF0RA_1LA1LD_1RC0RE_---1LC 1e9 C 2 -1
```
