# 1RB0LD_1RC0RB_1LA0RD_1LA0RE_1RF---_0LC0LF

bbchallenge id 17826. One of the six-state holdouts whose halting from blank tape is open (group G11, family **two-ended counter, (10)^n left / 110 digits right**). The pages are built from [`status.json`](status.json).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LD |
| B | 1RC | 0RB |
| C | 1LA | 0RD |
| D | 1LA | 0RE |
| E | 1RF | --- |
| F | 0LC | 0LF |

## Status

Open. Lean (kernel): halting configurations and bounded runs (`lean/Blank.lean`), the halt from `D> 1 1` (`halt_ctx`; that every halt passes through it is from the table) and
shift rules (`lean/Rules.lean`), 31 event rules for all sizes (`lean/Events.lean`). C: no halt in 2·10^10 steps.

## What it does

An **event** is the head in state A on cell 22 (cells from the start cell). Left of it: a binary counter, 4-cell
digits `1100` = 0, `1110` = 1, lowest digit next to a fixed `1110`; each event adds 1 (22n steps more for n carried
ones). Then the head crosses the fixed word `1100 1010 (1001010)^a` (a = 5 at step 10^9) to a nested counter of
3-cell digits (`000`, `001`, `010`, separated by single 1s and runs of `1001010`) and changes it: one digit after a
plain increment (40a+86 steps), more after a long carry. Example, events 1,490,258-1,490,287 (steps
1,000,000,220-1,000,012,872): event lengths 286, 794, 286, 320, 286, 960, ... (long after long carries). The left end
is visited when the left counter overflows (left end at cell -68 at step 3·10^9); late in the run (2.9·10^9) events
alternate with a 6-step event `A> 0 1 0 0 0` -> `A> 1 1 0 1 0`.

**Proved** (`lean/Events.lean`): 31 rules mined from the run (`py/mined.txt`; `py/hand.py` is empty), each for every
value of its repeat counts, among them the plain increment with any carry over the fixed word of any length.

**Coverage** (3·10^9 steps): 13,812,757 events, 6,176,693 matched (44.7%).

**Where it can halt.** From `D> 1 1` it halts (Lean `halt_ctx`); every halt passes through it (from the table: D1 = 0RE, E1 halts). In 3·10^9 steps this never happens (`evcov ... D:11`:
0 hits): the tape words put a 0 after every 1 that D reads. The CTL search (`bbtools.ctl` at K = 3, 4, 5) leaves
halting contexts `E> 1` with left `001`/`0010`/`00101` that it cannot exclude.

## Files

- `py/events.py` writes `lean/Events.lean` and `c/rules.txt`; `py/mined.txt`, `py/hand.py`.
- Batch tools in `../1RB---_1LC1RF_0LE0RD_0RB0LC_1RD0LD_0RC0RA/` (`c/evcov.c`, `py/miner.py`, `py/autoev.py`, `c/ev.c`):
  `./evcov M 3000000000 22 A c/rules.txt 0 0 D:11`.
- `lean/rules.py` writes `lean/Rules.lean`.

## Next steps

Decode the nested right counter (which digits change after a carry of length n), give the miner its digit words, and
prove the invariant that D never reads `1 1`.

## Pages

- [`pages/holdouts/1RB0LD_1RC0RB_1LA0RD_1LA0RE_1RF---_0LC0LF/explainer.html`](../../pages/holdouts/1RB0LD_1RC0RB_1LA0RD_1LA0RE_1RF---_0LC0LF/explainer.html)
- [`pages/holdouts/1RB0LD_1RC0RB_1LA0RD_1LA0RE_1RF---_0LC0LF/proof-status.html`](../../pages/holdouts/1RB0LD_1RC0RB_1LA0RD_1LA0RE_1RF---_0LC0LF/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh      # after scripts/setup-lean.sh
holdouts/1RB0LD_1RC0RB_1LA0RD_1LA0RE_1RF---_0LC0LF/lean/check.sh
gcc -O2 -o tmrun tools/c/tmrun.c && ./tmrun 1RB0LD_1RC0RB_1LA0RD_1LA0RE_1RF---_0LC0LF 20000000000
gcc -O2 -o ctxcount holdouts/1RB---_1LC1RF_0LE0RD_0RB0LC_1RD0LD_0RC0RA/c/ctxcount.c && ./ctxcount 1RB0LD_1RC0RB_1LA0RD_1LA0RE_1RF---_0LC0LF 1e9 D 2
```
