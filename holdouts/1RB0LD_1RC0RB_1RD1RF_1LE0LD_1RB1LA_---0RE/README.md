# 1RB0LD_1RC0RB_1RD1RF_1LE0LD_1RB1LA_---0RE

bbchallenge id 18358. One of the six-state holdouts whose halting from blank tape is open (group G11, family **sweeping bouncer over 0110/1110, with a counter**). The pages are built from [`status.json`](status.json).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LD |
| B | 1RC | 0RB |
| C | 1RD | 1RF |
| D | 1LE | 0LD |
| E | 1RB | 1LA |
| F | --- | 0RE |

## Status

Open. Lean (kernel): the halting configurations and bounded runs (`lean/Blank.lean`); the halt from `C> 1 0` and four shift rules (`lean/Rules.lean`); 60 event rules for all sizes (`lean/Events.lean`). C: no halt in 20,000,000,000 steps.

## What it does

**Events (new).** An *event* is the head in state E on cell 135 (cells from the start cell; the busiest state-cell
pair of steps 2.5·10^9-3·10^9: 193,833 visits; the visited tape is then cells -107..103,275, so this cell is in the
irregular part near the left end). The most frequent events are 8-step ones (`E> 0 1 0 0 0 1` -> `E> 1 1 0 1 1 1`,
`E> 0 1 0 0 1 1^a` -> `E> 1 1 0 0 0 1^a`) and ones that rewrite a run of `1110` words on the left into `1101`
(`1 0 0 1 1 0 (1110)^(a+1) 1 E> 1 1 0 0 1 1^b` -> `1 1 0 1 1 0 1 (1101)^a 1 1 0 1 E> 0 1 0 0 0 1^b`, 8a+28 steps).
60 rules mined from the run (`py/mined.txt`) are proved in Lean for every value of their repeat counts.
**Coverage** (3·10^9 steps): 2,088,696 events, 6,155 unmatched (99.7%). The events are only a small part of the
run: most steps are the sweeps over the long run (the uncovered events contain them). `C> 1 0` never occurs in that
run (`evcov ... 'C:10'`).

A bouncer with a counter: the head sweeps the whole tape; almost all of it is a run of `0110` (just after a left
turn) or `1110` (just after a right turn), each sweep turning one into the other; a short irregular part at the left
end acts as a counter. Width ~ t^0.66 (57,266 cells at 10^9 steps); turns at the ends at steps 21,462,671 (width
5,066), 31,783,946 (6,687), 54,729,845 (9,924), 84,392,656 (13,141), 156,386,041 (19,614), 252,596,376 (26,091).

Halting: F (on 0) follows only C on a 1, so the machine halts exactly from `C> 1 0` (Lean `halt_ctx`). In 10^9
steps C never read `1 0` ahead (`ctxcount M 1e9 C 3`).

## Files

- `py/events.py` writes `lean/Events.lean` (`python3 py/events.py lean > lean/Events.lean`) and `c/rules.txt` (`python3 py/events.py cov > c/rules.txt`); `py/mined.txt`, `py/hand.py`.
- Coverage: the batch's `c/evcov.c` in `../1RB---_1LC1RF_0LE0RD_0RB0LC_1RD0LD_0RC0RA/`: `./evcov 1RB0LD_1RC0RB_1RD1RF_1LE0LD_1RB1LA_---0RE 3000000000 135 E c/rules.txt 0 0 'C:10'`.
- `lean/rules.py` writes `lean/Rules.lean` (halting context and shift rules, by `bbtools.symtm`).
- Near-miss counts: `c/ctxcount.c` in `../1RB---_1LC1RF_0LE0RD_0RB0LC_1RD0LD_0RC0RA/c`.

## Next steps

The sweeps over the long run and the counter at the left end are the structure; the events at cell 135 are only the local work between sweeps. Next: the sweep rule (0110 <-> 1110 over the whole run) and the law of the left-end counter, as a macro machine.

## Pages

- [`pages/holdouts/1RB0LD_1RC0RB_1RD1RF_1LE0LD_1RB1LA_---0RE/explainer.html`](../../pages/holdouts/1RB0LD_1RC0RB_1RD1RF_1LE0LD_1RB1LA_---0RE/explainer.html)
- [`pages/holdouts/1RB0LD_1RC0RB_1RD1RF_1LE0LD_1RB1LA_---0RE/proof-status.html`](../../pages/holdouts/1RB0LD_1RC0RB_1RD1RF_1LE0LD_1RB1LA_---0RE/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh      # after scripts/setup-lean.sh
holdouts/1RB0LD_1RC0RB_1RD1RF_1LE0LD_1RB1LA_---0RE/lean/check.sh
gcc -O2 -o tmrun tools/c/tmrun.c && ./tmrun 1RB0LD_1RC0RB_1RD1RF_1LE0LD_1RB1LA_---0RE 20000000000
gcc -O2 -o ctxcount holdouts/1RB---_1LC1RF_0LE0RD_0RB0LC_1RD0LD_0RC0RA/c/ctxcount.c && ./ctxcount 1RB0LD_1RC0RB_1RD1RF_1LE0LD_1RB1LA_---0RE 1e9 C 3
```
