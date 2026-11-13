# 1RB0LA_0RC1RF_0LD1RE_1LA0RB_0RD---_1RA1RD

bbchallenge id 21606. One of the six-state holdouts whose halting from blank tape is open (group G11, family **ones-runs and zero-gaps, two-way list**). The pages are built from [`status.json`](status.json).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LA |
| B | 0RC | 1RF |
| C | 0LD | 1RE |
| D | 1LA | 0RB |
| E | 0RD | --- |
| F | 1RA | 1RD |

## Status

Open. Lean (kernel): the halting configurations and bounded runs (`lean/Blank.lean`); the halt from `B> 0 1 1` and 8 shift rules (`lean/Rules.lean`); 40 event rules for all sizes (`lean/Events.lean`). C: no halt in 20,000,000,000 steps.

## What it does

**Events (new).** An *event* is the head in state A on cell 0 (the start cell; the busiest state-cell pair of steps
2.5·10^9-3·10^9: 21,832,461 visits). Half of all events are the 4-step `A> 0 0 0 0` -> `A> 1 1 0 0`; the next ones
are `0 0 A> 1 1 0^7` -> `0 1 A> 0^6 1 0 0` (18 steps; exactly 2^24 = 16,777,216 times in 3·10^9 steps) and two with
one repeat each (8,388,597 and 8,388,584 times, about 2^23): the hit counts halve from rule to rule like the digits
of a binary counter. 40 rules mined from the run (`py/mined.txt`) are proved in Lean for every value of their repeat
counts. **Coverage** (3·10^9 steps): 101,546,466 events, 18,500 unmatched (99.98%). `B> 0 1 1` never occurs in that
run (`evcov ... 'B:011'`). It follows (not as a theorem) that a halt would have to come from an uncovered event.

The tape is a list of numbers written in two ways. When the head is at the right end, they are runs of 1s separated by single 0s (1^4 0 1^8 0 1^5 0 1^23 0 ...); when it is at the left end, the same numbers are gaps of 0s between single 1s (1 0^4 1 0^8 1 0^5 1 0^23 ...). State A, running left over a run of 1s, erases it (Lean: (1)^n A> 1 becomes A> 1 (0)^n), and the sweep right writes the runs back. The left end is a run A>0 0 (10)^n lengthened by one at each visit (45 to 48 between steps 7.4·108 and 1.5·109); the right end is one run of 1s lengthened by one at each new cell on the right (34 to 38 in the same stretch). In between, the list changes slowly and irregularly.

Halting: The halting transition is E reading a 1. E is entered only from C reading a 1 (C writes 1 and moves right), and C only from B reading a 0 (B writes 0 and moves right). In the first 109 steps B had 1 0 1 ahead 25 times and 1 1 0 10 times (the last at step 740,088,686, just after a visit to the left end), and never 0 1 1.

## Files

- `py/events.py` writes `lean/Events.lean` (`python3 py/events.py lean > lean/Events.lean`) and `c/rules.txt` (`python3 py/events.py cov > c/rules.txt`); `py/mined.txt`, `py/hand.py`.
- Coverage: the batch's `c/evcov.c` in `../1RB---_1LC1RF_0LE0RD_0RB0LC_1RD0LD_0RC0RA/`: `./evcov 1RB0LA_0RC1RF_0LD1RE_1LA0RB_0RD---_1RA1RD 3000000000 0 A c/rules.txt 0 0 'B:011'`.
- `lean/rules.py` writes `lean/Rules.lean` (the halting context and the shift rules, proved by `bbtools.symtm`):
  `cd lean && python3 rules.py > Rules.lean`.
- The near-miss counts come from `c/ctxcount.c` and `c/forbid.c` in
  [`../1RB---_1LC1RF_0LE0RD_0RB0LC_1RD0LD_0RC0RA/c`](../1RB---_1LC1RF_0LE0RD_0RB0LC_1RD0LD_0RC0RA/c) (shared by the
  batch): `./ctxcount M 1e10 S 3`, `./forbid M 1e10 S:111`.

## Next steps

Read the 40 rules as a macro machine (which numbers of the list the counter at the start cell changes) and decode the 18,500 uncovered events (visits to the ends). The visit law of the list (what one pass of the head does to a list of numbers, for all lists) is not yet written down.

## Pages

- [`pages/holdouts/1RB0LA_0RC1RF_0LD1RE_1LA0RB_0RD---_1RA1RD/explainer.html`](../../pages/holdouts/1RB0LA_0RC1RF_0LD1RE_1LA0RB_0RD---_1RA1RD/explainer.html)
- [`pages/holdouts/1RB0LA_0RC1RF_0LD1RE_1LA0RB_0RD---_1RA1RD/proof-status.html`](../../pages/holdouts/1RB0LA_0RC1RF_0LD1RE_1LA0RB_0RD---_1RA1RD/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh      # after scripts/setup-lean.sh
holdouts/1RB0LA_0RC1RF_0LD1RE_1LA0RB_0RD---_1RA1RD/lean/check.sh
gcc -O2 -o tmrun tools/c/tmrun.c && ./tmrun 1RB0LA_0RC1RF_0LD1RE_1LA0RB_0RD---_1RA1RD 20000000000
gcc -O2 -o ctxcount holdouts/1RB---_1LC1RF_0LE0RD_0RB0LC_1RD0LD_0RC0RA/c/ctxcount.c && ./ctxcount 1RB0LA_0RC1RF_0LD1RE_1LA0RB_0RD---_1RA1RD 1e9 B 3
```
