# 1RB0LD_0RC---_1LD0RF_0LE0RA_0RA1LF_0LA1LB

bbchallenge id 2336. One of the six-state holdouts whose halting from blank tape is open (group G11, family **two-ended counter, (011)^n left / 10 right**). The pages are built from [`status.json`](status.json).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LD |
| B | 0RC | --- |
| C | 1LD | 0RF |
| D | 0LE | 0RA |
| E | 0RA | 1LF |
| F | 0LA | 1LB |

## Status

Open. Lean: the halting configurations and bounded runs (`lean/Blank.lean`); the halting contexts `A> 0 1` and `1 F> 1` and 9 shift rules (`lean/Rules.lean`, kernel); the converse, that every configuration halting one step later is one of the two (`lean/HaltPred.lean`, kernel). C: no halt in 20,000,000,000 steps.

## What it does

The left end is a run of 011 after the head's cells (A>0 0 1 (011)^n), one copy longer at each visit to the left end (13 at step 1,530,193,864, 14 at step 1,815,265,479). The right end is a run of 10. In between lies an irregular word of 10, 110 and 1000. No exact rule has been found.

Halting: The halting transition is B reading a 1. B is entered from A reading a 0 (A writes 1 and moves right), or from F reading a 1 (F writes 1 and moves left), so the machine halts exactly from A> 0 1 or 1 F> 1 (Lean: halt_ctx, halt_ctx_F; the converse, that nothing else halts one step later, is halt_pred_1 in lean/HaltPred.lean, and halts_blank_pred_1 says a halting run from blank passes through one of the two). In the first 109 steps A never had 0 1 under and after it (its contexts are 0 0 and 1 0), and F reading a 1 never had a 1 on its left (ctxcount M 1e9 F 2 -1: 0 0, 0 1, 1 0). No near misses at all.

Two local laws hold throughout the first 10^9 steps: the cell right of A is always 0 (225,806,362 times), and F
reading a 1 never has a 1 on its left; the halt is exactly a break of one of them (`A> 0 1` or `1 F> 1`). Inside the
tape the runs of 1s have length 1 or 2 and the runs of 0s length 1 to 6 (300 tapes sampled every 1,000,003 steps).

Automata tried: `../1RB0LA_1RC1RA_1RD1RE_1LC---_0RB1LF_1RA0LE/c/far.c` (finite automata reduction) finds no
certificate with a DFA of at most 7 states on either side; `bbtools.ctl` with windows of 4–8 cells finds abstract
halts through `1 1 1`, which occurs on the real tape only rarely (first at step 5,506 at the left end).

## Files

- `lean/rules.py` writes `lean/Rules.lean` (the halting context and the shift rules, proved by `bbtools.symtm`):
  `cd lean && python3 rules.py > Rules.lean`.
- `py/halt_pred.py` writes `lean/HaltPred.lean` (every configuration that halts after exactly k more steps, k = 1, 2;
  shared by the batch): `python3 py/halt_pred.py 1RB0LD_0RC---_1LD0RF_0LE0RA_0RA1LF_0LA1LB 1 2 > lean/HaltPred.lean`.
- The near-miss counts come from `c/ctxcount.c` and `c/forbid.c` in
  [`../1RB---_1LC1RF_0LE0RD_0RB0LC_1RD0LD_0RC0RA/c`](../1RB---_1LC1RF_0LE0RD_0RB0LC_1RD0LD_0RC0RA/c) (shared by the
  batch): `./ctxcount M 1e10 S 3`, `./forbid M 1e10 S:111`.

## Next steps

Look for the invariant behind the missing contexts: a closed tape language over the words `10`, `110`, `1000`, `011` rather than fixed windows.

## Pages

- [`pages/holdouts/1RB0LD_0RC---_1LD0RF_0LE0RA_0RA1LF_0LA1LB/explainer.html`](../../pages/holdouts/1RB0LD_0RC---_1LD0RF_0LE0RA_0RA1LF_0LA1LB/explainer.html)
- [`pages/holdouts/1RB0LD_0RC---_1LD0RF_0LE0RA_0RA1LF_0LA1LB/proof-status.html`](../../pages/holdouts/1RB0LD_0RC---_1LD0RF_0LE0RA_0RA1LF_0LA1LB/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh      # after scripts/setup-lean.sh
holdouts/1RB0LD_0RC---_1LD0RF_0LE0RA_0RA1LF_0LA1LB/lean/check.sh
gcc -O2 -o tmrun tools/c/tmrun.c && ./tmrun 1RB0LD_0RC---_1LD0RF_0LE0RA_0RA1LF_0LA1LB 20000000000
gcc -O2 -o ctxcount holdouts/1RB---_1LC1RF_0LE0RD_0RB0LC_1RD0LD_0RC0RA/c/ctxcount.c && ./ctxcount 1RB0LD_0RC---_1LD0RF_0LE0RA_0RA1LF_0LA1LB 1e9 A 2
```
