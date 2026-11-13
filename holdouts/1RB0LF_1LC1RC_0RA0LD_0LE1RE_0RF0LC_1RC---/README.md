# 1RB0LF_1LC1RC_0RA0LD_0LE1RE_0RF0LC_1RC---

bbchallenge id 83189. One of the six-state holdouts whose halting from blank tape is open (group G11, family **two-ended counter, (10)^n left / 110 digits right**). The pages are built from [`status.json`](status.json).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LF |
| B | 1LC | 1RC |
| C | 0RA | 0LD |
| D | 0LE | 1RE |
| E | 0RF | 0LC |
| F | 1RC | --- |

## Status

Open. Lean: the halting configurations and bounded runs (`lean/Blank.lean`); the halting context `1 C> 1 1` and 8 shift rules (`lean/Rules.lean`, kernel); the converse, that every halt passes through `1 C> 1 1` (`lean/HaltPred.lean`, kernel). C: no halt in 20,000,000,000 steps.

## What it does

Both ends of the tape grow logarithmically. The left end is a long run of 10 after a few 0s (24 copies at step 556,283,168, 25 at step 1,678,517,170). The right end is a run of 110 (15 copies at step 1.8·109). In between lies a word of short digits (10, 110, 1110) in no fixed order that changes at each pass, like the digits of a counter, and decides when the head next reaches the left end. It is the same kind of machine as 1RB---_1LC1RF_0LE0RD_0RB0LC_1RD0LD_0RC0RA. No exact rule for the middle has been found.

Halting: The halting transition is F reading a 1. F is entered from A reading a 1 (moving left) or E reading a 0 (moving right). A is entered only from C reading a 0, which writes a 0 to A's left, so the first way is impossible. E is entered from D reading a 0 (moving left, and then F reads the 0 D wrote) or a 1 (moving right), so the halt needs D> 1 0 1; D is entered only from C reading a 1 and moving left, which gives 1 C> 1 1. Lean proves the steps from each context to the halt (halt_ctx, halt_ctx_A, halt_ctx_E), and the converse: a configuration halts three steps later if and only if it is 1 C> 1 1 (halt_iff_3, lean/HaltPred.lean). In the first 109 steps C had 1 C> 1 0 about 2.9·107 times and 0 C> 1 1 about 8.8·107 times, but never 1 C> 1 1: two of the three cells match all the time, the third never.

C's surroundings in 10^9 steps (`./ctxcount M 1e9 C 3 -1`): `0 C> 1 0` 29,411,582, `0 C> 1 1` 88,235,359,
`1 C> 0 0` 147,058,544, `1 C> 0 1` 29,411,751, `1 C> 1 0` 29,412,045, `0 C> 0 0` 22 times, never `1 C> 1 1`. Inside
the tape the runs of 1s have length 1 to 3; runs of 0s of length 3, 6, 9, 12 are rare (25, 7, 1, 1 in 300 sampled
tapes) while 4, 5, 7, 8, 10, 11 are common, a hint of a residue mod 3 that a proof would track.

Automata tried: `../1RB0LA_1RC1RA_1RD1RE_1LC---_0RB1LF_1RA0LE/c/far.c` (finite automata reduction) finds no
certificate with a DFA of at most 7 states on either side.

## Files

- `lean/HaltPred.lean` (every configuration that halts after exactly k more steps, k = 1, 2, 3, both directions) is written by
  the batch's generator: `python3 ../1RB0LD_0RC---_1LD0RF_0LE0RA_0RA1LF_0LA1LB/py/halt_pred.py 1RB0LF_1LC1RC_0RA0LD_0LE1RE_0RF0LC_1RC--- 1 2 3 > lean/HaltPred.lean`.
- `lean/rules.py` writes `lean/Rules.lean` (the halting context and the shift rules, proved by `bbtools.symtm`):
  `cd lean && python3 rules.py > Rules.lean`.
- The near-miss counts come from `c/ctxcount.c` and `c/forbid.c` in
  [`../1RB---_1LC1RF_0LE0RD_0RB0LC_1RD0LD_0RC0RA/c`](../1RB---_1LC1RF_0LE0RD_0RB0LC_1RD0LD_0RC0RA/c) (shared by the
  batch): `./ctxcount M 1e10 S 3`, `./forbid M 1e10 S:111`.

## Next steps

Find the rule of the middle counter and why `1 C> 1 1` never occurs although both of its halves are common; that pattern of near misses suggests a parity invariant.

## Pages

- [`pages/holdouts/1RB0LF_1LC1RC_0RA0LD_0LE1RE_0RF0LC_1RC---/explainer.html`](../../pages/holdouts/1RB0LF_1LC1RC_0RA0LD_0LE1RE_0RF0LC_1RC---/explainer.html)
- [`pages/holdouts/1RB0LF_1LC1RC_0RA0LD_0LE1RE_0RF0LC_1RC---/proof-status.html`](../../pages/holdouts/1RB0LF_1LC1RC_0RA0LD_0LE1RE_0RF0LC_1RC---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh      # after scripts/setup-lean.sh
holdouts/1RB0LF_1LC1RC_0RA0LD_0LE1RE_0RF0LC_1RC---/lean/check.sh
gcc -O2 -o tmrun tools/c/tmrun.c && ./tmrun 1RB0LF_1LC1RC_0RA0LD_0LE1RE_0RF0LC_1RC--- 20000000000
gcc -O2 -o ctxcount holdouts/1RB---_1LC1RF_0LE0RD_0RB0LC_1RD0LD_0RC0RA/c/ctxcount.c && ./ctxcount 1RB0LF_1LC1RC_0RA0LD_0LE1RE_0RF0LC_1RC--- 1e9 C 3 -1
```
