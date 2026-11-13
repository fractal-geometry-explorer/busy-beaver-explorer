# 1RB0LC_1RC0RA_1LD1LA_1RE1LD_---1RF_0RD1RA

bbchallenge id 133770. One of the six-state holdouts whose halting from blank tape is open (group G11, family **blocks of 4m+1 ones, binary clock**). The pages are built from [`status.json`](status.json).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LC |
| B | 1RC | 0RA |
| C | 1LD | 1LA |
| D | 1RE | 1LD |
| E | --- | 1RF |
| F | 0RD | 1RA |

## Status

Open. Trusted: the clock test (tick k = 2^k applications of a map on the word, see below). Lean: the halting configurations and bounded runs (`lean/Blank.lean`); the halting context `F> 0 0 0`, the 21-step rule at the right end and 8 shift rules (`lean/Rules.lean`, kernel); that every halt passes through `F> 0 0 0` (`lean/HaltPred.lean`, kernel). C: no halt in 30,000,000,000 steps.

## What it does

At each new cell on the right in state B the tape is mostly a list of digits `1^(4m+1) 0` (most of them 0), a big
block of 1s and `0 1 0 1 B>0`. New right cells come in bursts: `... 1^n 0 1 0 1 0 1 1 C>0` becomes
`... 1^(n+4) 0 1 0 1 B>0` in 21 steps (Lean `right_end_grow`), one more cell, then a long pause in which the head goes
to the left end and back. In the middle of a pause the digits look scrambled and the big block is cut into pieces;
at its end the list is (usually) restored and the big block is four 1s longer. The pauses double
(`py/periods.py`, 3·10^10 steps):

```
     459,930       919,858     1,839,714     3,679,426     7,358,850    14,717,698    29,435,394    58,870,786
 117,741,564   235,483,274   470,953,978   941,907,956 1,880,929,872 3,759,931,386 7,519,862,778
```

The first eight are exactly twice the previous one minus 2; the other corrections are −8, 146, −12,570, 0,
−2,886,040, −1,928,358, 6 (the larger ones when digits near the left end change). The number of head reversals per
period doubles exactly too (67,280,896 then 134,561,792 between the records at 487,921,948, 958,875,948 and
1,900,783,903). Each period is presumably one full count of a binary counter with one more digit than the last.

Halting: E (on 0) follows only D on a 0; D after C or D (moving left) gives E the 1 they wrote, so the only way in is
F on a 0 moving right: `F> 0 0 0` (Lean `halt_ctx`; the converse, that nothing else halts two steps later, `halt_iff_2`). Near misses `F> 0 0 1` at steps 257, 11,457, 16,839,809 and
2,371,684,619 (the only ones up to that step; `forbid` with `FROM`), each just after a long block was written at the
very left end: `1^54 F>0 0 1 0 1 0 1 ...` at the last one. The halt is the same picture with one more 0.

No exact rule for a period was found. A finite-automata-reduction search
(`../1RB0LA_1RC1RA_1RD1RE_1LC---_0RB1LF_1RA0LE/c/far.c`) finds no certificate with at most 6 DFA states on either
side.

## The clock (test)

Seen at the visits of the right end in state C on a 0, the tape is `W 1^(4n+1) 0 1 0 1 1 C>0`: a block of 4n+1 ones near the right end, n
growing by one per visit along a phase, and a word W further in. The clock test of the clock family
(`../1RB0LC_1LC0RB_0LE1LD_1LB1LA_0RA1LF_0LA---/py/clocktest2.py`, the general form: any end of the tape, a prefix, a repeated unit) fits:
From the visit at step 16,962,494 (n = 8) the word at each later visit of the phase is the word at the one before after 2^k applications of one base map, up to 2^14 applications (the visit at step 252,438,652). So this is the clock structure of `holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE` (tick k = 2^k
applications of a map on the word), checked by running the machine, not proved.

It is not yet proved: the step from one visit to the next is not the template of
`holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/py/gen_clock.py` (sweep the block into 0s, one trip into the
word, the smaller ticks, merge). Here the head works through the block itself like a binary counter before it goes
into the word, so the induction needs a different decomposition of the tick.

`TMRUN=./tmrun python3 ../1RB0LC_1LC0RB_0LE1LD_1LB1LA_0RA1LF_0LA---/py/clocktest2.py 1RB0LC_1RC0RA_1LD1LA_1RE1LD_---1RF_0RD1RA R C 2400000000 16962494 0 110101 1111 16`

## Files

- `lean/HaltPred.lean` (every configuration that halts after exactly k more steps, k = 1, 2, 3, both directions) is written by
  the batch's generator: `python3 ../1RB0LD_0RC---_1LD0RF_0LE0RA_0RA1LF_0LA1LB/py/halt_pred.py 1RB0LC_1RC0RA_1LD1LA_1RE1LD_---1RF_0RD1RA 1 2 3 > lean/HaltPred.lean`.
- `lean/rules.py` writes `lean/Rules.lean` (the halting context, the right-end rule and the shift rules, proved by
  `bbtools.symtm`): `cd lean && python3 rules.py > Rules.lean`.
- `py/periods.py` (shared by the three digit machines of the batch): `tmrun M 3e10 records 100000 > rec.txt;
  python3 py/periods.py rec.txt B` prints the steps between records and the corrections to doubling.
- The near-miss search: `FROM=20000000 ./forbid M 3e10 F:001` with `c/forbid.c` of
  [`../1RB---_1LC1RF_0LE0RD_0RB0LC_1RD0LD_0RC0RA/c`](../1RB---_1LC1RF_0LE0RD_0RB0LC_1RD0LD_0RC0RA/c).

## Next steps

Prove the clock: find how one tick decomposes (the counter inside the block, then the trips into the word) and
write the induction for it, as `lean/Clock.lean` does for the machines of `holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE`;
with it the accelerated simulator of that folder could follow the run. Before that:

Write one period as a rule: the left part is a counter whose full cycle is a period; find its digits (the scrambled
middle of a period is that counter written over the list and the big block) and the one-step rule of the counter
from the shift rules, then check it against the period table above and simulate far ahead. The question for
halting is what the left end looks like at the start of each period.

## Pages

- [`pages/holdouts/1RB0LC_1RC0RA_1LD1LA_1RE1LD_---1RF_0RD1RA/explainer.html`](../../pages/holdouts/1RB0LC_1RC0RA_1LD1LA_1RE1LD_---1RF_0RD1RA/explainer.html)
- [`pages/holdouts/1RB0LC_1RC0RA_1LD1LA_1RE1LD_---1RF_0RD1RA/proof-status.html`](../../pages/holdouts/1RB0LC_1RC0RA_1LD1LA_1RE1LD_---1RF_0RD1RA/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh      # after scripts/setup-lean.sh
holdouts/1RB0LC_1RC0RA_1LD1LA_1RE1LD_---1RF_0RD1RA/lean/check.sh
gcc -O2 -o tmrun tools/c/tmrun.c && ./tmrun 1RB0LC_1RC0RA_1LD1LA_1RE1LD_---1RF_0RD1RA 20000000000
gcc -O2 -o ctxcount holdouts/1RB---_1LC1RF_0LE0RD_0RB0LC_1RD0LD_0RC0RA/c/ctxcount.c && ./ctxcount 1RB0LC_1RC0RA_1LD1LA_1RE1LD_---1RF_0RD1RA 1e10 F 3
```
