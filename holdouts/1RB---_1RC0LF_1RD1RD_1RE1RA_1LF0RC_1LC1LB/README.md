# 1RB---_1RC0LF_1RD1RD_1RE1RA_1LF0RC_1LC1LB

bbchallenge id 43527. One of the six-state holdouts whose halting from blank tape is open (group G11, family **blocks of 3m+2 ones, binary clock**). The pages are built from [`status.json`](status.json).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | --- |
| B | 1RC | 0LF |
| C | 1RD | 1RD |
| D | 1RE | 1RA |
| E | 1LF | 0RC |
| F | 1LC | 1LB |

## Status

Open. Trusted: the clock test (tick k = 2^k applications of a map on the word, see below). Lean: the halting configurations and bounded runs (`lean/Blank.lean`); the halting context `C> x 1 1` and 12 shift rules (`lean/Rules.lean`, kernel); that every halt passes through `C> x 1 1` (`lean/HaltPred.lean`, kernel). C: no halt in 2.2·10^11 steps.

## What it does

At each new cell on the right in state E the tape is `1^(3a) 0 1^(3m1+2) 0 ... 1^(3mk+2) 0 E>0`: a number a and a
list of numbers m (`py/blocks.py`), most of them 0, 1 or 2, ending in a 2 and a run of 0s that grows by one at each
record. The run goes in **phases**. Inside a phase the steps between records double (d(k+1) = 2·d(k) + c, |c| ≤ 400
in phases 2–4), one 0 is appended and a disturbance (a 3 or a 4) walks one number to the left per record. When it
reaches the front, a changes from 4 to 1, then the front reads `1 3`, then a = 5, and the next record ends the phase
after a visit to the left end. Phase ends seen: steps 142,951,915, 776,063,293, 1,601,996,125 (a = 5 at 106,838,677,
567,646,766 and 1,331,610,646). Phase 4 (from step 1,602,340,776):

```
step             steps since last  a  numbers (cut after 23)
   2,308,202,496     352,930,955   4  1 1 2 0 0 1 1 3 1 0 1 1 1 2 1 1 1 1 2 1 2 1 3 ...
   3,014,064,227     705,861,731   4  1 1 2 0 0 1 1 3 1 2 1 1 2 1 1 1 1 2 1 2 1 3 1 ...
   4,425,787,802   1,411,723,575   4  1 1 2 0 0 1 3 1 1 2 1 1 2 1 1 1 1 2 1 2 1 3 1 ...
   7,249,234,961   2,823,447,159   4  1 1 2 0 0 3 1 1 1 2 1 1 2 1 1 1 1 2 1 2 1 3 1 ...
  12,896,129,288   5,646,894,327   4  1 1 2 0 2 1 1 1 1 2 1 1 2 1 1 1 1 2 1 2 1 3 1 ...
  24,189,918,303  11,293,789,015   1  1 1 1 1 2 0 0 1 1 1 1 1 2 1 1 2 1 1 1 1 2 1 2 ...
```

A run of 2.2·10^11 steps followed phase 4 to its end as the earlier phases foretold: a = 1 with `1 3` behind it at
step 46,777,495,938, a = 5 at 91,952,651,237, a visit to the left end at 113,640,626,946 and the phase-ending record at
136,228,769,152. The corrections c to exact doubling repeat from phase to phase: phase 4 has 177, −347, 93, 113, 9,
93, −179, 197, −179, 113, 9, 9, 361, −395, 29; phase 5 (from step 136,229,099,606) starts with five records more
(c = 29, 221, 241, 9, 9) and then repeats 177, −347, 93, 113, 9, 93, −179, 197, −179, 113, 9 up to step
222,918,842,017. Its records are 7.7 times longer than the matching ones of phase 4 (21,164,703 against 2,757,407 steps at c = 177), so if it keeps doing so phase 5 ends near 10^12 steps (an extrapolation).

Halting: A follows only D on a 1, D only C (which writes 1 and moves right), so the machine halts exactly from
`C> x 1 1` (Lean `halt_ctx`, `halt_ctx'`; also `halt_ctx_E` from `E> 1 0 1 1`; the converse, that nothing else halts two steps later, is `halt_iff_2` in `lean/HaltPred.lean`). C is entered from B on 0, E on 1,
F on 0. In 10^9 steps F never had `0 1` under it (nor B `0 x 1 1` ahead); in 10^10 steps E had `1 1 1 0` ahead 28
times, never `1 x 1 1`. Inside a phase nothing comes near; a phase end, where the left end is rewritten, is where it
would have to happen.

No exact rule for the carry was found. A finite-automata-reduction search
(`../1RB0LA_1RC1RA_1RD1RE_1LC---_0RB1LF_1RA0LE/c/far.c`) finds no certificate with at most 6 DFA states on either
side.

## The clock (test)

Seen at the visits of the right end in state C on a 0, the tape is `W (0 1 1)^n 0 C>0`: n digits 0 (blocks `1^2`) at the right end, n
growing by one per visit along a phase, and a word W further in. The clock test of the clock family
(`../1RB0LC_1LC0RB_0LE1LD_1LB1LA_0RA1LF_0LA---/py/clocktest2.py`, the general form: any end of the tape, a prefix, a repeated unit) fits:
From the visit at step 1,603,719,355 (n = 1) the word at the visit with n = k+2 is the word at the one before after exactly 2^k applications of one base map (the run of the machine from the visit with n = 1 to the next), for k = 0, ..., 8 (up to 256 applications). So this is the clock structure of `holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE` (tick k = 2^k
applications of a map on the word), checked by running the machine, not proved.

It is not yet proved: the step from one visit to the next is not the template of
`holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/py/gen_clock.py` (sweep the block into 0s, one trip into the
word, the smaller ticks, merge). Here the head works through the block itself like a binary counter before it goes
into the word, so the induction needs a different decomposition of the tick.

`TMRUN=./tmrun python3 ../1RB0LC_1LC0RB_0LE1LD_1LB1LA_0RA1LF_0LA---/py/clocktest2.py 1RB---_1RC0LF_1RD1RD_1RE1RA_1LF0RC_1LC1LB R C 2400000000 1603719355 0 0 110 10`

## Files

- `lean/HaltPred.lean` (every configuration that halts after exactly k more steps, k = 1, 2, 3, both directions) is written by
  the batch's generator: `python3 ../1RB0LD_0RC---_1LD0RF_0LE0RA_0RA1LF_0LA1LB/py/halt_pred.py 1RB---_1RC0LF_1RD1RD_1RE1RA_1LF0RC_1LC1LB 1 2 3 > lean/HaltPred.lean`.
- `lean/rules.py` writes `lean/Rules.lean` (the halting context and the shift rules, proved by `bbtools.symtm`):
  `cd lean && python3 rules.py > Rules.lean`.
- `py/blocks.py`: the records as number lists, `tmrun M 3e10 records 100000 > rec.txt; python3 blocks.py rec.txt 40`.
- `../1RB0LC_1RC0RA_1LD1LA_1RE1LD_---1RF_0RD1RA/py/periods.py rec.txt E`: the steps between records.
- The near-miss counts come from `c/ctxcount.c` and `c/forbid.c` in
  [`../1RB---_1LC1RF_0LE0RD_0RB0LC_1RD0LD_0RC0RA/c`](../1RB---_1LC1RF_0LE0RD_0RB0LC_1RD0LD_0RC0RA/c).

## Next steps

Prove the clock: find how one tick decomposes (the counter inside the block, then the trips into the word) and
write the induction for it, as `lean/Clock.lean` does for the machines of `holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE`;
with it the accelerated simulator of that folder could follow the run. Before that:

Write the carry as a transducer on (number, carry) from the block crossings, check it on the tables above, and work
out exactly what a phase end does to the front of the list (a = 4 → 1 → `1 3` → 5 → end); an exact rule for both
would give an accelerated simulator through many phases and say whether `C> x 1 1` can ever be written.

## Pages

- [`pages/holdouts/1RB---_1RC0LF_1RD1RD_1RE1RA_1LF0RC_1LC1LB/explainer.html`](../../pages/holdouts/1RB---_1RC0LF_1RD1RD_1RE1RA_1LF0RC_1LC1LB/explainer.html)
- [`pages/holdouts/1RB---_1RC0LF_1RD1RD_1RE1RA_1LF0RC_1LC1LB/proof-status.html`](../../pages/holdouts/1RB---_1RC0LF_1RD1RD_1RE1RA_1LF0RC_1LC1LB/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh      # after scripts/setup-lean.sh
holdouts/1RB---_1RC0LF_1RD1RD_1RE1RA_1LF0RC_1LC1LB/lean/check.sh
gcc -O2 -o tmrun tools/c/tmrun.c && ./tmrun 1RB---_1RC0LF_1RD1RD_1RE1RA_1LF0RC_1LC1LB 100000000000
gcc -O2 -o ctxcount holdouts/1RB---_1LC1RF_0LE0RD_0RB0LC_1RD0LD_0RC0RA/c/ctxcount.c && ./ctxcount 1RB---_1RC0LF_1RD1RD_1RE1RA_1LF0RC_1LC1LB 1e10 E 4
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB1RF_1LC0RE_1LE1LD_1RE0LC_1RA1RA_1RD---`](../1RB1RF_1LC0RE_1LE1LD_1RE0LC_1RA1RA_1RD---/README.md): rename A→F, B→D, C→E, D→A, E→B, F→C; it is this table started in state D

<!-- end of related machines -->
