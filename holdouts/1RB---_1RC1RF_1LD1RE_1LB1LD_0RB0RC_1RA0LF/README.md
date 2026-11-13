# 1RB---_1RC1RF_1LD1RE_1LB1LD_0RB0RC_1RA0LF

bbchallenge id 98843. One of the six-state holdouts whose halting from blank tape is open (group G11, family **clock and word map (block grows by 4, right end)**). The pages are built from [`status.json`](status.json).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | --- |
| B | 1RC | 1RF |
| C | 1LD | 1RE |
| D | 1LB | 1LD |
| E | 0RB | 0RC |
| F | 1RA | 0LF |

## Status

Open.

- Lean, kernel: the clock for every k and every word, for each tick whose 2^k P-steps all come back, at the right end of the tape (`lean/MirrorBridge.lean`,
  `tick_right_end`, `tick`), proved on the mirror image of the machine (`lean/MirrorMachine.lean`,
  `lean/MirrorRules.lean`, `lean/MirrorClock.lean`) and carried back by a mirror lemma.
- Lean, kernel (`lean/Rules.lean`): the halting context `B> 1 0 1` (`halt_ctx`) and 11 shift rules; (`lean/HaltPred.lean`) the converse, that every halt passes through `B> 1 0 1` (`halt_iff_2`, `halts_blank_pred_2`).
- Lean (`lean/Blank.lean`): the halting configurations, no halt in 10,000 steps (kernel), 10,000,000 (`native_decide`).
- Trusted computation: the exact accelerated run (`holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/py/clock.py`) agrees with `tools/c/tmrun.c` at all 81
  visits of the right end in the first 2·10^10 steps and follows the run to step 2.39·10^248 without a halt.
- C: no halt in 100,000,000,000 steps.

## The clock

Look at the run in the mirror (left and right swapped, `lean/MirrorMachine.lean`); there the clock is at the left end.
Write `J(j, W)` for `E> 1^(6+4j) 0 W` (state E on the first 1 of a block of 6+4j ones, a word W to its right).

- **Sweep** (`rule_sweep`): `0^4 E> 1^(6+4n) 0` becomes `0 0 0 1 0^(6+4n) F> 0` in 4n+10 steps (F erases the block).
- **P-step** (`PStep`): `0^6 F> 0 W` reaches `E> 1^6 0 W'` — one trip of the head through the word and back; this
  defines the map P on words. It must hold for every tape to the left.
- **Merge** (`rule_merge`): `0 0 0 1 E> 1` becomes `E> 1^5` in 14 steps.
- **Tick** (`tick`): if W reaches W' by 2^j P-steps of total cost E, then `0^4 J(j, W)` reaches `J(j+1, W')` in
  exactly `E + 28·2^j − 4` steps, for every j, W and tape to the left. Proof by strong induction on j as in the five
  machines of `holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE` (sweep, one P-step, ticks 0..j−1, merge);
  `lean/MirrorBridge.lean` turns it into the statement for this machine (`mir`, `step_mir`, `steps_mir`,
  `tick_right_end`).

In the machine itself (right end) the visits are the moments the head is in state C on a 0 with one 0 between it and
a block `1^L`; along a phase L grows by 4 per visit and the time between visits doubles.

**Phases of the exact accelerated run** (`holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/py/clock.py 1RB---_1RC1RF_1LD1RE_1LB1LD_0RB0RC_1RA0LF run 400`, stopped at step 2.39·10^248),
with their first and last visit:

| starts at step | block | last tick at step | block | ticks |
|---|---|---|---|---|
| 5.7718·10^8 | 1^1 | 3.7457·10^13 | 1^161 | 40 |
| 2.0070·10^22 | 1^1 | 6.5767·10^26 | 1^337 | 84 |
| 6.7309·10^26 | 1^5 | 1.6673·10^57 | 1^741 | 184 |
| 8.0977·10^140 | 1^1 | 7.7989·10^245 | 1^3245 | 811 |

Between these phases the run is in a **second regime**: the block at the end is a single 1 (`... 1^N 0 1 0 C>0`) while
the block N to its left grows by 4 per visit and the time between visits doubles — a clock one block further in,
whose tick has `1 0` beside it instead of four 0s and so is not the theorem above. It runs from 3.8·10^13 to
2.0·10^22, from 1.67·10^57 to 8.1·10^140 (one visit with block 1^2 at 2.64·10^86), and from 7.98·10^245 to the end of
the run (814 visits, the word growing from 7,764 to 11,020 cells). The accelerated run does these visits one at a
time (each with the P memo), which is why it slows down there. At the end of a first-block phase the block is
dissolved into the word (|W| 4,519 → 7,764 after the 1^3245 phase).

The earlier extrapolation (phase 3 of the records lasting beyond 10^16 steps) is superseded: in the run the clock
phase that contains those records ends at 3.7457·10^13, and the doubling continues in the second regime.

**Clock test** (`../1RB0LC_1LC0RB_0LE1LD_1LB1LA_0RA1LF_0LA---/py/clocktest2.py`, before the proof, against the
machine run): from the visit at step 877,164,131 the word at each visit is the word at the previous one after
1024, 2048, 4096 applications of one base map, the doubling of the clock.

## The records (earlier view)

At each new cell on the right in state E the tape is `1^2 0 (1^(4m1+1) 0) ... (1^(4mk+1) 0) 1 E>0`: a list of
digits m (`py/digits.py`; 71 of the 80 such records of a 3·10^10-step run have this form). The run goes in
**phases**. Inside a phase the steps between records satisfy d(k+1) = 2·d(k) + c with |c| ≤ 324, the last digit
grows by one per record, and a disturbance walks left one digit per record. A phase ends after the head visits the
left end; the phases seen end at steps 73,627 and 877,024,800. Phase 3 (records from step 877,024,856):

```
step             steps since last  digits (one character each, [m] for m > 9)
    877,024,856              56   00000000000111100000000000000000011110010011100210101020010000000000000011
    877,024,980             124   000000000001111000000000000000000111100100111002101010200100000000000022
    877,025,240             260   0000000000011110000000000000000001111001001110021010102001000000000033
...
  2,020,119,422     571,547,442   000000000001111000000000000010011110010011100210101010118[24]
  3,163,214,310   1,143,094,888   000000000001111000000000001000011110010011100210101010118[25]
  5,449,404,090   2,286,189,780   000000000001111000000000100000011110010011100210101010118[26]
 10,021,783,654   4,572,379,564   000000000001111000000010000000011110010011100210101010118[27]
 19,166,542,786   9,144,759,132   000000000001111000001000000000011110010011100210101010118[28]
```

At the start of the phase the last two digits grow together (`11`, `22`, `33`, ...); when the pair reaches 8 it
stops and the disturbance moves left, changing the digits it passes (`...0210102000118[10]`, `...0210103...`); from
step 2,020,119,422 it is a lone 1 walking through 0s. It has about 20 digits to cross before the left end; at one
digit per doubling record the phase lasts beyond about 2^20·9·10^9 ≈ 10^16 steps (extrapolation, not proved).

Halting: A follows only F on a 0 (`1RA`), F follows B on a 1 or F on a 1 (which erases it), so the machine halts
exactly from `B> 1 0 1` (Lean `halt_ctx`, and `halt_iff_2` for the converse). In 10^10 steps B never had `1 0 1` ahead and F never `0 1`; nothing like
it happens inside a phase, so halting, if it happens, happens at a phase end.

No exact rule for the walk was found: the time per record doubles because the head runs the whole list between
records, and the walk changes nonzero digits in a way not yet written down. A finite-automata-reduction search
(`../1RB0LA_1RC1RA_1RD1RE_1LC---_0RB1LF_1RA0LE/c/far.c`) finds no certificate with a DFA of at most 6 states on
either side.

## Files

- `lean/HaltPred.lean` (every configuration that halts after exactly k more steps, k = 1, 2, 3, both directions) is written by
  the batch's generator: `python3 ../1RB0LD_0RC---_1LD0RF_0LE0RA_0RA1LF_0LA1LB/py/halt_pred.py 1RB---_1RC1RF_1LD1RE_1LB1LD_0RB0RC_1RA0LF 1 2 3 > lean/HaltPred.lean`.
- `holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/py/gen_clock.py 1RB---_1RC1RF_1LD1RE_1LB1LD_0RB0RC_1RA0LF` writes `lean/MirrorMachine.lean`, `lean/MirrorRules.lean`, `lean/MirrorClock.lean` and
  `lean/MirrorBridge.lean` (the machine is in `MIRROR`, `ONES_FIRST` and `VISIT` of `clock.py`).
- `python3 holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/py/clock.py 1RB---_1RC1RF_1LD1RE_1LB1LD_0RB0RC_1RA0LF tmcheck 2e10` compares the accelerated run with `tmrun` at every visit;
  `... run 400` follows the phases (about 15 minutes to 2.4·10^248, memory grows to 4 GB).
- `lean/rules.py` writes `lean/Rules.lean` (the halting context and the shift rules, proved by `bbtools.symtm`):
  `cd lean && python3 rules.py > Rules.lean`.
- `py/digits.py`: the records as digit lists, `tmrun M 3e10 records 100000 > rec.txt; python3 digits.py rec.txt 34`.
- `../1RB0LC_1RC0RA_1LD1LA_1RE1LD_---1RF_0RD1RA/py/periods.py rec.txt E`: the steps between records and the
  corrections to doubling.
- The near-miss counts come from `c/ctxcount.c` and `c/forbid.c` in
  [`../1RB---_1LC1RF_0LE0RD_0RB0LC_1RD0LD_0RC0RA/c`](../1RB---_1LC1RF_0LE0RD_0RB0LC_1RD0LD_0RC0RA/c).

## Next steps

Prove the tick of the second regime (`1^N 0 1 0` at the end, the block N growing by 4: the same induction with the
left context `1 0` in the mirror) and add it to the accelerated run; then describe what a phase end does to the word,
where the halting context `B> 1 0 1` would have to appear.

## Pages

- [`pages/holdouts/1RB---_1RC1RF_1LD1RE_1LB1LD_0RB0RC_1RA0LF/explainer.html`](../../pages/holdouts/1RB---_1RC1RF_1LD1RE_1LB1LD_0RB0RC_1RA0LF/explainer.html)
- [`pages/holdouts/1RB---_1RC1RF_1LD1RE_1LB1LD_0RB0RC_1RA0LF/proof-status.html`](../../pages/holdouts/1RB---_1RC1RF_1LD1RE_1LB1LD_0RB0RC_1RA0LF/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh      # after scripts/setup-lean.sh
holdouts/1RB---_1RC1RF_1LD1RE_1LB1LD_0RB0RC_1RA0LF/lean/check.sh
gcc -O2 -o tmrun tools/c/tmrun.c && ./tmrun 1RB---_1RC1RF_1LD1RE_1LB1LD_0RB0RC_1RA0LF 100000000000
gcc -O2 -o ctxcount holdouts/1RB---_1LC1RF_0LE0RD_0RB0LC_1RD0LD_0RC0RA/c/ctxcount.c && ./ctxcount 1RB---_1RC1RF_1LD1RE_1LB1LD_0RB0RC_1RA0LF 1e10 F 2
```
