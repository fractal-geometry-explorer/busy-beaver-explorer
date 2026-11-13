# 1RB---_0LC0RB_1RA1LD_0RD1LE_1LF0LA_1LB0LE

bbchallenge id 130321. One of the six-state holdouts whose halting from blank tape is open (group G11).

Family **G11-X** (nested transfers between counters, `1RB---_0LC0RB`): this machine is the reference machine of the family.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | --- |
| B | 0LC | 0RB |
| C | 1RA | 1LD |
| D | 0RD | 1LE |
| E | 1LF | 0LA |
| F | 1LB | 0LE |

## What it does

Read the tape as words: `a` = `1000`, `b` = `1100`, `c` = `1110`, `d` = `10`, `e` = `110`, `f` = `100`, `g` = `11110`,
`i` = `11000`. `a`/`b` are the digits 0/1 of counters counting down, `b`/`c` the digits 0/1 of counters counting up.

- **The engine.** Most of the time the tape is `L · i e x i d · R`: `L` (digits `a`/`b`, highest on the left, `x` its
  lowest digit) and `R` (digits `b`/`c`, lowest on the left). Each visit of the head to the engine takes 1 from `L` and
  adds 1 to `R` (reference machine, from step 9,937,953: `L` = …bbb·b, bbb·a, bba·b, bba·a, … while `R` = bbb, cbb, bcb,
  ccb, …). `R` continues past separators (`e c g b e g`, `e c g`) that the carries cross: three pieces, 3 + 10 + 7 digits.
- **Epochs.** The head reaches the right end with a burst of 45–61 new cells at steps 50,631; 4,943,138; 66,904,148;
  591,307,944; 2,120,776,816; 7,329,720,424 (widths 127, 183, 244, 297, 366, 427; 516 at 10^11 steps). Each epoch
  then visits the left end, the right end and the left end once more. At each epoch start the middle of the tape holds
  one more counter (`i`; `ieai bbb eaibei`; `ibebabaabieiebbibei bbbb eibei`; …) before the fixed tail
  `bbbbbbbbbb e b i bbbbbbb ee i^k`, k = 5, 6, 7, …: nested loops, one level deeper per epoch.
- **Where it can halt.** Only in A reading 1 (A entered from C0 = 1RA and E1 = 0LA). No transition is
  rare (each at least 2.6·10^7 uses in 10^9 steps).

The twin `1RB---_0LC0RB_1RA1LD_1LE1LF_1LB0LF_0RC0LA` has the same tape as this machine at every one of the 34 end-of-tape records of the first 1.5·10^9
steps (it is about 5% faster).

## The transfer engine, third round

An engine visit (event) is the head in state A on the 0 of `d` = `10` in `L' i e x i d R` (cell −129 in the
transfer phase). Words: `a` = `1000`, `b` = `1100`, `c` = `1110`, `i` = `11000`, `e` = `110`, `g` = `11110`, and
two more digit words of the left counter, `z` = `0000` and `v` = `0100`.

- **The rule** (`lean/Events.lean`, 12 theorems, kernel, every size; `py/events.py`):
  - left: x = b → a; or x = a → b with a borrow over m digits `a` (they become `b`), stopped by the first other
    digit, which drops one step: b → a, z → b, v → z. So the left digits are v, z, b, a = 3, 2, 1, 0 in a binary
    counter that may hold digits 2 and 3 (fresh digits come as v); borrowing from an a gives a b, as in binary.
  - right: +1, lowest digit first, b = 0 and c = 1, with the carry crossing the separators S1 = `e c g b e g` and
    S2 = `e c g c` unchanged: `c^k b` → `b^k c`, `c^j S1 c^k b` → `b^j S1 b^k c`, `c^j S1 c^h S2 c^k b` → `b^j S1 b^h S2 b^k c`.
  - steps: x = b: 14k + 50; x = a: 14k + 12m + 100 (+2 for z); across S1 +152; across S1 and S2 +266 + 14h.
- **Coverage** (`python3 py/events.py --coverage 1000000000`): from step 9,932,925 to 126,682,235 the engine is
  visited 1,023,987 times, all at cell −129, and all but 21 visits are instances of the theorems (b_r 511,993,
  ab_r 383,991, ab_s1 127,843, ab_s2 117, az_s1 18, av_r 2, av_s1 2). A borrow that reaches the left end reads the
  blank cells as `z` digits: `a^4` at the end becomes `b^5`, the left counter restarts one digit longer.
- **The right counter shrinks.** It has 19 digits (3 + 10 + 6). The 21 uncovered visits are its overflows, at visit
  499,692 (so it started at 24,596) and then after 2^18, 2^17, …, 16, 8, 8, 4, 2, 1 more visits: each overflow runs
  the carry to the right end (the first is the epoch at step 66,904,148) and leaves the counter a digit shorter, and
  the phase ends at visit 1,023,987 (step 126,682,235), when no digit is left.
- **The next level.** After the phase the engine is one level deeper. At step 3·10^8 the tape reads
  `L1 i b e L2 i e i e x y d R` with L1 = `baababaaababa`, L2 = `aaaabb`: at each visit (every 50–310 steps) the
  two-digit counter `x y` counts down (bb, ab, ba, aa), L2 drops by one every fourth visit, and the right counter, now
  with a one-digit piece in front (`b`/`c` `e g` …), counts up. So an epoch is a transfer in which the left counter
  is itself fed by a slower counter, one more level per epoch. These rules are not yet proved.

## Status

Open. Lean, kernel only: the halting configurations and 10^4 steps (`lean/Blank.lean`), the sweeps of the run
and one transfer step (`event_b`) (`lean/Rules.lean`). Every engine visit of the transfer phase, for every size, 12 theorems (`lean/Events.lean`). `native_decide`: 10^7 steps. C: no halt in 10^11 steps.

## Next steps

Write the epoch as a recursive program on the list of counters (what each separator does to a carry or borrow, what
is written at the ends), so that the epoch-to-epoch map is a formula; then ask whether A can ever land on a 1.

## Scripts

`py/events.py` writes `lean/Events.lean` (`--coverage STEPS [SHOW]`: every engine visit of the run against the rules, with `c/xdump.c`).
`py/rules.py` writes `lean/Rules.lean`; `py/g11rules.py` (shared by the batch) generates the rule files. The C tools
of the batch are in `c/` here (`gcc -O2 -o X X.c`): `raw.c` (the tape at every end-of-tape record), `snap.c` and
`every.c` (snapshots), `hist.c`/`hist2.c` (where the head turns), `chg.c` (change counts per cell), `ymax.c`, `usage.c`,
`trlog.c`, `lockstep.c`, `longrun.c`.


## First look

Growth class **exp/exp** (left: exp, exponent 0.084; right: exp,
exponent 0.047). After 1,000,000,000 steps: 302 cells visited (264 left of the
start, 32 right), 185 ones.

- left, step 614,357,513: `D>0 1 0 1^3 0 1^3 0 1^3 0 1^3 0 1^3 0 1^3 0 1^3 0 1^3 0 1^3 0 1^3 0 1^3 0 1^3 0 1^3 0 1^3 0 1^4 0 1^2 0^2 1^2 0 1^3 0 1^3 0 1^3 0 1^3 0 1^3 0 1^3 0 1^4 0 1^2 0 1^4 0 1^2 0 1^3 0 1^3 0 1^4 0 1^3 0 1^2 0 1^4 0 1^3 0 1^3 0 1^2 0^2 1^2 0^2 1^2 0 1^4 0 1^3 0 1^2 0 1^4 0 1^2 0^2 1^3 0 1^2 0^2 1^3 0 1^3 0 `
- right, step 591,307,947: `1 0^3 1 0^3 1 0^3 1^2 0^2 1^2 0^2 1 0^3 1 0^3 1 0^3 1 0^3 1 0^3 1^2 0^2 1^2 0^2 1 0^3 1 0^3 1^2 0^3 1^2 0^2 1^2 0 1^2 0^2 1 0^3 1^2 0^2 1 0^3 1 0^3 1^2 0^2 1^2 0^3 1^2 0 1^2 0^3 1^2 0 1^2 0^2 1^2 0^2 1^2 0^3 1^2 0^2 1^2 0 1^2 0^3 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0 1^2 0^3 1^2 0^2 1^2 0 1^2 0^3 1^`

## Pages

- [`pages/holdouts/1RB---_0LC0RB_1RA1LD_0RD1LE_1LF0LA_1LB0LE/explainer.html`](../../pages/holdouts/1RB---_0LC0RB_1RA1LD_0RD1LE_1LF0LA_1LB0LE/explainer.html)
- [`pages/holdouts/1RB---_0LC0RB_1RA1LD_0RD1LE_1LF0LA_1LB0LE/proof-status.html`](../../pages/holdouts/1RB---_0LC0RB_1RA1LD_0RD1LE_1LF0LA_1LB0LE/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB---_0LC0RB_1RA1LD_0RD1LE_1LF0LA_1LB0LE/lean/check.sh
```
