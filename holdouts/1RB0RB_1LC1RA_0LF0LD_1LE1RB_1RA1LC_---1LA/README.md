# 1RB0RB_1LC1RA_0LF0LD_1LE1RB_1RA1LC_---1LA

bbchallenge id 157503. A six-state holdout of BB(6), third of the family of six starting `1RB0RB` (holdout indices
31–36). **Open.** The tape is a row of blocks of 1s separated by single 0s; every excursion sends a left-going pass
from the right end that shifts blocks one cell right until it meets a block of length 1. The machine can halt only
if a pass reaches the *leftmost* block while that block has length 1. The passes reach deeper and deeper like a
counter, and the depth front has not reached the left end since step 29,281.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RB |
| B | 1LC | 1RA |
| C | 0LF | 0LD |
| D | 1LE | 1RB |
| E | 1RA | 1LC |
| F | --- | 1LA |

Relatives: machines 31 (`1RB0RB_0LC1RA_1RD1LC_1LA1LE_1LF0LD_---0LA`) and 32 (`1RB0RB_1LC1RA_0LE1LD_0RE1LF_---1LA_1LD0LC`)
share `A = 1RB 0RB` and `B1 = 1RA` (the right sweep flips `11 ↔ 01`) and the same plan — a pass from the right end
that stops at a block of a certain kind, and a halt only when that block is the leftmost one — but they are different
machines (not equal up to mirror image and renaming of states), and the stopping block differs: odd blocks for 31,
blocks of length 3n+3 for 32, blocks of length 1 here.

## What it does

**Where it can halt** (a hand argument from the table, with the Lean runs as the pieces). The only halting
transition is F on 0. F is entered only from C on 0, and C from B on 0 or E on 1, so a halt is `0 A> 1 0`
(`halt_a`) or `0 0 E> 1` (`halt_e`). The first never occurs after the start: A is entered from B or E moving
right, which write a 1 behind it, or from F moving left, which writes a 1 in front of it. E is entered only from D
on 0 moving left, so a halt is exactly `0 0 1 D> 0`: D on a separator with a block of length 1 left of it, and two
0s left of that. Inside the tape the 0s are single (observed at every excursion start in the first 2·10^6 steps;
not proved), so this means: **the leftmost block has length 1 and a pass
reaches it.**

**The pass** (`lean/Rules.lean`, all values, any surrounding tape). From the right end the head runs left through
the last block in states C, B, D at three steps a cell (`c_run`). At each separator it looks at the block to the
left:

| block left of the separator | what happens | theorem |
|---|---|---|
| length ≥ 2 | the block is shifted one cell right and the pass goes on | `c_shift` |
| length 1, not leftmost | the block becomes `1 1` and F turns the head around | `c_stop` |
| length 1, leftmost | F reads 0: **halt** | `c_halt` |
| the leftmost block, length ≥ 2 | the head turns right and the tape grows on the left (a *left record*) | `c_lead` |

Then the head returns right flipping pairs (`sweep_d`, `sweep_b`) and the right end grows by about one cell per
excursion (√steps growth).

**The counter.** The last left record in sight is at step 29,281. At step 29,479 (`counter_start`,
`lean/Start.lean`, `native_decide`) the tape is

    Q (110101)^26 1 1 A> 1,     Q = 1^4 0 1 0 1 0 1 0 1^3 0 1^3 0 1^3 0 1^3 0 1 0 1 0 1^3 0 1 0 1 0 1 (40 cells)

so the 26 copies of `110101` (blocks `1 1`, `1`, `1`, …) sit between the fixed prefix and the right end. Passes stop
at the first singleton block from the right; the depth of the passes follows a ruler-like pattern (period 6 at the
bottom: depths 196, 194, 192, 196, 194, then a deeper one), like a counter in a mixed radix. The deepest pass so
far moves left in steps of 2 to 12 cells, each new depth taking several times as many excursions as the last
(macro simulator, mode 1):

| depth (cells from the left end) | right-end records (2 cells each) | step |
|---|---|---|
| 162 | 780 | 1.9·10^6 |
| 136 | 1,848 | 1.2·10^7 |
| 122 | 5,028 | 9.8·10^7 |
| 110 | 10,788 | 4.6·10^8 |
| 98 | 41,016 | 6.7·10^9 |
| 88 | 171,852 | 1.2·10^11 |
| 86 | 184,332 | 1.36·10^11 |

None deeper by 1.36·10^11 steps (where the run was stopped). The leftmost block is now `1^4`; a left record (`c_lead`) can change it, and so can a
pass that turns at the second block (the return sweep rewrites the end of the leftmost block), so nothing simple
keeps it from becoming a singleton.

**Small counters.** Starting the machine on `Q (110101)^m 1 1 0` in state B (the configuration one step after
`counter_start`, with m copies) the next left record comes, without a halt, for m = 0 … 9 and 11, after 22, 28, 274,
112, 1,456, 496, 12,784, 14,536, 12,784, 4,936 and 10,696 right-end records: growing fast but irregularly in m; we
found no closed law like that of machine 31.

## Status

Open. Proved: the pass and its four endings (kernel), the configuration at step 29,479 (native); the reduction of
halting to "a pass reaches a leftmost block of length 1" is a hand argument plus the observation that interior
separators are single 0s (not proved). The macro simulator `c/mrun.c` (a copy of the one of machine 31) runs 1.36·10^11
steps without a halt.

## What is proved

| result | level | where |
|---|---|---|
| halts exactly when F reads 0 | kernel | `step_none_iff`, `lean/Blank.lean` |
| no halt in 10^4 / 10^7 steps | kernel / native | `blank_runs_kernel`, `blank_runs_native` |
| the halting patterns `0 0 E> 1`, `0 A> 1 0` | kernel | `halt_e`, `halt_a`, `lean/Rules.lean` |
| the pass and how it ends (shift, stop, halt, left record), all values, any context | kernel | `c_run`, `c_shift`, `c_stop`, `c_halt`, `c_lead`; generated by `py/gen_rules.py` |
| the right sweeps | kernel | `sweep_d`, `sweep_b` |
| step 29,479 is `Q (110101)^26 1 1 A> 1` | native | `counter_start`, `lean/Start.lean` |
| no halt in 1.36·10^11 steps; depth records above; small-counter epochs | trusted | `c/mrun.c` (`./mrun <M> 2 <steps> 1`) |

## For later

* Find the block-word macro step (where the pass stops is proved; the right-end bookkeeping and the return sweep are
  not yet summarised) and the counter it implements.
* Decide whether the leftmost block can become a singleton: that is the whole question.
* A law for the epoch length in m (the small-counter data above are irregular; maybe the right parameter is not m).

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RB_1LC1RA_0LF0LD_1LE1RB_1RA1LC_---1LA/lean/check.sh
gcc -O2 -o mrun holdouts/1RB0RB_1LC1RA_0LF0LD_1LE1RB_1RA1LC_---1LA/c/mrun.c && ./mrun 1RB0RB_1LC1RA_0LF0LD_1LE1RB_1RA1LC_---1LA 2 1e12 1
```

## Pages

- [`pages/holdouts/1RB0RB_1LC1RA_0LF0LD_1LE1RB_1RA1LC_---1LA/explainer.html`](../../pages/holdouts/1RB0RB_1LC1RA_0LF0LD_1LE1RB_1RA1LC_---1LA/explainer.html)
- [`pages/holdouts/1RB0RB_1LC1RA_0LF0LD_1LE1RB_1RA1LC_---1LA/proof-status.html`](../../pages/holdouts/1RB0RB_1LC1RA_0LF0LD_1LE1RB_1RA1LC_---1LA/proof-status.html)
