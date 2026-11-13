# 1RB1LC_1LA1RB_1LD0LA_1RE1RD_---1RF_1LB0RF

bbchallenge id 124655. One of the six-state holdouts whose halting from blank tape is open. Family: **binary
accumulator fed by a counter**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LC |
| B | 1LA | 1RB |
| C | 1LD | 0LA |
| D | 1RE | 1RD |
| E | --- | 1RF |
| F | 1LB | 0RF |

## What it does

**The counter.** Between overflows the tape is

    Z(s, v, W) =  (1 1 0^(5a_1-2)) (1 1 0^(5a_2-2)) ... (1 1 0^(5a_m-2)) F>0 W      (blank on both sides)

where (a_1, ..., a_m) is a composition of s and W = W_1 0 W_2 0 ... is a list of words, each `1 x0 1 x1 ...` a binary
number N_i (least significant bit first) and consecutive words separated by a single 0. Read the cuts between the
parts as an (s-1)-digit binary number v ((s) is v = 0, (1, ..., 1) is v = 2^(s-1)-1). A *tick* turns
(.., a+2, 1^t) into (.., a+1, t+1), which is v -> v+1 with carry t, and adds 1 to N_1, in exactly 20 + 18t + 4c steps
(c the carry of N_1 + 1). After (1, ..., 1) the round ends and the tape is

    X(k, W) =  C>0 1 0 1^(5k+3) 0 W

with k = s-1 and N_1 one larger; the next round starts at Z(k+2, 0, W) after 5k+22 steps. So a round from
X(k, N, b) adds 2^(k+1) to N in exactly `84*2^k - 5 + 4(s2(N) - s2(N + 2^(k+1)))` steps (s2 = binary digit sum).

**Overflows.** A tick with N_1 = 2^b - 1:

* v even (*small restructure*): N_1 becomes 2^(b+2) + 24 on b+3 bits, joined with W_2 if there is one, and the
  counter drops its lowest digit: Z(s-1, v/2+1, ..) after 103 + 4b + 18 tau(v/2) steps, or X(s-2, ..) after
  99 + 4b + 13(s-2) steps when v/2+1 = 2^(s-2). (tau = trailing ones.) In X terms this is the old formula
  `X(k, N, b) -> X(k, 2^(b+2) + 24 + (M-1)/2, b+3)`.
* v odd, or at the end of a round (*big restructure*): the tape is rebuilt; not decoded. The result depends only on v
  (checked for s <= 6 at three widths b: the ones at the top of N only lengthen the new word, and the step count
  grows by 4 per extra bit), may hold several words, and passes
  through configurations `C>0 1 0 1^(5j+1) 0 W` with gaps of 5a+1 cells (a different counter).

**The run.** From X(6, 215, 8) at step 5,452: small restructures at 7,140, 49,183, 392,336; big at 3,143,847
(s = 17), giving X(0, 9223585492820455065, 64) at 3,145,810. Then (accelerated run, below) small restructures at
10^20.59, 10^21.54, 10^22.45; big at 10^23.36 (s = 73, 1.05e6 direct steps), giving two words of 120 and 137 bits;
small at 10^34.17 joining them (260 bits); small at 10^79.59, 10^80.54, 10^81.45, 10^82.36; big at
10^83.26 = step 182,119,650,625,878,709,221,319,201,792,865,606,639,418,572,043,303,327,520,181,863,006,769,660,686,314,911,784
(s = 272). That one builds a second counter inside the tape, right of a `0^21` gap, which runs as if the gap were
the end of the tape; it had not returned to the left end after 2*10^10 direct steps.

A halt needs E to reach the blank right end (Lean); ticks, round ends and small restructures are proved step for
step, so a halt could only come out of a big restructure.

## What is established

**Proved in Lean, kernel only** (`lean/Blank.lean`): the halting configurations (`step_none_iff`); no halt in 10,000
steps (`blank_runs_kernel`).

**Proved in Lean, kernel only** (`lean/Edge.lean`, `lean/EdgeCert.lean`): a closed tape language from windows of three
cells covers the run from blank tape, so every halt happens in state E with blank tape from the head on: the machine
halts exactly when E reaches the blank region at the right (`halt_at_edge`, `halts_iff_edge`).

**Proved in Lean, kernel only** (`lean/Family.lean`): the run is `X(6, 215, 8)` at step 5,452 and `X(6, 1091, 11)` at
step 9,079 (`blank_X_5452`, `blank_X_9079`).

**Proved in Lean, kernel only** (`lean/Rules.lean`, written by `py/rules.py` with `bbtools.symtm`): the 13 counter
rules, each for all values of its variables and all tapes in its contexts: `round_start`; `tick_even`,
`tick_even_carry`, `tick_odd`, `tick_odd_carry` (every t and c); `round_end`, `round_end_carry`; the small
restructure `small_end`, `small_join`, `small2_end`, `small2_join`, `small_last_end`, `small_last_join`.

**Proved in Lean with `native_decide`**: no halt in 10^7 steps (`blank_runs_native`); the run is
`X(0, 9223585492820455065, 64)` at step 3,145,810 (`blank_X_epoch`).

**Computed** (trusted C/Python):
* no halt in 10^11 steps (`tools/c/tmrun.c`, 288 cells);
* the closed form of a round, result and exact step count, on 2,070 configurations with b <= 11 (`accel.py regular`);
* the jumps of `accel.py` (bulk ticks, round ends, small restructures with joins) from 3,600 random configurations
  with one to three words, against a direct simulation (`accel.py rules 1 1500`, `rules 2 2000`);
* the accelerated run from step 5,452 lists exactly the 44 X configurations, with step counts, of a direct
  10^11-step run (`accel.py events`);
* the accelerated run reaches 10^83.26 steps without a halt, through the events above (`accel.py run 1000000
  2000000000`). Each piece is a kernel rule or a direct simulation, but the glue (tick sums, the counter as binary
  number) is Python: a computation, not a proof.
* The earlier checks of `py/family.py` (regular and small rules on all small cases, a scan of 10,240 small
  configurations for 10^7 steps each without a halt).

**Open**: the big restructure in general, the nested structure at 10^83.26, and the question.

## For later

* Decode the big restructure: run `ptab`-style tables from `Z(s, v, 2^b-1, b)` (v odd) and the `5j+1` counter
  (`C>0 1 0 1^(5j+1) 0 W`), whose gaps 5a+1 act as walls; the nested run at 10^83.26 suggests a recursive description.
* Prove the composition of the Lean rules: an induction over v (the composition counter as a function of v) turning
  the tick rules into the round rule, and the bounded arithmetic of `accel.py` into Lean.
* Follow the s = 272 big restructure with an accelerated simulator for the nested counter (the jumps of `accel.py`
  apply to it if the wall behaves like the left end; check that first).

## Layout

| path | what it is |
|---|---|
| `lean/Machine.lean`, `lean/Blank.lean` | the machine and bounded runs (generated) |
| `lean/EdgeCert.lean`, `lean/Edge.lean` | the closed tape language (from `bbtools.ctl`, K = 3) and the right-edge theorem |
| `lean/Family.lean` | `X(k, N, b)` and three configurations of the run (kernel, `native_decide`) |
| `lean/Rules.lean` | the 13 counter rules (kernel), generated by `py/rules.py` |
| `c/tmfrom.c` | a direct simulator started from a given run-length tape, printing the tape at end-of-tape events |
| `py/family.py` | the X family, its rules, and the checks of round 1 |
| `py/accel.py` | the counter model, the accelerated simulator and its checks |
| `py/rules.py` | writes `lean/Rules.lean` |

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LC_1LA1RB_1LD0LA_1RE1RD_---1RF_1LB0RF/lean/check.sh
gcc -O2 -o /tmp/tmfrom holdouts/1RB1LC_1LA1RB_1LD0LA_1RE1RD_---1RF_1LB0RF/c/tmfrom.c && export TMFROM=/tmp/tmfrom
cd holdouts/1RB1LC_1LA1RB_1LD0LA_1RE1RD_---1RF_1LB0RF/py
python3 rules.py | diff - ../lean/Rules.lean
python3 accel.py regular; python3 accel.py rules 1 1500; python3 accel.py run 1000000 2000000000
/tmp/tmfrom 1RB1LC_1LA1RB_1LD0LA_1RE1RD_---1RF_1LB0RF A>0 100000000000 C L 100000000 > cl.txt && python3 accel.py events cl.txt
```

## Pages

- [`pages/holdouts/1RB1LC_1LA1RB_1LD0LA_1RE1RD_---1RF_1LB0RF/explainer.html`](../../pages/holdouts/1RB1LC_1LA1RB_1LD0LA_1RE1RD_---1RF_1LB0RF/explainer.html)
- [`pages/holdouts/1RB1LC_1LA1RB_1LD0LA_1RE1RD_---1RF_1LB0RF/proof-status.html`](../../pages/holdouts/1RB1LC_1LA1RB_1LD0LA_1RE1RD_---1RF_1LB0RF/proof-status.html)

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB1LA_1LA1RC_1RD0RB_1LE1LD_---1LF_1RA0LF`](../1RB1LA_1LA1RC_1RD0RB_1LE1LD_---1LF_1RA0LF/README.md): rename A→B, B→A, C→C, D→D, E→E, F→F and exchange left and right; it is this table started in state B, in a mirror

<!-- end of related machines -->
