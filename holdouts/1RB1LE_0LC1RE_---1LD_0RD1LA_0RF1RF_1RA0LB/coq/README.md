# Coq (busycoq) proof that the machine halts

A second proof that this machine halts, in Coq on busycoq's own definitions (`TM`, `halts`, `c0`), in one
self-contained file in the style of busycoq's BB6 branch:

```coq
Theorem halt : halts tm c0.        (* M_1RB1LE_0LC1RE_HHH1LD_0RD1LA_0RF1RF_1RA0LB.v *)
```

`Print Assumptions halt` prints `Closed under the global context`. The only computation is one evaluation of
the accelerated run, checked by Coq's kernel (`native_cast_no_check`, which falls back to the VM when the native
compiler is not installed). The Lean proof in `../lean` uses `native_decide` for its runs; this proof does not
need that.

## What is in the file

- **Calls, hits and levels** (`Call`, `HitH`, `HitV`, `W p j Y`): the same vocabulary as `../lean/Odo.lean`,
  without step counts.
- **The level rules** (`hit0` … `hit15`, `halt2_HC` … `halt15_HC`, `frontH`, `frontV`, …): one hit on a level
  at each of the 16 positions, for every block count and every rest of the tape. Each is proved by busycoq's
  symbolic execution (shift rules over the blocks), with the calls on the rest as hypotheses that the tactic
  applies when the head reaches them; the tapes in between are found by the tactic, not written in the file.
  `gen_hits.py` writes these 25 lemmas.
- **The ladder** (`stack_run`): any number of hits on any list of levels, with block counts and hit numbers in
  binary; whole turns of 16 hits by arithmetic (`advF`, `passF`, bit shifts).
- **The accelerated run** (`loop`, `loop_ok`): a function on (front, levels, tail cells) whose every step is
  checked: it simulates only the tail cells, cell by cell, and moves the levels by arithmetic. `loop_ok`: if it
  returns `true` from a configuration reached from blank tape, the machine halts.
- **`halt`**: `loop 10000 true s0 = true`, from the blank tape.

## Speed-ups compared with the Lean proof

1. **No direct run first.** The Lean proof runs the machine for 27,172,911 steps (to just after the last reset)
   before the accelerated run starts. Here the run starts on the blank tape: when the tail's calls do not come
   back as the levels expect and there is no level left to write out, the function makes a plain visit on the
   cells. Only 28 visits (24,594 steps) are plain, and the resets of visits 3, 11, 25 and 3,006 pass through the
   same code.
2. **Bit shifts** for the turns of 16 hits (`N.shiftr`, `N.land`) instead of division: 3 times faster.
3. **Many hits on the tail at once.** The cost of the run is the pass over all levels (up to 887 numbers of up
   to 2,500 bits) for each hit that reaches the tail. The function first finds, on the tail cells alone, how many
   hits in a row come back as the levels expect (at most 64, `batchCap`), and then moves the levels once for all
   of them. The run takes 30 s in Coq's VM instead of 5.7 minutes (16: 78 s, 40: 41 s, 100: 34 s, 256: 51 s).

## Build

```
git clone -b BB6 https://github.com/ccz181078/busycoq
sh build.sh busycoq        # about 2 minutes; build.log is the output of one clean build (Coq 8.18.0)
```

Too little fuel (`loop 300`) makes `halt` fail, so the evaluation is not vacuous.

## The number of steps

The Coq theorem says that the machine halts, not when. The step is known exactly from the Lean proof
(`halt_step`, with `native_decide`) and from two independent programs (`../py/accel.py`, `../verify/`):
1,273,570,026,215,…,474,403,686, a number with 759 digits, about 1.2736 × 10^758. The halt comes after
6.457 × 10^378 visits of the right end; the tape grows by about two cells per visit, so the step is about
3.05 × (visits)². The number of visits is about 9.3 × (8/3)^887, since the ladder has 887 levels and each
level gets 3/8 of the hits of the one above.
