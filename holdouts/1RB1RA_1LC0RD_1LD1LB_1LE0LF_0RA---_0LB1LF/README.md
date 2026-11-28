# 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1LF

bbchallenge id 99431. Both sides grow by sweeps; the tape is an irregular list with one long periodic block inside it (the word 1^7 00 1 00 repeated, 3,766 times at 8.8·10^8 steps) that grows steadily.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RA |
| B | 1LC | 0RD |
| C | 1LD | 1LB |
| D | 1LE | 0LF |
| E | 0RA | --- |
| F | 0LB | 1LF |

## What it does

Both sides grow (left like t^0.66, right like √t). At the left end the tape is a list of runs of 1s of length
3a + 1 separated by `00`, with one long **periodic block** in it:

    step 882,788,555:  E>0 1^17 0010 1^3 0 (01)^3 1^4 00 1^5 (001)^4 1^8 (001)^3 1^6 00 1^11 …
                       … (001111111001)^3766 00 (10011)^3 1^3 (001111100111)^5 00 …

(7,550 of the 7,582 runs of 1s have length 3a + 1; 7,574 of the 7,581 runs of 0s have length 2.) The block
`(001111111001)^3766` is the pair of runs 1^7, 1^1 repeated. At the right end (step 999,852,606) the same block is
written `(011011101011)^2687 … (01)^1608`. Outside the block the list is irregular.

In plain words: a sweeping machine that rewrites a list of numbers each time, in which one long regular stretch
keeps growing while the rest churns.

## What is proved

- Lean, kernel only (`lean/Blank.lean`, generated): the halting configurations (`step_none_iff`) and no halt in the first 10,000 steps; with `native_decide`, none in the first 10<sup>7</sup>.
- Lean, kernel only (`lean/Rules.lean`, written by `py/rules.py`): the shift rules of the leftward sweep in B across `(01)^n` and `(011)^n` (`shift_l_B_01`, `shift_l_B_011`).
- C (`tools/c/triage.c`, trusted): no halt in the first 10<sup>9</sup> steps.
- C (`tools/c/tmrun.c`, trusted): no halt in the first 1,000,000,500,000 steps (10<sup>12</sup>; 22 November 2026,
  about 70 minutes; 806,171 ones at the end).
- Lean, kernel only (`lean/EngineRules.lean`, written by `py/engine_rules.py`): 11 of the macro rules of DeepMind's
  busycoq PR 93 engine as they hold for this machine, for every count, including the 5 that differ from PR 93's table
  (see [PR 93's engine on this table](#pr-93s-engine-on-this-table-22-november-2026)), and the two moves by which
  the halving-chain engine crosses a digit to the right (`pr93_rightD0`, `pr93_rightD`).
- Lean, kernel only (`lean/LearnedRules.lean`, written by `py/prove_prules.py`): the 100 most used of the halving-chain
  engine's learned rules, for every count (see [A halving-chain engine](#a-halving-chain-engine-22-november-2026)).

Everything else above is measured on runs (heuristic), not proved.

## Open

Whether it halts. The periodic block and the codes are measured; the irregular part is not understood.
Halting needs D reading 0 with a 1 to its left.

## For later

More than a day. Next: (0) the left-end counter of the halving-chain engine at 10^13 (see below) as a counter of its
own; (1) follow the periodic block over time (how many copies per left visit) and prove the
sweep across it with `symtm.prove`; (2) look at the irregular part as a list of numbers (runs 1^(3a+1)) and test
whether the sweep acts on it as a finite transducer.

## PR 93's engine on this table (22 November 2026)

**Result: the engine does not carry over.** The question stays open; no halt was found.

- **The table.** Exchange the names E and F, and replace the detour D0 `1LE`, E0 `0RA`, A1 `1RA` by the single step
  `1RA`. The detour ends in the same configuration unless the cell left of D is 1, where the machine halts. The table
  becomes G = `1RB1RA_1LC0RD_1LD1LB_1RA0LE_0LB1LE`. That is the table T3 of DeepMind's halting proof in
  [busycoq PR 93](https://github.com/ccz181078/busycoq/pull/93) (`1RB1RA_1LC0RD_1LD1LB_1RA0LE_0LB0LF_0LB---`) with
  one transition changed, E1. T3 erases the 1 and steps left twice (E1 `0LF`, F0 `0LB`). G keeps the 1 and walks left
  over 1s (E1 `1LE`). G has no halting transition. **This machine halts exactly when G's run from blank tape has D
  reading 0 with a 1 on its left.**
- **The rules.** PR 93's engine works with three configurations, `CfgR l r = l A> 0100 r`, `CfgL l r = l <B 1 r`
  and `CfgJ l r = l <C 100 r`, and the digit words `D n = 1 (11)^n 00`. Of its 18 basic rules, 14 hold here
  unchanged (direct simulation, counts up to 4, random tape around). The four that end in `CfgJ` (collision,
  collide, defect0, finishP) still end in `CfgJ`, but where T3 writes the digit `D (k+1)`, this machine writes
  `D k 10`. Lean proves 11 of the rules for every count, including all 5 changed forms (`lean/EngineRules.lean`). In
  none of the 18 rules does D read 0 next to a 1, so a halt can only come where an engine steps cell by cell.
- **Why PR 93's engine does not carry over.** For T4 (the table of 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB0LE) the
  same four rules only moved a carry from one digit to the next, so the engine's counting of calls (one call: from
  `CfgR l r` to `CfgL l s` without touching `l`) survived a patch. Here a call that collides leaves a `10 10`:
  PR 93's `call (D_j 10 D0 D0 r) (D_(j+1) D2 10 r)` becomes `D_(j+1) D1 10 10 r` (checked for j = 0 to 3). The next
  call that meets `10 10` does not return within the words it was given; it runs on into the tape beyond. In the run,
  repeated calls add `D1 D2` once per two calls. PR 93's batched calls (`doCallsD`) have no counterpart, and a new
  engine would need this machine's own call algebra.
- **What the tape looks like** (left-end visits, direct run to 3·10^10 steps). The tape is a list of digits `D n`
  with a few `10` defects. It holds halving chains, for example at step 12,537,719,512
  `D5773 D0 D0 D2884 10 D1440 10 D0 D0 D0 D720 D1 D359 D1 D179 D1 D89 …`, and growing periodic blocks:
  `(D2 D1)^15875`, `(D3 D0)^3841`, `(D0 D0 D3)^105`. The block `1^7 00 1 00` of the section above is `D3 D0 D0`.
- **Accelerated runs.** The accelerated simulator `rsim.py` (validated against direct simulation at 6 points up to
  10^10 steps) found no halt in 984,180,560,109,706,163 steps (9.8·10^17; 3 hours, 350 jumps). The recursive-rule simulator `tools/py/bbtools/rleaccel_rec.py` stalls
  near 10^8 steps (K = 2, 3, 6; 5 minutes each).
- **A faster port (22 November 2026).** `c/rsim_fast.cpp` is `rsim.py` in C++ with the same decisions, about 15 to 25
  times faster here (rules looked up by a running hash of the trailing cells, no string building in the rope
  tidying). It follows the same trajectory as `rsim.py`: with `rsim_screen.py`'s targets both pass 10^6, …, 10^13 at
  the same step counts with the same numbers of rules, learning calls, samples and jumps, and its tape matches direct
  simulation at 8 points up to 3·10^10 (`py/rsim_fast_validate.py`). It passes the Python run's 3-hour reach after
  212 seconds and found **no halt in 1,000,000,000,008,656,179 steps (10^18)** after 65 minutes; the decade after
  that had not finished 5 hours later (no jump: the sweeps are crossed one rule at a time, 7·10^9 rules by 10^18).
  The jumps are validated, not proved, so this bound rests on them. Progress comes in bursts and depends on where a
  run pauses between targets: with targets ×1.5 apart the same program stalled near 8.4·10^13 for an hour.

- **A chain-phase engine (26 November 2026).** `c/rsim_chain.cpp` is `rsim_fast.cpp` plus a macro step for the
  chain phases, where rsim's jumps never fire. At each increment visit the right tape is read as a chain of levels
  `1^(2a+1) 00` with short separators between them. One increment changes each separator and level by a rule that
  depends only on its neighbours (a radius-1 automaton, learned from exact increments). It also moves a few long
  blocks by fixed amounts and costs an affine number of steps in the counts. The cost is learned by perturbing each
  count and running the exact simulator. The engine takes a macro step only when every rule it needs is known, and
  only after the same pattern has been checked against an exact increment twice; any mismatch stops the run.
  Checks: in a run to 9.84·10^17 with every prediction re-simulated, there were no mismatches. All 2,796
  chain-phase exits (step count and a hash of the whole tape) are the same with and without macro steps, which
  stood in for 700,000 increments. It found **no halt in 3,588,977,699,892,617,375 steps (3.5·10^18)** in
  20 minutes. The macro steps rest on the learned automaton and cost model, which are checked, not proved, like
  rsim's jumps.
- **Cycles and checkpoints (28 November 2026).** Past 3.5·10^18 the chain stands still while a block near the right
  end alternates between two shapes, so the engine now takes one macro step per repeating cycle of up to 4
  increments (the learned rules are kept separately for each cycle length). Rechecked to 9.84·10^17 against the
  run without macro steps: all 528 shared exit points have the same step count and tape hash, and the final step
  count is the same. The engine also saves the tape to a checkpoint every 4 minutes and resumes from it (the
  project's `longrun` job `1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1LF-chain-engine`). **No halt in
  80,750,788,992,831,569,943 steps (8.07·10^19).** There it slows again: a halving chain of `(01)^n` blocks has
  formed on the left side (`(01)^53511490`, `(01)^26755744`, `(01)^13377871`, `(01)^6688936`, …), which the
  engine, written for chains on the right side, does not read yet.

The same table from other starts: 1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1RF (start B),
1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE1RF (start C) and 1RB0RF_0LC---_1LD1LC_1RE0LA_1RA1RD_0RD1RF (start D). The same
changed rules apply to all four.

## A halving-chain engine (22 November 2026)

**Result: no halt in 2·10^17 steps of an exact engine that never jumps, and the engine's rules are proved, not
measured.** The question stays open. The 10^18 bound still rests on the accelerated simulator above.

- **The engine.** `c/hce.cpp` runs the reduced table G. The tape is two stacks of tokens around the head: digits `D n`
  on the right, `S n = 1 (01)^(n+1)` on the left, raw bits, repeated words, and *segments* (long lists of digits, kept
  as runs of repeated patterns and crossed in one move using their sum). The head is in one of PR 93's three modes R, L,
  J or a plain state. Crossing a digit or a segment uses rules proved in Lean (`pr93_rightD0`, `pr93_rightD`,
  `pr93_left`, `pr93_leftJ`). Everything else simulates a small window of tokens cell by cell. When a count in the
  window is large, the engine applies a rule learned from five probe runs with counts `base + 6t`.
- **The learned rules are proved.** `py/prove_prules.py` states each learned rule for this machine, detours
  included, for every t and every tape around the window, and `bbtools.symtm` proves it. All 3,481 rules learned on
  the way to 10^13 steps are proved this way (1,614,984 uses). Lean's kernel checks the 100 most used
  (`lean/LearnedRules.lean`, 74% of the uses, in CI). Checking all of them takes hours: some proofs hit the kernel's
  time limit and would need a different proof shape.
- **The halt test.** A halt (D reading 0 with a 1 on its left) can only happen in a cell-by-cell window. A window
  whose leftmost cell is D reading 0 is made wider first, so the cell to its left is always known. In the run below
  this never happened.
- **Checked against direct simulation.** The tape equals a direct simulation of G at 10^5, 10^7, 10^8 and 3·10^8
  steps (`hce check`).
- **The run.** `NOBLK=1 NOCYC=1 hce export 2e17` (no jumps of any kind): 200,000,000,629,086,925 steps of G without a
  halt, in 27 minutes (10^17 after 21 minutes). The machine itself takes 2 more steps per detour, so this is also a
  bound for the machine. By then the engine has learned 3,843 rules; the 3,481 learned by 10^13 are the ones proved
  above. Event counts grow about ×3 per decade of steps: the engine is exact but does not batch whole far passes.
  Runs toward 10^18 ran out of memory (14 GB) somewhere between 2·10^17 and 5·10^17 steps, in a jump of several GB
  within a minute; the cause is not found yet. The segments' runs take 32 bytes each (16 million runs at 10^17).
- **What it shows.** Around 10^12 steps the left end of the tape is exactly periodic: every 83 far passes it eats 4
  copies of the block `D7 D0 D0 D2` and adds 166 `D0` digits further right. The engine can jump over such cycles
  (cycle detection on its event hashes; 2 jumps over 3,590 cycles near 10^12), but by 10^13 the left end has become an
  aperiodic, growing counter that eats `(D3 D0 D0)^58372` one copy per two far passes, and no further cycle repeats.
  The middle of the tape (mostly `D0`) is passed through unchanged. All activity is at the left end (runs `1^(3a+1)`
  used up 3 ones per far pass) and at the right end (two `D0` digits added per far pass, or a marker alternating `10`
  and `1010`).
- **Why it does not settle the question.** A proof needs the dynamics of the left-end counter, which is not
  understood. The engine is written for this table; `c/hce.cpp` holds G's table in three arrays at the top (TW, TM, TQ) and the halt test in `rawsim`,
  which is where a sibling table would change it.

## Reproduce

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1LF/lean/check.sh
python3 holdouts/1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1LF/py/rules.py          # rewrites lean/Rules.lean
python3 holdouts/1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1LF/py/observe.py 1e7 B 6  # the tape at the last moments each end grew
python3 holdouts/1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1LF/py/engine_rules.py   # rewrites lean/EngineRules.lean
python3 holdouts/1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA1RF_0LC---/py/rsim_screen.py 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1LF 10800
python3 holdouts/1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1LF/py/rsim_fast_validate.py 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1LF 1e6,1e8,1e10,3e10
g++ -O2 -std=c++17 -o rsim_fast holdouts/1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1LF/c/rsim_fast.cpp
DECADES=1 ./rsim_fast 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1LF run 3900 out.json   # passes 10^18
g++ -O2 -std=c++17 -o rsim_chain holdouts/1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1LF/c/rsim_chain.cpp
LOGEXITS=1 ./rsim_chain 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1LF chain 1e25 1200 2   # 3.5*10^18 in 20 min
CKPT=ck ./rsim_chain 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1LF chain 1e25 10800 2   # checkpoints in ck/, resumes from them; 7.6*10^19 in 80 min
LOGEXITS=1 ./rsim_chain 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1LF chain 1e17 3000 100000000   # no macro steps: same EXIT lines
g++ -O2 -std=c++17 -o hce holdouts/1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1LF/c/hce.cpp
NOBLK=1 ./hce check 1e5 1e7 1e8 3e8                    # tape equals direct simulation of G
NOBLK=1 NOCYC=1 ./hce export 1e13 rules13.txt          # 15 seconds; the learned rules
python3 holdouts/1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1LF/py/prove_prules.py rules13.txt LearnedRules.lean 100   # symtm proofs
NOBLK=1 NOCYC=1 ./hce export 2e17 rules.txt            # 27 minutes, no jumps
gcc -O2 -o tmrun tools/c/tmrun.c && ./tmrun 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1LF 1000000500000   # about 70 minutes
```

## Pages

- [`pages/holdouts/1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1LF/explainer.html`](../../pages/holdouts/1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1LF/explainer.html)
- [`pages/holdouts/1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1LF/proof-status.html`](../../pages/holdouts/1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1LF/proof-status.html)

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE1RF`](../1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE1RF/README.md): rename A→D, B→E, C→A, D→B, E→C, F→F and exchange left and right; it is this table started in state C, in a mirror
- [`1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1RF`](../1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1RF/README.md): rename A→E, B→A, C→B, D→C, E→D, F→F and exchange left and right; it is this table started in state B, in a mirror
- [`1RB0RF_0LC---_1LD1LC_1RE0LA_1RA1RD_0RD1RF`](../1RB0RF_0LC---_1LD1LC_1RE0LA_1RA1RD_0RD1RF/README.md): rename A→C, B→D, C→E, D→A, E→B, F→F and exchange left and right; it is this table started in state D, in a mirror

<!-- end of related machines -->
