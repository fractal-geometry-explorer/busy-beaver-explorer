# Level-by-level invariants for the draining ternary odometer: what the experiment shows (26 November 2026)

Section H of `holdouts/recent-proofs/technique-survey-nov26.md`. Machines:
1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD and 1RB---_0RC0LA_1LD0RB_1LE0LF_1RC1LF_0LC0LB. The second is the mirror
image of the first started in another state, so both obey the same local rules; everything below was run on the
mirrored table of the first (`1LB0RD_1LC0LF_1RA1LF_0RA0LE_1RD---_0LA0LD`, sample state D), as `py/cdigits.py` does.

Status: exploratory. Nothing here is a proof. Scripts are in `holdouts/1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD/py/` (`walls.py`, `gen2.py`,
`topwalls.py`) and `holdouts/1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD/c/synth.c`; outputs in `holdouts/1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD/data/`.

## 1. The grammar

At a sample the tape is `TOP digit* (1000)^L 100 head`. A digit is a run of r blocks `1000` and then a wall.

* Counter walls: Z = `101010`, O = `10`, T = `100000`.
* Every other wall of the earlier notes (`b1_2`, `b2_1`, `b1_4`, `b2_3`, `b1_7`, `b3_3`, `b2_5`) is a single block
  `1^a 0^b`, and each one comes from a fusion. When the carry stops on an O whose run is empty, the O cannot give
  up a block, so its 1 is erased and it fuses with the wall above it:
  T+O gives `b1_7`, `b1_2`+O gives `b1_4`, `b2_1`+O gives `b2_3`, `b2_3`+O gives `b2_5`, O+O gives one more run
  block (the two digits disappear, which is the merge 1,931 + 0 + 10,064 = 11,995 seen at 6x10^65), Z+O gives O O.
* The far-end "gadget" is the top wall together with a first digit of run 0. Its cycle of nine is
  `b1_2`, `b2_1 [0]T`, `b1_2 [0]Z`, `b1_2 [0]O`, `b1_4`, `b2_1 [0]Z`, `b2_1 [0]O`, `b2_3`, `b2_1`, and each step is
  one carry out of the first real digit. `b1_4` is the step that turns the last run into a new bottom digit.
* A gadget in the middle is a digit that never passes a carry upward. It cycles
  `[a]b2_3`, `[a-1]O [0]b2_1`, `[a-1]O [0]b1_2`, `[a-1]b2_3`, losing one block per three carries and taking two
  blocks per cycle from the digit below it. Everything above it is frozen until a reaches 0. It is born from
  `[a]T [0]O`. This is the nesting: the tape is a stack of counters, and only the lowest one runs.

`data/wall_table.txt` gives, for every block `1^a 0^b` with a <= 4 and b <= 9, what one carry does to it at the tape end
and after a run (symbolic runs of the machine, `py/walls.py`). The 270 window rules met in the
first 300,000 sweeps (10^11 steps) of the real run all fit the description above. The carry chain is
transparent: the local outcomes are the same with and without a chain of T digits.

## 2. The grammar alone is not a safe closed set

Halting walls exist: a carry into `b2_4`, `b3_4`, `b4_2`, `b4_3`, `b4_4` or `b4_5` halts (`data/wall_table.txt`).
And tapes of the grammar reach them. The smallest example is `[0]b1_2 [2]O [1]O [0]`, cells
`1001000100010100010100`, which halts 5,370 steps after the sample (direct simulation, `c/synth.c`).

The route below was traced in full on four halting tapes. Of 60 random halting tapes, 55 end with its last step
(`b2_2`, then `b2_4`); the other 5 end at `b4_3`, and how they get there was not traced.

1. The top wall is `b1_2` and a middle gadget `[a]b2_3` sits directly below it.
2. The gadget drains to a = 0 while the top is frozen at `b1_2`. `b1_2 [0]b2_3` fuses to the top wall `b3_1`.
3. `b3_1` takes one carry and becomes `b2_2`. If the run of the first digit is 0 at that point, the digit goes
   Z, O and then fuses: `b2_2`+O gives `b2_4`. The next carry into `b2_4` halts, whatever the lower runs are.

If the first digit has two or more blocks when `b3_1` appears, the top goes `b3_1`, `b2_2`, `b2_3` and rejoins
the normal cycle. So halting needs the digit below the gadget to hold exactly one block at the moment the gadget
drains, with the top parked at `b1_2`. That digit loses two blocks per gadget cycle, so the condition is
arithmetic: roughly (its run) - 2a = 1 with the right phases.

Random tapes of the grammar (top state uniform over the nine, four digits, digit j with a run uniform in
0..s*2^j, 3,000 tapes per scale, 3x10^7 steps each, `py/gen2.py` and `c/synth.c`):

| scale s | halting tapes |
|---|---|
| 1 | 29 |
| 3 | 24 |
| 10 | 6 |
| 30 | 1 |

The step cap cuts off late halts at the larger scales, so read this only as: halts exist at every scale and get
rarer as runs grow.

## 3. What this means for section H

An induction on the level can prove the regular part: the closed-form jump (the 3^p - 1 increments that take p
digits from all Z to all T are a translation of the runs) for every p, on top of `sweepZ` and `sweepO` in
`lean/Chain.lean`. That is a clean Lean target and would put the accelerator's first ingredient in the kernel.

It cannot prove non-halting by itself. Any closed set has to exclude step 3 above, and that depends on the exact
values of two runs at a collapse, not on the shape of the tape. In the real runs the top digits hold thousands of
blocks and collapses are separated by enormous times, so a hit is unlikely each time, but that is a probabilistic
argument of the kind made for cryptids, not an invariant. I have not found a structural reason why the real orbit
could never meet the condition.

## 4. The top walls of the real runs (26 November 2026)

`py/topwalls.py` runs the exact accelerator `py/oacc.py` from the first sample after step 10^6 and looks at the
far end after every macro step (25 minutes per machine; outputs `data/c2_topwalls.json`, `data/c1_topwalls.json`).

| machine | reached | top walls seen | `b3_1`, `b2_2` or a halting wall anywhere | `b1_2` with `b2_3` directly below |
|---|---|---|---|---|
| 1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD | 5.16x10^86 steps | `b1_2`, `b2_1`, `b1_4`, `b2_3` | never | never |
| 1RB---_0RC0LA_1LD0RB_1LE0LF_1RC1LF_0LC0LB | 1.92x10^85 steps | `b1_2`, `b2_1`, `b1_4`, `b2_3`, and `b2_5` four times near 1.2x10^7 | never | never |

So neither run has entered the first step of the halting route. A gadget stood directly below the top wall only
early on: between 1.1x10^6 and 3.2x10^6 steps in the first machine (under `b1_4`, `b1_2` and `b2_1`, in the
safe phases) and near 8x10^6 steps in the second. After that the wall below the top is always a counter digit.
The other odd walls (`b1_7`, `b3_3`, `b2_5`) occur only lower down. Steps before 10^6 are not in this log; the
window rules of the direct run from 2x10^5 steps show no such wall either.

This is an observation up to these step counts, not an invariant.

## 5. Suggested next steps

1. Derive the halting condition in closed form (which top state, which digit states, which run values) and state
   it as a Lean lemma in both directions. This turns "does it halt" into a question about the run arithmetic at
   collapses.
2. Prove the closed-form jump for all p by induction on the level.
3. Look for structure in the bottom of the tape: the small constant runs 63, 65, 67, 71 next to `b2_3` recur
   across many decades of `data/c2_oacc_decades.txt`, which suggests the generator of new digits is regular even
   if the top collapses are not.
