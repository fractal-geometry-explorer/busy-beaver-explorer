# Sweep results (17 November 2026)

**No map reached its halting case.** About 10 hours on 4 cores, in 2-hour sessions resumed from checkpoints.

- **25 maps were run past their earlier bound, in a range where a halt was possible:** the three Antihydra-type
  walks, the four two-big-number maps, the five phase machines, the three frame maps with `accel`, the five
  machines of the Doucette family, 1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_---0RE,
  1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA, 1RB---_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD,
  1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RB1RF_---1RD (17,958-bit numbers, up from 11,902) and
  1RB0LF_1LC0LD_1RD1LB_---1RE_0RA1RE_1LA0LE.
- **1 map stayed behind its earlier run:** 1RB1RF_1LC---_1LE1RD_1RA0RC_0LF0LA_0LD0RB reached 15,414-bit numbers in
  Python; its C program c/emap.c had already reached 47,748 bits.
- **5 maps were run but cannot halt in the range run,** because a counter or budget is far from empty:
  1RB0LC_0LC0RF_1RD1LC_0RA1LE_---0LD_1LF1LA and 1RB0LC_1LC0RD_1LF1LA_1LB1RE_1RB1LE_---0LE (inside a budget of
  2^1478 and 2^399946 phases), 1RB0RD_0RC1RE_1RD0LA_1LE1LC_1RF0LD_---0RA (Lean already rules out a halt in
  10^2899 steps), 1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_---0LA (phase 3 needs about 10^101 iterates) and
  1RB0LD_1RC1RA_1LD0RB_1LE1LA_1RF0RC_---1RE (the epoch-4 wall has 39,991 digits). Their runs only confirm the maps.
- **5 maps were not extended** (marked in the table), for the reason given there.

How each was run:
- `residue.py` (divide and conquer, exact, every block checked to divide exactly): Antihydra
  1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA, 1RB1RC_1LC1LE_1RA1RD_0RF0RE_1LA0LB_---1RA and
  1RB1LD_1RC1RE_0LA1LB_0LD1LC_1RF0RA_---0RC, each to 4.3·10^9 map steps (about 2.5·10^9-bit numbers), up from
  10^5 to 10^6. Their counters were then about 2.2·10^9, 2.2·10^9 and 1.4·10^9, so a halt is not in sight.
- C programs resumed from the 16 Nov halt-hunt checkpoints: the four e/q phase machines and
  1RB1RF_1LC1LF_0RE1LD_0LB1LD_---1RC_1RA0RD (tools/c/doubling_phases.c, psq.c), and the four two-big-number maps
  (tools/c/redmaps.c).
- `engine.py` for the rest, in rounds of 900, 1800, 3600, … seconds per map.

Units differ by map: "steps" are steps of the Lean map; "Lean steps" for the modules with `accel` count every
step of the Lean `next` inside a batched phase, so they are astronomically large and are not comparable with
the earlier bounds, which counted phases or rounds; the number size (bits) is the comparable figure there.
"closest" is the largest value of (bits of the numbers) − (bits of the distance to the halting value) seen after
step 1000: a closest of c means the halting test missed by about 2^−c of the numbers' size. Values of 17 to 27
over millions of steps are what chance predicts; nothing came unusually close.

## Table
| machine | kind | before this sweep | now (no halt) | run by | note |
|---|---|---|---|---|---|
| 1RB0LC_0LC0RF_1RD1LC_0RA1LE_---0LD_1LF1LA | parity-3/2 | 4 budget refills survived (cycles 3, 8, 25, 2,549; status.json, py/map.py orbit); the fifth budget is a 1,479-bit c, about 2^1478 rounds, so no run can finish it; machine check 4e8 steps (py/map.py check) | 4.51·10^907817 Lean steps, 3,015,705 bits | engine.py |  |
| 1RB0LC_1LC0RD_1LF1LA_1LB1RE_1RB1LE_---0LE | parity-3/2 | 4 budget ends survived (phases 4, 34, 683,741, 683,742; status.json, py/map.py orbit); the budget is now a 399,947-bit c, about 2^399,946 phases, so no run can finish it; machine check 4e8 steps (py/map.py check) | 1.45·10^918465 Lean steps, 3,051,076 bits | engine.py |  |
| 1RB0LD_1RC1RA_1LD0RB_1LE1LA_1RF0RC_---1RE | parity-3/2 | 3 epochs (walls 3, 25, 227097; 227,128 phases, ~1e79981 steps), epoch 3 odd by native_decide (lean/Epoch3.lean epoch3_odd, halts_late); epoch 4 wall has 39,991 digits | 7,424,256 steps, 4,210,052 bits | engine.py |  |
| 1RB0LF_1LC0LD_1RD1LB_---1RE_0RA1RE_1LA0LE | doubling-pay | 20,000,000 macro steps = 1.92e14 machine steps (macro_runs, native_decide, lean/MacroRun.lean); outer orbit N = 10, 27, ..., 17220, 8534636888060 (~6.5e25 steps) by py/outer.py with a heuristic (unproved) inner-epoch jump | 5.06·10^7139 Lean steps, 23,718 bits | engine.py | closest 6 bits |
| 1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA | reset-table | 10,000 resets (Lean native_decide, lean/Orbit.lean orbit_10000; t ~3,900 bits); 300 resets kernel (orbit_300) | 2,721,024 steps, 1,058,342 bits | engine.py | closest 25 bits |
| 1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA | doubling-pay | 1e8 returns to S (4.6e9 nodes, X up to 1.52e10), c/orbit.c (status.json); 1e7 nodes by native_decide (orbit_native). busycoq PR 60 claims a halt at a = 28*2^85 - 6 after ~1e25 returns (not compiled here) | not extended | busycoq PR 60's halt is about 10^25 returns away; the module reproduces PR 60's 86-node endgame |  |
| 1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_---1LB | power-of-3 | 30,000 samples, numbers 1,874 digits, > 10^3747 machine steps (Lean kernel, lean/Bound.lean; status.json) | 3,499,008 steps, 734,450 bits | engine.py | closest 22 bits |
| 1RB0RB_1LC1RE_1LF0LD_1RA1LD_1RC1RB_---1LC | power-of-2 | 30,000 samples, numbers 1,835 digits, > 10^3669 machine steps (Lean kernel, lean/Bound.lean; status.json) | 7,913,600 steps, 1,588,844 bits | engine.py | closest 27 bits |
| 1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD | frame | 1e11 frames, no halt (this module's exact accel, tools/sweep group D run, 2026-11-17); before: 1e8 frames (Lean no_halt_phases, native_decide, ~4.5e11 steps), 1e15 steps (c/mrun.c macro sim) | 6.31·10^13 Lean steps, 25 bits | engine.py |  |
| 1RB0RD_0RC1RE_1RD0LA_1LE1LC_1RF0LD_---0RA | reset-table | 6,819 phases evaluated (Lean native, lean/Orbit.lean check_6819: second reset, stack m > 10^2900); hence the next 10^2899 phases provably exist and no halt in 10^2899 steps (runs_long) | 4,081,408 steps, 5,765,701 bits | engine.py |  |
| 1RB0RE_1LC1LD_0RA0LD_1LB0LA_1RF1RA_---1LB | reset-table | 3 rounds (fuel 5, 14, 185) then the start of round 4, (0, 22205951667644132025548), after 138 applications of next (status.json, py/orbit.py); round 4 cannot halt before its fuel is spent (~1e22 applications) | not extended | round 4 has fuel 2.2·10^22; nothing can be decided before it runs out |  |
| 1RB0RF_1RC1RF_1LD0LE_---1LC_1RA1LE_1LC1RB | power-of-2 | 200,000 passes, n then 80,223 bits (status.json, py/study.py); 10,000 passes native in Lean (orbit_10000) | 4,083,456 steps, 1,639,329 bits | engine.py | closest 27 bits |
| 1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE | power-of-2 | 200,000 samples, p then 40,089 bits (status.json; Lean native time 200000 >= 2^80181, lean/LowerBound.lean; kernel 5,000 samples) | 6,967,680 steps, 1,397,902 bits | engine.py | closest 22 bits |
| 1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_---0LD | power-of-2 | 3e6 Doucette terms (c/doucette.c, trusted C); 300,000 terms Lean native_decide (Fit_native); community 1e8 terms | 6,487,360 steps, 3,055,687 bits | engine.py | closest 24 bits |
| 1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_---0LA | reset-table | 585 map terms (orbit_585, native_decide): phases 0-2 without halt; term 585 is S_3(6, c) with c ~ 2.3e101, so phase 3 needs ~1e101 iterates (NOTES.md: out of reach) | 9,864,576 steps, 5,770,070 bits | engine.py |  |
| 1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC | frame | 1e11 frames, no halt (this module's exact accel, tools/sweep group D run, 2026-11-17); before: 1e8 frames (Lean no_halt_phases, native_decide, ~5.95e11 steps), 1e15 steps (c/mrun.c macro sim) | 2.26·10^14 Lean steps, 26 bits | engine.py |  |
| 1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_---0RE | power-of-2 | 1e6 rounds, N then 666,845 bits (status.json, py/orbit.py) | 1,756,864 steps, 1,171,429 bits | engine.py | closest 20 bits |
| 1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RB1RF_---1RD | frame | 9,500 rounds (2.8e8 bulk steps, N 11,902 bits, ~1e7170 machine steps), c/xyz.c (halt-hunt/maps NOTES.md) | 5.13·10^5405 Lean steps, 17,958 bits | engine.py | closest 17 bits |
| 1RB1LD_1RC1RE_0LA1LB_0LD1LC_1RF0RA_---0RC | parity-3/2 | 1e6 rounds (status.json, Python py/orbit.py; k = 331,763 at the end) | 4.31·10^9 steps | residue.py |  |
| 1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_---0RE | frame | 1e11 phases, ~4.1e30 steps (holdouts/<m>/c/mrun.c; halt-hunt/maps logs/ph2.log) | 9.80·10^11 phases | tools/c/doubling_phases.c 2 |  |
| 1RB1LF_1RC1RF_0LD1RE_---1LC_0RB1RE_1LA0LE | doubling-mod | 1e11 inner operations (5.0e10 right-end visits, ~1e31 machine steps, 35 odd pools, 18 without bracket), c/fast.c (status.json); 1e4 nodes by native_decide (orbit_native) | not extended | c/fast.c already at 10^11 operations; not extended here |  |
| 1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_---1LC | doubling-mod | 1e11 operations (5.0e10 visits, 54 resets, v ~ 3.5e10), c/odo.c (status.json); 1e7 by native_decide (op_native) | not extended | c/odo.c already at 10^11 operations; not extended here |  |
| 1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA | parity-3/2 | 1e6 walk steps (status.json, Python py/walk.py run; p = 498,505 at the end) | 4.31·10^9 steps | residue.py |  |
| 1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE | subtractive-3x | 2e7 rounds (~6.1e6 bits), tools/c/redmaps.c rb (halt-hunt/maps NOTES.md) | 4.00·10^7 rounds | tools/c/redmaps.c rb |  |
| 1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD | subtractive-3x | 2e7 rounds (halt-hunt/maps, redmaps rc) | 4.00·10^7 rounds | tools/c/redmaps.c rc |  |
| 1RB1RC_1LC1LE_1RA1RD_0RF0RE_1LA0LB_---1RA | parity-3/2 | 1e5 rounds (status.json, Python py/orbit.py; counter m = 50,008 at the end); 10,000 rounds Lean kernel (first_rounds) | 4.31·10^9 steps | residue.py |  |
| 1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_---0RE | frame | 1e11 phases, ~4.1e30 steps (holdouts/<m>/c/mrun.c; halt-hunt/maps logs/ph1.log) | 1.00·10^12 phases | tools/c/doubling_phases.c 1 |  |
| 1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE | frame | 1e11 phases, ~4.1e30 steps (holdouts/<m>/c/mrun.c; halt-hunt/maps logs/ph3.log) | 8.80·10^11 phases | tools/c/doubling_phases.c 3 |  |
| 1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_---0RE | frame | 1e11 phases, ~4.1e30 steps (holdouts/<m>/c/mrun.c; halt-hunt/maps logs/ph4.log) | 4.00·10^11 phases | tools/c/doubling_phases.c 4 |  |
| 1RB1RE_1LC0RA_0RD1LB_---1RC_1LF1RE_0LB0LE | subtractive-3x | 3e7 map steps, 6.5e6 bits (tools/c/redmaps.c re0, halt-hunt/maps/NOTES.md, 16 Nov 2026) | 5.00·10^7 map steps | tools/c/redmaps.c re0 |  |
| 1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_---0LE | power-of-2 | 8e6 map steps, n then 5,332,435 bits (status.json; halt-hunt/maps/NOTES.md, redmaps re1, checkpoints/map_re1.ck) | 1.50·10^7 map steps | tools/c/redmaps.c re1 |  |
| 1RB1RE_1LC1LD_---1LA_1LB1LE_0RF0RA_1LD1RF | parity-3/2 | Lean (kernel): epochs 0-3 have c = 3, 20, 297, 459271258863231 and epoch 3 ends in a new epoch (epochs_first, epochs_4), so no halt in the first 80 + 114,817,814,715,807 phases; epoch 4's phases (c4 ~ 10^(2e13)) never computed (README) | not extended | epoch 4 is about 10^14·(3/2)^… phases away; Lean already covers epochs to 459271258863231 |  |
| 1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE | frame | 1e11 frames, no halt (this module's exact accel, tools/sweep group D run, 2026-11-17); before: 1e8 frames (Lean no_halt_phases, native_decide, ~9.7e11 steps), 1e15 steps (c/mrun.c macro sim) | 2.01·10^13 Lean steps, 23 bits | engine.py |  |
| 1RB1RF_1LC1LF_0RE1LD_0LB1LD_---1RC_1RA0RD | frame | 1e11 phases, 2e10 pass starts (holdouts/<m>/c/psq.c; halt-hunt/maps logs/psq.log) | 1.00·10^12 phases | holdouts/…/c/psq.c |  |
| 1RB1RF_1LC---_1LE1RD_1RA0RC_0LF0LA_0LD0RB | doubling-pay | 40,000 epochs (1.95e9 jump steps, epoch value N 47,748 bits), c/emap.c (halt-hunt/maps NOTES.md) | 1.01·10^4640 Lean steps, 15,414 bits | engine.py | closest 14 bits |
| 1RB---_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD | subtractive-3x | 10,000 R rounds of the map (py/samplemap.py orbit, status.json: 29,225,208 C steps, 25,330 A steps, x thousands of bits); map checked against the machine for 1e10 steps (samplemap.py check) | 9.62·10^5481 Lean steps, 18,211 bits | engine.py | closest 16 bits |
