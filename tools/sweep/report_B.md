# Group B transcription report (condensed from the transcribing agent)

All nine modules validated against the machines' own scripts and direct runs; each runs under engine.py.

| machine | map (Lean) | KIND | validated | notes |
|---|---|---|---|---|
| 1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_---0LD (Space Needle) | Macro.lean g, halts_iff; Collatz.lean F, halts_iff_pow2. g(0,c)=(c+2,1), g(1,c)=halt, g(2k+2,c)=(5k+c+7,1), g(2k+3,c)=(k,k+c+4), from (3,1) | power-of-2 | 20,000 states = Collatz.lean Fit; c/verify.c meets first 17 states | D=b+3 at c=1 visits: D=2^v(2a+1) -> D+v+3a; halts iff some D is a power of 2 (Doucette). Bound 3e6 terms (ours), 1e8 community |
| 1RB1LD_1RC1RE_0LA1LB_0LD1LC_1RF0RA_---0RC | Round.lean next: (3t,k)->(4t+4,k-1 or 0), (3t+1,k)->(4t+4,k+1), (3t+2,0) halt, (3t+2,k)->(4t+5,k+1); from (8,1) | parity-3/2 (4/3 residue walk) | 20,000 states = py/orbit.py; direct run meets 8 states | counter drift +1/3; bound 1e6 rounds |
| 1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA (Antihydra) | Macro.lean nxt | parity-3/2 | 20,000 = walk.py; walk.py check 2e6 ok | x=a+5 gives x -> floor(3x/2) |
| 1RB1RE_1LC0RA_0RD1LB_---1RC_1LF1RE_0LB0LE | Map.lean f: r>=p+2:(2p+2,r-p-1); r=p+1 halt; r=p:(2,4p+1); r<p:(p-r,4r+2); from (2,1) | subtractive-3x (doubling) | 20,000 = check_map.f; samples.c 1e9 steps 48/48 | bound 3e7 steps |
| 1RB1RC_1LC1LE_1RA1RD_0RF0RE_1LA0LB_---1RA | Macro.lean next, Reduction.lean halts_iff': r(n even,m)->r(3(n/2)+2,m+2); r(n odd,0)->z(3(n/2)+6); r(n odd,m>=1)->r(3(n/2)+5,m-1); z(k odd)->r(3(k/2)+2,1); z(k even) halt; from z(1) | parity-3/2 (Hydra-type) | 20,000 = py/orbit.py; --check 3e6 15/15 | y=n+4: even y -> 3y/2, m+2; odd -> (3y+3)/2, m-1 |
| 1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA | Reset.lean F (with chainF fuel), halts_iff_44; from z(44) | reset-table | = lean_map.F on v<3000 and 10,000 orbit states; accel = step | halts at z(t) with t+2s+11=2^(s+3) or rs(d) with d+s+4=2^(s+2); bound 10,000 resets |
| 1RB---_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD | MapThm.lean mstep, halts_iff; from (7,1,false) | subtractive-3x (doubling chain) | = samplemap.step on x,m<200; samplemap check 1e9 0 mismatches | accel runs whole B phase (n counts Lean steps, huge) |
| 1RB0LC_0LC0RF_1RD1LC_0RA1LE_---0LD_1LF1LA | Map.lean next, halts_iff; from (1,1,4) | parity-3/2 with budget | = map.nxt; direct 4e8 steps 27,727 moments agree | budgets 9, 31, 4966, then a 1,479-bit budget |
| 1RB0LC_1LC0RD_1LF1LA_1LB1RE_1RB1LE_---0LE | Map.lean next, land, halts_iff; from (15,7,7,1) | parity-3/2 with budget | grid 36,000 states = map.nxt; direct 1e8 steps 8,454 moments agree | budget now 399,947 bits |

Groupings: doubling chain landing on an exact value (1RB1RE_1LC0RA_0RD1LB..., 1RB0LF_1LC1RA..., 1RB---_1RC1LE...);
Antihydra-type parity/residue walks with a counter (Antihydra, 1RB1RC_1LC1LE..., 1RB1LD_1RC1RE...);
huge budget counters (the two 1RB0LC_ machines); power-of-2 test (Space Needle).
For the three accel maps that count Lean steps in bulk, use --seconds, not --steps.
