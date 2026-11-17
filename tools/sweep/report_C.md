# Group C transcription report (condensed from the transcribing agent)

All nine modules transcribed from the Lean files, matched against the machines' scripts and direct runs, and run
under engine.py (str/None components checkpoint and resume).

| machine | map (Lean) | KIND | bound before this sweep | notes |
|---|---|---|---|---|
| 1RB0LD_1RC1RA_1LD0RB_1LE1LA_1RF0RC_---1RE | Macro.lean mstep: J=j+3 floor(K/2); K even: a>=1 -> (a-1,J+1,0), a=0 halt; K odd: a>=1 -> (a-1,J+3,1), a=0 -> (2J+7,0,1). From (3,0,1) | parity-3/2 (countdown epochs) | 3 epochs, walls 3, 25, 227097 (~1e79981 steps); epoch-4 wall has 39,991 digits | halting = parity of a fixed sequence sampled at tower-growing walls |
| 1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_---0LA | Reset.lean next: c>=2 -> (floor(3x/2)+7, c-2); reset table at c<=1. From (4,4,False) | reset-table | 585 terms (native_decide); phase 3 needs ~1e101 iterates | halts on one residue class in four at a reset |
| 1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RB1RF_---1RD | Model.lean nxt (22 rows), X/Y/Z, from X(2,0,2) | frame | 9,500 rounds (11,902 bits) | halting needs c-b = 2 at a Y run start |
| 1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_---1LC | Doubling.lean op: 2u<v -> (c,2u,v+1); 2u>v,c>=1 -> (c-1,2u-v,v+1); 2u=v,c>=1 -> (c-1,1,v+2); 2u>v,c=0 -> (2(v-u-1),2u-v,2u-v+3); 2u=v,c=0 halt. From (0,2,5) | doubling-mod | 1e11 ops, 54 resets (c/odo.c) | numbers ~36 bits; same kind as 1RB1LF_1RC1RF_... |
| 1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE | Round.lean next, from (3,1,False) | subtractive-3x | 2e7 rounds | **main branches identical to 1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD**; differ only at rows i=j+1, i+2=j |
| 1RB1RF_1LC---_1LE1RD_1RA0RC_0LF0LA_0LD0RB | Map.lean emap, from D(3,0) | doubling-pay | 40,000 epochs (47,748 bits) | halts n odd, k=1 |
| 1RB1LF_1RC1RF_0LD1RE_---1LC_0RB1RE_1LA0LE | Map.lean F/inner (26 rows), from vis(None,2,0) | doubling-mod | 1e11 ops, 35 odd pools (c/fast.c) | even pool = doubling map of 1RB1RA_0LC0RE_... |
| 1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA | Map.lean F/overflow, from s(7) | doubling-pay | 1e8 returns (c/orbit.c) | busycoq PR 60 claims a halt ~1e25 returns out; module reproduces PR 60's 86-node endgame from p(8, 56*2^85-286) to p(1083197534374707740536733690, 0) |
| 1RB0LF_1LC0LD_1RD1LB_---1RE_0RA1RE_1LA0LE | Macro.lean mstep + Reduce.lean halts_iff, from (10,0,none,None,0,0) | doubling-pay | 2e7 macro steps (1.92e14 machine steps, native_decide) | outer N halts iff N = 2^(n+4)-2n-10 (if proved; converse computed N<=3000); busycoq PR 67 says never halts |
