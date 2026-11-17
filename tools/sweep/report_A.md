# Group A transcription report (condensed from the transcribing agent)

All nine modules match the machines' own orbit scripts and direct runs from blank tape, and run under engine.py.

| machine | map (Lean) | KIND | bound before this sweep | notes |
|---|---|---|---|---|
| 1RB0RF_1RC1RF_1LD0LE_---1LC_1RA1LE_1LC1RB | Macro.lean f = g(n-1,2): g(0,c)=c+2 (c even) or (3c+9)/2; g(2i+2,c)=c+3i+5; g(1,c)=halt; g(2i+3,c)=g(i,c+i+4). Closed form: n+2=2^j m, f=2^j m+(m+2j-1)/2. From n=4 | power-of-2 | 200,000 passes (80,223 bits) | halts iff n+2 a power of 2 >= 4; odd branch (3n+5)/2 like Antihydra |
| 1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_---0RE | Orbit.lean phase/next: N -> phase(1,N); phase(K,m)= none (m=0), phase(2K+4,m-2K-6) (m>=2K+6), else 2K+3m+2. From N=22 | power-of-2 | 1e6 rounds (666,845 bits) | **same map as 1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_---0LE under N = 2n+2** (checked n < 200,000); this machine is that map's orbit from n = 10 |
| 1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_---0LE | Phase1.lean ph; closed form c_i=10*2^i-i-7, c_i<n<=c_{i+1}: n -> 3n-2c_i+i+3, n=c_{i+1} halts. From n=1 | power-of-2 | 8e6 steps (5.3e6 bits) | accel = closed form (checked, not Lean-proved) |
| 1RB1RE_1LC1LD_---1LA_1LB1LE_0RF0RA_1LD1RF | Phase.lean ph/endv/epochs; state (c,u,x), one phase per step | parity-3/2 (Hydra-like, epochs) | Lean kernel: epochs c = 3, 20, 297, 459271258863231 (1.1e14 phases) | decision only at epoch ends; epoch lengths grow doubly exponentially; out of reach of stepping |
| 1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_---1LB | Map.lean f, from (3,1), halts p=2 with 3 / r | power-of-3 | 30,000 samples, > 10^3747 steps (Lean kernel) | hole-map family; division chain hits 2 iff p+1 = 3^k |
| 1RB0RB_1LC1RE_1LF0LD_1RA1LD_1RC1RB_---1LC | Map.lean f, from (2,2), halts p=1 | power-of-2 | 30,000 samples, > 10^3669 steps (Lean kernel) | hole-map family (base 2); odd branch identical to 1RB1LA_0LC0RC_... |
| 1RB0RD_0RC1RE_1RD0LA_1LE1LC_1RF0LD_---0RA | Map.lean next, from (14,5), halts m=1, n = 1 mod 3 | reset-table | 6,819 phases, > 10^2899 steps (Lean native) | counter drains by 1 or 2 by n mod 3 while n grows x8/3; each reset ~1/5 halting |
| 1RB0RE_1LC1LD_0RA0LD_1LB0LA_1RF1RA_---1LB | Macro.lean next, from (0,5), halts k odd, z=0 | reset-table (Hydra-like fuel) | 3 rounds; round 4 has fuel 2.2e22 | u -> 3 ceil(u/2), fuel -1/-2 by parity |
| 1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE | Reduction.lean F, from (0,2), halts p=1 | power-of-2 | 200,000 samples (40,089 bits) | hole-map family |
