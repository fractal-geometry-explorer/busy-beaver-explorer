# F08 zone orbits (from the F08 thread, 17 Nov; not run by this engine)

State at zone step 3*10^7; window = sweeps covered exactly; nothing leaves the word = no halt and no reset.

| machine | C window | Lean native | passes into old zone |
|---|---|---|---|
| 1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA | 3*2^77 sweeps (~4e47 steps), quiet | 3*2^63 sweeps, no halt in 1.5e39 steps | 79 by 3*2^77, background only |
| 1RB0RB_1LC1RA_1LF0LD_0LE1LD_1RA1LC_---1LA | same | same | same |
| 1RB1LD_1RC0RC_1LD1RB_1LF0LE_0LA1LE_---1LB | same | same | same |
| 1RB0RB_1RC1RA_0LD1LC_0RA1LE_1LF0LC_---1LA | 3*2^81 (~1e50 steps), quiet | 3*2^66, no halt in 9e40 steps | none reach the old zone |

The disturbance front moves about 3.3 cells per doubling of time in all four. Code:
holdouts/1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA/c/window.c (F08 thread's PR).
