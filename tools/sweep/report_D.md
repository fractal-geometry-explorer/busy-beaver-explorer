# Group D transcription report: the eight frame maps (condensed from the transcribing agent)

`step` is generated from the text of `def next` in each `lean/Phases.lean` (one `if` per Lean case, in match order).
Checked: first 10^6 states equal the existing scripts (fitlib / phasemap / passmap), and map states found in order in
direct runs (1.9e3 to 1e5 states per machine, up to 3e7 steps). accel (maps/_cycle.py: exact batching of translation
cycles of up to 8 Lean cases, keeping first-match order) equals step over 3e7 frames.

| machine | map | bound before | growth | notes |
|---|---|---|---|---|
| 1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD | 78 cases, from z(0,0,2) | 1e8 frames (Lean), 1e15 steps (mrun.c) | ~3.3 sqrt(n) | sampled returns: x4/3 by l mod 3 |
| 1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC | 30 cases, from e(1,0) | same | ~3.3 sqrt(n) | sampled returns: doubling for even l |
| 1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE | 66 cases, from g(0,1) | same | ~4.3 sqrt(n) | sampled returns: pure doubling in a budget |
| 1RB1RF_1LC1LF_0RE1LD_0LB1LD_---1RC_1RA0RD | ps/q, from ps(0,2), halts ps(a,c) c<=1 | 1e11 phases (psq.c) | linear | pass ps(a,c) -> ps(2a+4, c-2a-4) |
| 1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_---0RE | e/r/q, from r(0,2), halts e(x,z) z<=1 | 1e11 phases (~4.1e30 steps) | linear | E(x,z) -> E(2x+4, z-2x-6) |
| 1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_---0RE | e/a/q from a(0,0) | 1e11 phases | linear | same E rule |
| 1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE | e/a/q from a(0,0) | 1e11 phases | linear | **conjugate to 1RB1LE_1RC1RA_... except on a thin set** (phi: r(x,y)->a(x,y-1), q(m,k,t)->q(m,k/2,t)); orbits share 89,633 e-states in the first 1e6 phases, a halt inside a synced stretch is a halt of both |
| 1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_---0RE | e/r/q from r(0,2) | 1e11 phases | linear | same family, not conjugate |

Doubling inside a slowly growing budget (close to x -> 2x mod L); E-run lengths geometric(1/2). No x3/2, so no
resemblance to Antihydra/Collatz/Doucette. The three sqrt(n) machines run 1e11 frames in 54-136 s with accel; the
five linear ones gain only ~2x from batching E-runs.
