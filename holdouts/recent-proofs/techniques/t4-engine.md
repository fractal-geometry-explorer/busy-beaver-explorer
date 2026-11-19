# t4-engine: DeepMind's ChaoticBell1 fast engine (busycoq PRs 82, 84, 93) and its T4 retargeting (PRs 100, 108, 109)

## The shared core

All nine machines are one of four source tables (exact table isomorphism, checked by brute force over the 720 state
permutations and both orientations; a scratch script, not kept). The tables agree on A0 A1 B0 C0 C1 D0 D1:

- P  = 1RB1RA_1LC0RE_1LD1LB_1RA0LE_1RA0LF_0LB---   start B: 1RB0LE_1RC1RA_1LD0RE_1LA1LD_1LD0RF_0RA--- (PR 82, mirror);
  start C: 1RB1RD_1LC0RE_1LD1LC_1RA0LE_1LC0RF_0RD--- (PR 93, mirror); start D: 1RB0LE_1RC1RB_1LD0RE_1LA1LC_1RB0LF_0LC--- (PR 84, direct)
- Q  = 1RB1RA_1LC0RD_1LD1LB_1RA0LE_0LB1LF_0RD---   start B: 1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA1RF_0LC--- (PR 82, mirror);
  start D: 1RB0LE_1RC1RB_1LD0RA_1LA1LC_0LC1LF_0RA--- (PR 84, direct)
- T3 = 1RB1RA_1LC0RD_1LD1LB_1RA0LE_0LB0LF_0LB---   start C: 1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0RD--- (PR 93, mirror)
- T4 = 1RB1RA_1LC0RD_1LD1LB_1RA0LE_0LB0LF_0RA---   start B: 1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA0RF_0LD--- (PR 108, ours);
  start C: 1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0LC--- (ours; valu42 PR 100); start A + D0 detour:
  1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB0LE (PR 109, ours); start D: 1RB0LE_1RC1RB_1LD0RA_1LA1LC_0LC0LF_0RB--- (open, other thread).

## Technique (all nine)

Invariant shape: run-length tapes over macro words. Digit `D n = 1 (11)^n 00`, its swept form `S n = 1 (01)^(n+1)`,
`PL n`, `DefWord a k = (10)^a 1^k 01 S0`, timers `(111)^k`, counters `(10)^b`. Three macro configurations (source
orientation): `CfgR l r = l A> 0100 r`, `CfgL l r = l <B 1 r`, `CfgJ l r = l <C 100 r`. About 21 base rules
(rule_right/left: D n <-> S n across a sweep; rule_emptyR: append D0 D0 at the blank end; rule_restart: consume one
111 per round trip; rule_collide: 10 D0 D0 to CfgJ (D2 10); rule_leftJ: J delivers +1 to the S word on its left;
rule_pairR: D(2+n) D(2+n) to PL n on the left; defect rules for odd leftovers), each proved by symbolic stepping
(`steps`/`follow` with induction for the scans). Higher-order lemmas: `call r s := forall l, CfgR l r -->* CfgL l s`,
`calls k` (k round trips), loopL/loopR/loopJ over `(111)^k` timers, calls_collision (2k D0 become D3^(k-1) D2 plus
a carry: halve and move up 3 levels), returnP over PL words. The counter: rows of equal digits at levels 0, 3, 6, ...
halved and carried one place up per pass; parity leftovers ("defects") are the chaotic part. No closed-form map.

Engine: `stepFast : FastState -> option FastState`, FastState = (left Runs, RTape, mode in MR/ML/MJ/RAW q d); RTape is
a split list (raw prefix, front digits, reversed back digits, tail) of `(level, count)` pairs in binary N, O(1)
amortized at both ends; batching by division (`capDiv`, `doCallsD`, `trySweepMR_a0`, `sweepLeftSuper`). Soundness
`stepFast_spec`: Some s' gives `denote s -->* denote s'`, None gives `halts` (None only from a raw step on the
undefined transition). `run_pow k` iterates 2^k; `run_ok : is_none (run_pow 22 init) = true` by vm_compute
(`vm_check_eq`). Transport: `Perm (flip src_tm) tm permState` + `flip_halts`/`perm_halts` (PR 93/82/108/100),
none for PR 84 (written directly in the machine's states B/C/D with a separate right-end d0 counter, `stepK`,
`runHalted 1240545`, final `rule_halt` pattern), and the `detour` lemma (halts_in src n -> halts tm) for PR 109.

Sizes: PR 82 3,463 lines, 2,160,351 / 2,162,009 engine steps, max d0 about 10^71.75, 40 s in Coq 8.20.1. PR 84 4,750
lines, 1,240,545 steps, d0 about 10^180.6, about 10^361 machine steps, 87 s. PR 93 5,713 lines, 2,452,242 steps
(both machines, as reported), d0 about 10^420.5, 523 s. T4: 5,730 lines (124 changed vs PR 93: the four rules through
F0 end in `CfgL l (11 X)` instead of `CfgJ l X`, i.e. the carry goes right since 11 D n = D (n+1); trySweepMR_a0
needs la >= 1), run_pow 19; start B 261,156 steps (2^2410 cells, 33 min Coq 8.18), start C 427,055 (2^4360, 4 h),
start A 350,227 (2^3562, 110 min).

Generality: the engine is specific to the core A-D table (the D/S word algebra and the three configurations), but
not to E/F: any machine whose table is this core (up to renaming and mirroring) plus an E/F gadget works if (a) every
macro rule passing through E/F is restated for the new gadget (as T3 -> T4 changed 4 rules), (b) the start state's
run enters the CfgR/CfgL/CfgJ regime, and (c) the run actually reaches the halting transition within a feasible
engine budget (no non-halting proof is possible with this method: it is a proved accelerated simulator, so it decides
only halting machines, or a non-halting one only if the engine reached a provably repeating configuration, which
these chaotic runs never do). Cheap extra reductions: a "detour" transition that ends where the core step ends or
halts (PR 109's lemma) and, for different starts, a new init plus permState.

## Candidates (decision "open")

Found by searching all 608 tables for distance <= 3 transitions from P, Q, T3 or T4 under any renaming and either
orientation (a scratch script, not kept), plus tracker class and record shapes over 3e6 steps.
All the near ones differ from T4 in exactly D0 and E1 (a D0 detour through E/F as in PR 109, and a changed E1, which
sits on the F-event path, so like T3 -> T4 the rules through E1/F would have to be restated).

1. 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB0LF : T4 from A with the PR 109 detour, E1 = 0LE instead of 0LF (E/F swapped
   naming); Chaotic Bell Class 1; its own page and PR 109's sibling note say it behaves like 1RB1RA_..._0LB0LE; record
   shape 269 left / 1752 right in 3e6 steps (PR 109 machine: 228 / 1826).
2. 1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE0RF : T4 mirrored, start C, differs in D0 and E1; Chaotic Bell Class 1;
   the PR 93 machine's page says "same mechanism", sorted 1^(6j+1) 00 blocks; shape 1662 / 200 (127983: 1992 / 266).
3. 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1LF : T4 from A, D0 detour + E1 = 1LE; shape 828 / 1960 (somewhat wider).
4. 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE : T4 from A, D0 detour + E1 = 1RF (T4 naming); shape 873 / 1286.
5. 1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE1LC : T4 mirrored, start C, D0 + E1 differ; shape 1144 / 1387.
6. 1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1LD : T4 mirrored, start B, D0 + E1 differ; shape 2230 / 548.
7. 1RB0RF_0LC---_1LD1LC_1RE0LA_1RA1RD_0RD0RF : T4 mirrored, start D, D0 + E1 differ; Chaotic Bell Class 1; but T4
   from D itself has not halted in the engine yet, so lower odds of a feasible halt.
8. Not near any of the four tables (> 5 transitions), but same block language (1^(6k+1) 00 rows, Chaotic Bell
   Class 1), so the word algebra might transfer with a new state map: 1RB0LE_0RC1RA_1RD0RF_0LE1LD_1RA1LC_---0RE,
   1RB1LD_1RC0LA_0RD1RB_1RE0RF_0LA1LE_---0RA, 1RB0RF_0LC1LB_1RD1LA_1RE0LC_0RA1RD_---0RC.

Caveat for all: the method only proves halting, and only if the engine run halts within budget; candidates 1-7 could
also turn out to run forever (then this method cannot settle them).
