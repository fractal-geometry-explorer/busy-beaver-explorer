# Families of the undecided holdouts (20 November 2026)

Of the 608 holdouts, **554** are undecided here: open, cryptid, or covered only by an outside proof that has not been compiled here (34 machines). This note regroups them into families where one proof technique could settle several machines at once, and ranks the families. It replaces the ranking of the 13 November plan (F01 to F12, kept in `families.json` as each machine's `old` family). The machine-readable version is [`families.json`](families.json), written with this note by [`regroup.py`](regroup.py); the [holdout map](../pages/holdouts/index.html) can filter by family.

## How the families were made

- **Table distance.** For every pair of the 608 machines, `regroup.py` counts the transitions that differ between the two tables, minimised over the 720 renamings of the states and the mirror image. Distance 0 is the same table started elsewhere (298 pairs), distance 1 one changed transition (582 pairs). Joining machines at distance 1 or less gives the *table sets*. Machines in one table set share most of their macro rules, so a Lean library written for one usually proves on the others (as `Family.lean` did for all 40 of F05).
- **Mechanism.** Table sets with the same mechanism, read from each machine's own description and the community tracker's class, were joined into one family, and machines with the same mechanism on unrelated tables were added by a pattern on their descriptions (the rules are in `regroup.py`).
- **Ranking.** By the number of machines one argument would settle, weighed by how likely the argument is to work, judged from what is already proved. These are judgements, not results.
- Machines that fit none of the families keep their 13 November family (listed at the end), and Collatz-like machines and cryptids form one parked family.

## Ranking

| rank | family | machines | of which awaiting review | technique | odds |
|---|---|---|---|---|---|
| 0 | **R00** Outside proofs awaiting compilation (busycoq PRs 43 to 68) | 34 (all) | 34 | compile and record | high |
| 1 | **R01** Base-5 marker counter on one five-state core (F05) | 45 |  | one drift invariant on the shared core (first: same-run equivalences, 40 questions to about 10) | medium-low |
| 2 | **R02** Clock and word: a block grows in doubling time while a word map runs 2^k times | 15 |  | automaton invariant for the word map P alone, plus the clock lemma in Lean | medium |
| 3 | **R03** Blocks of 10s split by 01100: one table core with cursors that triple blocks | 15 |  | shared Lean library for the core, then exact block-list runs to hunt halts | medium |
| 4 | **R04** Base-4 counters with countdown timers (Skelet 1-like) | 16 | 1 | halt hunting with exact odometer jumps (PR 83 / 89 method) | medium-high for halts |
| 5 | **R05** Cellular-automaton sweeps: running parity and Sierpinski triangles | 10 |  | prove each sweep is one CA step; closed form by Lucas' theorem for the parity pair | medium for the parity pair, low for the others |
| 6 | **R06** Neighbours of DeepMind's PR 93 tables (the T3 and T4 engine) | 11 |  | retarget the PR 93 engine and run to the halt (halting only) | medium |
| 7 | **R07** Up/down counters and two binary counters with rebuilds | 11 | 2 | compile PRs 57 and 58; prove the closed rebuild maps; extend the wall invariant | medium |
| 8 | **R08** Reservoir counters: a chaotic zone eats a reservoir behind a growing block | 10 |  | Lean leftmost-zone reduction, then a two-zone model | medium for the four, low for the rest |
| 9 | **R09** Word map phi with a counter: one table, a race between word and collisions | 7 |  | port the one-map reduction to the siblings; invariant of the map | medium-low |
| 10 | **R10** Visit laws on streams (busycoq PR 59 family) | 7 | 4 | compile PRs 55 and 59; accelerated visit-law runs for the rest | high for the four pending, low to medium for the three open |
| 11 | **R11** Nested ternary counters (draining odometers) | 7 |  | exact macro simulators to the first top-level overflow | medium for halts |
| 12 | **R12** Two-word sweepers: base-3 and binary counters side by side | 11 |  | decode the middle first | low |
| 13 | **R13** Shifted-run quartet (F09) | 4 |  | transfer theory for the shifted run | medium-low |
| 14 | **R14** Block lists rewritten like a cellular automaton (blocks of 4k+3 ones) | 6 |  | none yet | low |
| parked | **R15** Collatz-like maps and cryptids (parked) | 98 | 3 | halt hunts on proved maps only | very low |
| - | the rest of F01 to F11 | 257 | | no shared technique found | |

## Recommended next attacks

1. **Compile the outside proofs of busycoq PRs 43 to 68** (34 machines). They are the only machines on the list whose proofs exist but have not been checked here, and checking them is mechanical (the same procedure as for PRs 78 to 109). Ten of them also belong to families below (R04, R07, R10 and R15).
2. **R01, the F05 core** (45 machines). The largest family by far, with its whole macro structure already proved in Lean on all 40 core tables. One invariant on the drift settles all of them; the equivalence proofs that cut 40 questions to about 10 are a safe first step.
3. **R02, clock and word** (15 machines on six tables). The clock lemma is in Lean for six; what is left is a finite-state question about one word map per machine, which an automaton search on the word alone can answer far more cheaply than the whole-tape search that failed.
4. **R04 and R11, base-4 and ternary countdown counters** (23 machines). Halt hunting with exact odometer jumps; this kind of family (F06) produced half of the decisions of the week of 13 November, all halting, and short-timer tapes of the same shape are proved to halt.
5. **R05, cellular-automaton sweeps** (10 machines). New idea: for the two running-parity machines, a Lean proof that each sweep is one row of Pascal's triangle mod 2 turns halting into a statement about binary digits (Lucas' theorem).

Next in line: R03 (one table core, a shared library as for F05) and R06 (the PR 93 engine retargeted). R07 and R10 start with the compiles in step 1.

## The families

### R01. Base-5 marker counter on one five-state core (F05) (45 machines)

**Mechanism.** Forty machines are one five-state core, `1RB0LC_0RC0RB_1LD0RE_0LE?LF_1LA0LB_??---` in frame A, differing in D1, F0 and the start; five more use the same core with E1 or F0 changed. The tape is a list of 0010-blocks run like a nested base-5 counter; a machine can halt only at an F-event (the detour through F) that reads a 1.

**Known.** Lean proves the visit law, its closed form and a conservation law for all 40 on each machine's own table (`Family.lean` in each folder); the exact block-list map ran 37 of them to 10^200 steps, every F-event reading 0.

**Technique.** One invariant on the shared core: show that an F-event never reads 1, i.e. that the drift b(i+1) - 5·b(i) is never near 0 when its block runs out. A proof on the core settles all 40 at once; even without it, Lean proofs that variants with the same block list are the same run cut the 40 questions to about 10.

**Odds.** medium-low: halting needs two rare events to coincide, and nothing found so far bounds the drift; but the payoff is the largest of any single argument.

| machine | standing | community class | table set | 13 Nov family | notes |
|---|---|---|---|---|---|
| [`1RB---_0LC0LB_1RF0LD_1RE0RB_1LB0RC_0RD1RA`](1RB---_0LC0LB_1RF0LD_1RE0RB_1LB0RC_0RD1RA/README.md) | open | Skelet 1-like Class 1 | T1 (40) | F05 |  |
| [`1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0LC---`](1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0LC---/README.md) | open | Skelet 1-like Class 1 | T1 (40) | F05 |  |
| [`1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0LE---`](1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0LE---/README.md) | open | Skelet 1-like Class 1 | T1 (40) | F05 |  |
| [`1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---`](1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---/README.md) | open | Skelet 1-like Class 1 | T1 (40) | F05 |  |
| [`1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RB---`](1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RB---/README.md) | open | Skelet 1-like Class 1 | T1 (40) | F05 |  |
| [`1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RE---`](1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RE---/README.md) | open | Skelet 1-like Class 1 | T1 (40) | F05 |  |
| [`1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LA---`](1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LA---/README.md) | open | Skelet 1-like Class 1 | T1 (40) | F05 |  |
| [`1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LB---`](1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LB---/README.md) | open | Skelet 1-like Class 1 | T1 (40) | F05 |  |
| [`1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LC---`](1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LC---/README.md) | open | Skelet 1-like Class 1 | T1 (40) | F05 |  |
| [`1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1RA---`](1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1RA---/README.md) | open | Skelet 1-like Class 1 | T1 (40) | F05 |  |
| [`1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_0LB---`](1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_0LB---/README.md) | open | Skelet 1-like Class 1 | T1 (40) | F05 |  |
| [`1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_0LD---`](1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_0LD---/README.md) | open | Skelet 1-like Class 1 | T1 (40) | F05 |  |
| [`1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_0RE---`](1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_0RE---/README.md) | open | Skelet 1-like Class 1 | T1 (40) | F05 |  |
| [`1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_1LB---`](1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_1LB---/README.md) | open | Skelet 1-like Class 1 | T1 (40) | F05 |  |
| [`1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_1LD---`](1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_1LD---/README.md) | open | Skelet 1-like Class 1 | T1 (40) | F05 |  |
| [`1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_0LD---`](1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_0LD---/README.md) | open | Skelet 1-like Class 1 | T1 (40) | F05 |  |
| [`1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_0LE---`](1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_0LE---/README.md) | open | Skelet 1-like Class 1 | T1 (40) | F05 |  |
| [`1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_0RA---`](1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_0RA---/README.md) | open | Skelet 1-like Class 1 | T1 (40) | F05 |  |
| [`1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_0RC---`](1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_0RC---/README.md) | open | Skelet 1-like Class 1 | T1 (40) | F05 |  |
| [`1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1LD---`](1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1LD---/README.md) | open | Skelet 1-like Class 1 | T1 (40) | F05 |  |
| [`1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1RA---`](1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1RA---/README.md) | open | Skelet 1-like Class 1 | T1 (40) | F05 |  |
| [`1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1RE---`](1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1RE---/README.md) | open | Skelet 1-like Class 1 | T1 (40) | F05 |  |
| [`1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_0LA---`](1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_0LA---/README.md) | open | Skelet 1-like Class 1 | T1 (40) | F05 |  |
| [`1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_0RB---`](1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_0RB---/README.md) | open | Skelet 1-like Class 1 | T1 (40) | F05 |  |
| [`1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_0RE---`](1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_0RE---/README.md) | open | Skelet 1-like Class 1 | T1 (40) | F05 |  |
| [`1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_1LD---`](1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_1LD---/README.md) | open | Skelet 1-like Class 1 | T1 (40) | F05 |  |
| [`1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_1RB---`](1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_1RB---/README.md) | open | Skelet 1-like Class 1 | T1 (40) | F05 |  |
| [`1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_1RE---`](1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_1RE---/README.md) | open | Skelet 1-like Class 1 | T1 (40) | F05 |  |
| [`1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0LA---`](1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0LA---/README.md) | open | Skelet 1-like Class 1 | T1 (40) | F05 |  |
| [`1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0LB---`](1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0LB---/README.md) | open | Skelet 1-like Class 1 | T1 (40) | F05 |  |
| [`1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0LC---`](1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0LC---/README.md) | open | Skelet 1-like Class 1 | T1 (40) | F05 |  |
| [`1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0RA---`](1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0RA---/README.md) | open | Skelet 1-like Class 1 | T1 (40) | F05 |  |
| [`1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0RD---`](1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0RD---/README.md) | open | Skelet 1-like Class 1 | T1 (40) | F05 |  |
| [`1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_1LB---`](1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_1LB---/README.md) | open | Skelet 1-like Class 1 | T1 (40) | F05 |  |
| [`1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_1RC---`](1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_1RC---/README.md) | open | Skelet 1-like Class 1 | T1 (40) | F05 |  |
| [`1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_1RD---`](1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_1RD---/README.md) | open | Skelet 1-like Class 1 | T1 (40) | F05 |  |
| [`1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA1RF_0LD---`](1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA1RF_0LD---/README.md) | open | Skelet 1-like Class 1 | T1 (40) | F05 |  |
| [`1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA1RF_0RC---`](1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA1RF_0RC---/README.md) | open | Skelet 1-like Class 1 | T1 (40) | F05 |  |
| [`1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA1RF_0RE---`](1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA1RF_0RE---/README.md) | open | Skelet 1-like Class 1 | T1 (40) | F05 |  |
| [`1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA1RF_1RE---`](1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA1RF_1RE---/README.md) | open | Skelet 1-like Class 1 | T1 (40) | F05 |  |
| [`1RB0LC_0RC0RB_1LD0RE_0LE0LB_1LA1RF_0LD---`](1RB0LC_0RC0RB_1LD0RE_0LE0LB_1LA1RF_0LD---/README.md) | open | Skelet 1-like Class 1 | T32 (3) | F05 |  |
| [`1RB0LC_0RC0RE_1RD1LF_1LE0RA_0LA0LE_0RB---`](1RB0LC_0RC0RE_1RD1LF_1LE0RA_0LA0LE_0RB---/README.md) | open | Skelet 1-like Class 1 | T32 (3) | F05 |  |
| [`1RB1LF_1LC0RD_0LD0LC_1RE0LA_0RA0RC_0RE---`](1RB1LF_1LC0RD_0LD0LC_1RE0LA_0RA0RC_0RE---/README.md) | open | Skelet 1-like Class 1 | T32 (3) | F05 |  |
| [`1RB0LD_0LB1RC_0RD---_1RE0RF_1LF0RA_0LA0LF`](1RB0LD_0LB1RC_0RD---_1RE0RF_1LF0RA_0LA0LF/README.md) | open | Skelet 1-like Class 1 | T84 (2) | F05 |  |
| [`1RB0RC_1LC0RD_0LD0LC_1RE0LA_0LE1RF_0RA---`](1RB0RC_1LC0RD_0LD0LC_1RE0LA_0LE1RF_0RA---/README.md) | open | Skelet 1-like Class 1 | T84 (2) | F05 |  |

### R02. Clock and word: a block grows in doubling time while a word map runs 2^k times (15 machines)

**Mechanism.** A block at one end grows by 2, 3 or 4 cells per tick and tick k applies one word map P (one trip of the head) 2^k times to the word beside it; halting is possible only when a rebuild of the end goes wrong. Six tables.

**Known.** The clock lemma (block growth and the 2^k trips, whenever the trips return) is proved in Lean for every k on six of them, for example `1RB0RA_1RC0RC_1LD0LE_1RA1LC_1LC0LF_0LC---` and `1RB---_1RC1RF_1LD1RE_1LB1LD_0RB0RC_1RA0LF`. DeepMind's file lists three as cryptids.

**Technique.** Close the word map alone: find a regular language of words that P maps into itself and that never triggers the halting rebuild (a SAT search over automata on the word, much smaller than the whole-tape search that failed in `satctl.json`), then combine it with the clock lemma in Lean. The same pipeline serves every member; only P changes.

**Odds.** medium: the remaining question is one finite-state map per machine, not a counter race; the three DeepMind cryptids are the least likely.

| machine | standing | community class | table set | 13 Nov family | notes |
|---|---|---|---|---|---|
| [`1RB---_1RC1RF_1LD1RE_1LB1LD_0RB0RC_1RA0LF`](1RB---_1RC1RF_1LD1RE_1LB1LD_0RB0RC_1RA0LF/README.md) | open | Shift-overflow counter | T14 (4) | F02 |  |
| [`1RB0LA_1RC---_1RD1RA_1LE1RF_1LC1LE_0RC0RD`](1RB0LA_1RC---_1RD1RA_1LE1RF_1LC1LE_0RC0RD/README.md) | open | Shift-overflow counter | T14 (4) | F02 |  |
| [`1RB1RE_1LC1RD_1LA1LC_0RA0RB_1RF0LE_1RA---`](1RB1RE_1LC1RD_1LA1LC_0RA0RB_1RF0LE_1RA---/README.md) | open | Shift-overflow counter | T14 (4) | F02 |  |
| [`1RB0RA_1RC0RC_1LD0LE_1RA1LC_1LC0LF_0LC---`](1RB0RA_1RC0RC_1LD0LE_1RA1LC_1LC0LF_0LC---/README.md) | open | Shift-overflow counter | T20 (4) | F02 |  |
| [`1RB0RB_1LC0LE_1RD1LB_1RA0RD_1LB0LF_0LB---`](1RB0RB_1LC0LE_1RD1LB_1RA0RD_1LB0LF_0LB---/README.md) | open | Shift-overflow counter | T20 (4) | F02 |  |
| [`1RB0RE_1LC1RA_1LD0LC_1LA0LA_1RA0RF_0RA---`](1RB0RE_1LC1RA_1LD0LC_1LA0LA_1RA0RF_0RA---/README.md) | open | Shift-overflow counter | T20 (4) | F02 |  |
| [`1RB0RF_1RC0RA_1LD1RB_1LE0LD_1LB0LB_0RB---`](1RB0RF_1RC0RA_1LD1RB_1LE0LD_1LB0LB_0RB---/README.md) | open | Shift-overflow counter | T20 (4) | F02 |  |
| [`1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE`](1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/README.md) | open | Shift-overflow counter | T45 (3) | F02 | DeepMind: cryptid |
| [`1RB0RE_1LC1RA_1LD0LC_0RE0LA_1RA1RF_0RA---`](1RB0RE_1LC1RA_1LD0LC_0RE0LA_1RA1RF_0RA---/README.md) | open | Shift-overflow counter | T45 (3) | F02 | DeepMind: cryptid |
| [`1RB1RF_1RC0RA_1LD1RB_1LE0LD_0RA0LB_0RB---`](1RB1RF_1RC0RA_1LD1RB_1LE0LD_0RA0LB_0RB---/README.md) | open | Shift-overflow counter | T45 (3) | F02 | DeepMind: cryptid |
| [`1RB1RF_1LC0RE_1LE1LD_1RE0LC_1RA1RA_1RD---`](1RB1RF_1LC0RE_1LE1LD_1RE0LC_1RA1RA_1RD---/README.md) | open | Shift-overflow counter | T62 (2) | F02 |  |
| [`1RB0LC_1LC0RB_0LE1LD_1LB1LA_0RA1LF_0LA---`](1RB0LC_1LC0RB_0LE1LD_1LB1LA_0RA1LF_0LA---/README.md) | open | Shift-overflow counter | T65 (2) | F02 |  |
| [`1RB0LE_0LC0RB_1RD1LD_1RA1LF_0LB1LE_---1LB`](1RB0LE_0LC0RB_1RD1LD_1RA1LF_0LB1LE_---1LB/README.md) | open | Shift-overflow counter | T88 (2) | F02 |  |
| [`1RB1LC_1LA1RE_0RD0LA_---1LB_1LD0RF_0RE1RB`](1RB1LC_1LA1RE_0RD0LA_---1LB_1LD0RF_0RE1RB/README.md) | open | Shift-overflow counter | - | F03 |  |
| [`1RB1LD_1LC0RE_1LA1RC_0LC0LA_0RF0RC_---0RB`](1RB1LD_1LC0RE_1LA1RC_0LC0LA_0RF0RC_---0RB/README.md) | open | Shift-overflow counter | - | F03 |  |

### R03. Blocks of 10s split by 01100: one table core with cursors that triple blocks (15 machines)

**Mechanism.** Twelve machines one transition apart (tracker class Chaotic Bell Class 3) and three neighbours two transitions away: a list of blocks (10)^n separated by 01100 or single 1s, with a cursor or reflector that walks through it and triples or moves blocks, on a budget held in the first block.

**Known.** Round trips and the moving reflector are proved in Lean for several, for example `1RB0LC_1RC0RA_1LA0LD_1LE0RB_1RD1LF_0LA---` and `1RB0RC_1LC0LD_1RA0LB_1LE0RA_1RD1LF_0LC---`; `1RB1RF_1RC0RE_1LD0RB_1RE0LC_1RA0LE_0RC---` has a halting tape of the same form proved in Lean.

**Technique.** Do for this core what `Family.lean` did for F05: one generated Lean library of the shared rules proved on every member's table, then an exact block-list map per member run far to hunt for halts (the budget rules make a halt plausible).

**Odds.** medium: shared rules make the library cheap; whether the runs halt is unknown.

| machine | standing | community class | table set | 13 Nov family | notes |
|---|---|---|---|---|---|
| [`1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE---`](1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE---/README.md) | open | Chaotic Bell Class 3 | T3 (12) | F07 |  |
| [`1RB0LC_1RC0RA_1LA0LD_1LE0RB_1LC1LF_0LA---`](1RB0LC_1RC0RA_1LA0LD_1LE0RB_1LC1LF_0LA---/README.md) | open | Chaotic Bell Class 3 | T3 (12) | F01 |  |
| [`1RB0LC_1RC0RA_1LA0LD_1LE0RB_1RB1LF_0LA---`](1RB0LC_1RC0RA_1LA0LD_1LE0RB_1RB1LF_0LA---/README.md) | open | Chaotic Bell Class 3 | T3 (12) | F07 |  |
| [`1RB0LC_1RC0RA_1LA0LD_1LE0RB_1RD1LF_0LA---`](1RB0LC_1RC0RA_1LA0LD_1LE0RB_1RD1LF_0LA---/README.md) | open | Chaotic Bell Class 3 | T3 (12) | F07 |  |
| [`1RB0LE_1RC1RF_1RD0RA_1LE0RC_1LC0LD_0RD---`](1RB0LE_1RC1RF_1RD0RA_1LE0RC_1LC0LD_0RD---/README.md) | open | Chaotic Bell Class 3 | T3 (12) | F01 |  |
| [`1RB0RC_1LC0LD_1RA0LB_1LE0RA_1LB1LF_0LC---`](1RB0RC_1LC0LD_1RA0LB_1LE0RA_1LB1LF_0LC---/README.md) | open | Chaotic Bell Class 3 | T3 (12) | F01 |  |
| [`1RB0RC_1LC0LD_1RA0LB_1LE0RA_1RA1LF_0LC---`](1RB0RC_1LC0LD_1RA0LB_1LE0RA_1RA1LF_0LC---/README.md) | open | Chaotic Bell Class 3 | T3 (12) | F07 |  |
| [`1RB0RC_1LC0LD_1RA0LB_1LE0RA_1RD1LF_0LC---`](1RB0RC_1LC0LD_1RA0LB_1LE0RA_1RD1LF_0LC---/README.md) | open | Chaotic Bell Class 3 | T3 (12) | F07 |  |
| [`1RB0RD_1LC0RA_1LA0LB_1RE0LC_1LC1RF_0RB---`](1RB0RD_1LC0RA_1LA0LB_1RE0LC_1LC1RF_0RB---/README.md) | open | Chaotic Bell Class 3 | T3 (12) | F07 |  |
| [`1RB0RD_1LC0RA_1LA0LB_1RE0LC_1LD1RF_0RB---`](1RB0RD_1LC0RA_1LA0LB_1RE0LC_1LD1RF_0RB---/README.md) | open | Chaotic Bell Class 3 | T3 (12) | F07 |  |
| [`1RB0RD_1LC0RA_1LA0LB_1RE0LC_1RA1RF_0RB---`](1RB0RD_1LC0RA_1LA0LB_1RE0LC_1RA1RF_0RB---/README.md) | open | Chaotic Bell Class 3 | T3 (12) | F01 |  |
| [`1RB1LC_1LA0RE_0LD---_1RE0LF_1RF0RD_1LD0LB`](1RB1LC_1LA0RE_0LD---_1RE0LF_1RF0RD_1LD0LB/README.md) | open | Chaotic Bell Class 3 | T3 (12) | F07 |  |
| [`1RB0LE_1LC0RA_1LD0RC_1LE1LF_1LA0LC_0LA---`](1RB0LE_1LC0RA_1LD0RC_1LE1LF_1LA0LC_0LA---/README.md) | open | Chaotic Bell Class 3 | T43 (3) | F07 |  |
| [`1RB0LE_1RC0LB_1RD1RF_1RE0RB_1LA0RD_0RE---`](1RB0LE_1RC0LB_1RD1RF_1RE0RB_1LA0RD_0RE---/README.md) | open | Chaotic Bell Class 3 | T43 (3) | F07 |  |
| [`1RB1RF_1RC0RE_1LD0RB_1RE0LC_1RA0LE_0RC---`](1RB1RF_1RC0RE_1LD0RB_1RE0LC_1RA0LE_0RC---/README.md) | open | Chaotic Bell Class 3 | T43 (3) | F07 |  |

### R04. Base-4 counters with countdown timers (Skelet 1-like) (16 machines)

**Mechanism.** A base-4 counter whose digits sit between blocks, and blocks that lose 4^i (or 9, 24, 96, ...) units per visit like timers; when a timer runs out digits fuse or a level is rebuilt.

**Known.** Digit and sweep rules are proved in Lean for several; for `1RB1RE_1LC0RC_1RA1LD_1RB0LA_0LC1RF_---1RD` and `1RB1RE_1LC0RF_1LA0LD_1LE1LC_0RA0LC_1RA---` Lean proves that tapes of the same shape with short timers halt. `1RB1LF_0RC1RC_1LD0RD_0LE0LA_1RA0LB_---1LD` halts iff its twin `1RB1LE_1RC1LF_0RD1RD_1LE0RE_0LA0LB_---1LE` halts from state B (Lean). `1RB0RB_0LC1RA_1RD1LC_1LA1LE_1LF0LD_---0LA` has a halting proof in busycoq PR 64 (not compiled here).

**Technique.** Halt hunting with exact odometer jumps (the PR 83 / PR 89 method: b^k ticks in one operation, then an exact executor to the halt). In the week of 13 November this kind of family (F06) gave half of all decisions, all of them halting.

**Odds.** medium-high for halts: short-timer tapes halt, so a run that reaches one is a proof.

| machine | standing | community class | table set | 13 Nov family | notes |
|---|---|---|---|---|---|
| [`1RB1LD_1RC1RE_1LA0RA_1RC0LB_0LA1RF_---1RB`](1RB1LD_1RC1RE_1LA0RA_1RC0LB_0LA1RF_---1RB/README.md) | open | Skelet 1-like Class 1 | T15 (4) | F06 |  |
| [`1RB1LD_1RC1RE_1LA0RA_1RC0LB_0LA1RF_---1RD`](1RB1LD_1RC1RE_1LA0RA_1RC0LB_0LA1RF_---1RD/README.md) | open | Skelet 1-like Class 1 | T15 (4) | F01 |  |
| [`1RB1RE_1LC0RC_1RA1LD_1RB0LA_0LC1RF_---1RD`](1RB1RE_1LC0RC_1RA1LD_1RB0LA_0LC1RF_---1RD/README.md) | open | Skelet 1-like Class 1 | T15 (4) | F01 | DeepMind: acceleration |
| [`1RB1LE_0RC---_1RD0LA_1RE0RB_0LA0LF_0LD1LF`](1RB1LE_0RC---_1RD0LA_1RE0RB_0LA0LF_0LD1LF/README.md) | open | Skelet 1-like Class 1 | T40 (3) | F06 |  |
| [`1RB0RE_1LC1LF_1RA1LD_0LB---_1RF1LE_0LB0RA`](1RB0RE_1LC1LF_1RA1LD_0LB---_1RF1LE_0LB0RA/README.md) | open | Skelet 1-like Class 1 | T111 (2) | F06 |  |
| [`1RB1LA_0LC0RE_1LD1LB_1RE1LF_1RC0RA_0RC---`](1RB1LA_0LC0RE_1LD1LB_1RE1LF_1RC0RA_0RC---/README.md) | open | Skelet 1-like Class 1 | T111 (2) | F06 |  |
| [`1RB1LF_1LC1RB_1LF1LD_1LE0RD_1LB---_1LA0LA`](1RB1LF_1LC1RB_1LF1LD_1LE0RD_1LB---_1LA0LA/README.md) | open | Shift-overflow structural counter | T120 (2) | F06 |  |
| [`1RB1LD_1RC1RF_1LA1RD_1RE0LB_---0RA_0LA1RC`](1RB1LD_1RC1RF_1LA1RD_1RE0LB_---0RA_0LA1RC/README.md) | open | Skelet 1-like Class 1 | T123 (2) | F01 |  |
| [`1RB1LE_1RC1LF_0RD1RD_1LE0RE_0LA0LB_---1LE`](1RB1LE_1RC1LF_0RD1RD_1LE0RE_0LA0LB_---1LE/README.md) | open | Skelet 1-like Class 1 | T124 (2) | F06 |  |
| [`1RB1LF_0RC1RC_1LD0RD_0LE0LA_1RA0LB_---1LD`](1RB1LF_0RC1RC_1LD0RD_0LE0LA_1RA0LB_---1LD/README.md) | open | Skelet 1-like Class 1 | T124 (2) | F06 |  |
| [`1RB---_1LC0LC_1RD1LB_1LE1RD_0LA1LF_1LD0RF`](1RB---_1LC0LC_1RD1LB_1LE1RD_0LA1LF_1LD0RF/README.md) | open | Shift-overflow structural counter | - | F06 |  |
| [`1RB---_1RC1RF_1LD1RA_1LB0LE_1LF1LF_0RB0LD`](1RB---_1RC1RF_1LD1RA_1LB0LE_1LF1LF_0RB0LD/README.md) | open | Skelet 1-like Class 1 | - | F06 |  |
| [`1RB0LF_1LC0RC_1RA1LD_0RB0LE_1LC0LB_---1LA`](1RB0LF_1LC0RC_1RA1LD_0RB0LE_1LC0LB_---1LA/README.md) | open | Skelet 1-like Class 1 | - | F06 |  |
| [`1RB0RB_0LC1RA_1RD1LC_1LA1LE_1LF0LD_---0LA`](1RB0RB_0LC1RA_1RD1LC_1LA1LE_1LF0LD_---0LA/README.md) | awaiting review | Shift-overflow bouncer counter | - | - | busycoq PR 64 |
| [`1RB1LF_1LC1RB_1LE1LD_1LB0RD_1LF---_1LA0LA`](1RB1LF_1LC1RB_1LE1LD_1LB0RD_1LF---_1LA0LA/README.md) | open | Shift-overflow structural counter | - | F06 |  |
| [`1RB1RE_1LC0RF_1LA0LD_1LE1LC_0RA0LC_1RA---`](1RB1RE_1LC0RF_1LA0LD_1LE1LC_0RA0LC_1RA---/README.md) | open | Skelet 1-like Class 1 | - | F06 |  |

### R05. Cellular-automaton sweeps: running parity and Sierpinski triangles (10 machines)

**Mechanism.** Each sweep rewrites the tape like one step of a one-dimensional cellular automaton. In `1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF` and its slower twin `1RB0RE_1RC0RC_1LD---_0LB1LE_1RF0LD_1RA1RF` a leftward sweep replaces a binary word by its running parity, so the space-time diagram is Pascal's triangle mod 2; `1RB1LB_1LC0RD_0LE1LA_0RF1RA_1LE0LA_---0RB` runs rule 102 (XOR); the others draw Sierpinski-like triangles on blocks of 1s.

**Known.** Two pairs run through the same tapes (observed); for the XOR machine the bulk-merge trigger is known and was last seen at 4.07·10^6 steps in a 10^11 run.

**Technique.** For the parity machines, prove in Lean that sweep n writes row n of Pascal's triangle mod 2 in 4-cell letters. Lucas' theorem then gives every cell in closed form, and the halting condition becomes a statement about binary digits that may be provable outright. The same template (sweep = one CA step, then a closed form of the CA) is the route for the rest.

**Odds.** medium for the parity pair, low for the others; untried, and a closed form is rare among holdouts.

| machine | standing | community class | table set | 13 Nov family | notes |
|---|---|---|---|---|---|
| [`1RB---_0RC1RD_1LA0LA_1LE0RB_1LF1LE_1LC0LD`](1RB---_0RC1RD_1LA0LA_1LE0RB_1LF1LE_1LC0LD/README.md) | open | Chaotic 1dCA-like in bell | T8 (5) | F11 | DeepMind: reduction |
| [`1RB0LF_1RC1RB_1RD0RA_1RE0RE_1LF---_0LD1LA`](1RB0LF_1RC1RB_1RD0RA_1RE0RE_1LF---_0LD1LA/README.md) | open | Chaotic 1dCA-like in bell | T8 (5) | F11 |  |
| [`1RB0RB_1LC---_0LA1LD_1RE0LC_1RF1RE_1RA0RD`](1RB0RB_1LC---_0LA1LD_1RE0LC_1RF1RE_1RA0RD/README.md) | open | Chaotic 1dCA-like in bell | T8 (5) | F11 |  |
| [`1RB0RE_1RC0RC_1LD---_0LB1LE_1RF0LD_1RA1RF`](1RB0RE_1RC0RC_1LD---_0LB1LE_1RF0LD_1RA1RF/README.md) | open | Chaotic 1dCA-like in bell | T8 (5) | F11 |  |
| [`1RB1RA_1RC0RF_1RD0RD_1LE---_0LC1LF_1RA0LE`](1RB1RA_1RC0RF_1RD0RD_1LE---_0LC1LF_1RA0LE/README.md) | open | Chaotic 1dCA-like in bell | T8 (5) | F11 |  |
| [`1RB0LE_1RC1RB_1RD0RA_0RE---_1LF1LA_1LA1LF`](1RB0LE_1RC1RB_1RD0RA_0RE---_1LF1LA_1LA1LF/README.md) | open | Chaotic 1dCA-like in bell | T19 (4) | F11 |  |
| [`1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF`](1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF/README.md) | open | Chaotic 1dCA-like in bell | T19 (4) | F11 | DeepMind: reduction |
| [`1RB1RA_1LC0RF_1LD1LC_1LE0LB_0LF---_1RA1RB`](1RB1RA_1LC0RF_1LD1LC_1LE0LB_0LF---_1RA1RB/README.md) | open | Chaotic 1dCA-like in bell | T19 (4) | F11 |  |
| [`1RB1RC_1RC1RB_1LD0RA_1LE1LD_1LF0LC_0LA---`](1RB1RC_1RC1RB_1LD0RA_1LE1LD_1LF0LC_0LA---/README.md) | open | Chaotic 1dCA-like in bell | T19 (4) | F11 |  |
| [`1RB1LB_1LC0RD_0LE1LA_0RF1RA_1LE0LA_---0RB`](1RB1LB_1LC0RD_0LE1LA_0RF1RA_1LE0LA_---0RB/README.md) | open | Chaotic 1dCA-like in bouncer | - | F11 |  |

### R06. Neighbours of DeepMind's PR 93 tables (the T3 and T4 engine) (11 machines)

**Mechanism.** Eleven open machines within one transition of the PR 93 tables, whose five decided members all halt (PR 93, PR 100, PR 102, and our 1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA0RF_0LD--- and 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB0LE). Behaviour varies: chaotic bells over runs 1^(6k+1), sweeping transducers, counters with long digits.

**Known.** `1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB0LF` runs 10^1336 steps without a halt on the PR 93 engine, with a Coq skeleton that compiles and waits only for the engine to stop.

**Technique.** Retarget the PR 93 run-length engine (each rule proved sound) to every member and run it to the halt. It can prove halting only; a member that does not halt needs a different argument.

**Odds.** medium: five of sixteen in this neighbourhood halted this way, but the remaining runs are already long.

| machine | standing | community class | table set | 13 Nov family | notes |
|---|---|---|---|---|---|
| [`1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA0RF`](1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA0RF/README.md) | open | Chaotic Bell Class 1 | T2 (16) | F07 |  |
| [`1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1LD`](1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1LD/README.md) | open | Unknown | T2 (16) | F11 |  |
| [`1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1RF`](1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1RF/README.md) | open | Unknown | T2 (16) | F01 |  |
| [`1RB0RF_0LC---_1LD1LC_1RE0LA_1RA1RD_0RD0RF`](1RB0RF_0LC---_1LD1LC_1RE0LA_1RA1RD_0RD0RF/README.md) | open | Chaotic Bell Class 1 | T2 (16) | F07 |  |
| [`1RB0RF_0LC---_1LD1LC_1RE0LA_1RA1RD_0RD1RF`](1RB0RF_0LC---_1LD1LC_1RE0LA_1RA1RD_0RD1RF/README.md) | open | Unknown | T2 (16) | F01 |  |
| [`1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB0LF`](1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB0LF/README.md) | open | Chaotic Bell Class 1 | T2 (16) | F07 |  |
| [`1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1LF`](1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1LF/README.md) | open | Unknown | T2 (16) | F01 |  |
| [`1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE`](1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE/README.md) | open | Unknown | T2 (16) | F11 |  |
| [`1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE0RF`](1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE0RF/README.md) | open | Chaotic Bell Class 1 | T2 (16) | F07 |  |
| [`1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE1LC`](1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE1LC/README.md) | open | Unknown | T2 (16) | F11 |  |
| [`1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE1RF`](1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE1RF/README.md) | open | Unknown | T2 (16) | F01 |  |

### R07. Up/down counters and two binary counters with rebuilds (11 machines)

**Mechanism.** One counter counts up while another counts down; when the down counter is empty a rebuild eats low digits of the other and refills it. A halt needs one exact rebuild (for example a walk that crosses the whole counter).

**Known.** Ticks are proved in Lean for every size; the rebuilds are known in closed form (checked, not proved) and iterated past 10^150,000,000 steps. Two members have outside non-halting proofs: busycoq PR 57 (`1RB1LE_1RC0RB_1LD1RC_1LA1LE_1LF0LA_1LC---`) and PR 58 (`1RB1LC_0RC0RB_1LD0LA_1LE---_1LF1RA_1LA1LC`), neither compiled here.

**Technique.** Compile PRs 57 and 58, then prove the closed rebuild recursions in Lean and extend the PR 57/58 wall invariant to the case where a rebuild reads only part of the counter (that is where it failed for the three siblings).

**Odds.** medium: the rebuilds are already explicit maps; the last step is a number-theoretic inequality.

| machine | standing | community class | table set | 13 Nov family | notes |
|---|---|---|---|---|---|
| [`1RB0RF_1RC1LB_1LD1RE_1LB0LD_1RF0RC_1RA---`](1RB0RF_1RC1LB_1LD1RE_1LB0LD_1RF0RC_1RA---/README.md) | open | Shift-overflow counter | T23 (4) | F03 |  |
| [`1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RF0LE_1RA---`](1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RF0LE_1RA---/README.md) | open | Shift-overflow counter | T23 (4) | F03 |  |
| [`1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RF1RC_1RA---`](1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RF1RC_1RA---/README.md) | open | Shift-overflow counter | T23 (4) | F03 |  |
| [`1RB1LD_1RC0RB_1LA1RC_1LE0LA_1LF---_1LC---`](1RB1LD_1RC0RB_1LA1RC_1LE0LA_1LF---_1LC---/README.md) | open | Shift-overflow counter | T23 (4) | F03 |  |
| [`1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB0RF_0RB---`](1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB0RF_0RB---/README.md) | open | Shift-overflow counter | T119 (2) | F03 |  |
| [`1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB0RF_1RC---`](1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB0RF_1RC---/README.md) | open | Shift-overflow counter | T119 (2) | F03 |  |
| [`1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---`](1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---/README.md) | open | Shift-overflow counter | - | F03 |  |
| [`1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LB`](1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LB/README.md) | open | Shift-overflow counter | - | F03 |  |
| [`1RB1LC_0RC0RB_1LD0LA_1LE---_1LF1RA_1LA1LC`](1RB1LC_0RC0RB_1LD0LA_1LE---_1LF1RA_1LA1LC/README.md) | awaiting review | Shift-overflow counter | - | - | busycoq PR 58 |
| [`1RB1LE_1RC0RB_1LD1RC_1LA1LE_1LF0LA_1LC---`](1RB1LE_1RC0RB_1LD1RC_1LA1LE_1LF0LA_1LC---/README.md) | awaiting review | Shift-overflow counter | - | - | busycoq PR 57 |
| [`1RB1LE_1RC0RB_1RD1LF_1LA0LC_1LD0LA_---0RE`](1RB1LE_1RC0RB_1RD1LF_1LA0LC_1LD0LA_---0RE/README.md) | open | Shift-overflow counter | - | F03 |  |

### R08. Reservoir counters: a chaotic zone eats a reservoir behind a growing block (10 machines)

**Mechanism.** A block of words grows at one end; behind it a zone of about a hundred cells is rewritten like a counter and slowly eats a reservoir; the far end is touched at rare events, and only those can halt.

**Known.** Lean proves the halting pattern for the four 111110-machines; a model of their leftmost zone reproduces every real arrival at the left end. For `1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA1RF_---1RD` the reservoir is decoded as independent mod-4 counters and Lean proves a halt can only happen beyond the far end.

**Technique.** Prove the leftmost-zone reduction in Lean (the 16 November plan's item 3), then model two zones with the block between them. Could settle the four 111110-machines either way, and the same tools apply to the five reservoir eaters.

**Odds.** medium for the four, low for the rest (their next events are 2^1100 sweeps away or more).

| machine | standing | community class | table set | 13 Nov family | notes |
|---|---|---|---|---|---|
| [`1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA`](1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA/README.md) | open | Shift-overflow bouncer counter | T22 (4) | F08 |  |
| [`1RB0RB_1LC1RA_1LF0LD_0LE1LD_1RA1LC_---1LA`](1RB0RB_1LC1RA_1LF0LD_0LE1LD_1RA1LC_---1LA/README.md) | open | Shift-overflow bouncer counter | T22 (4) | F08 |  |
| [`1RB1LD_1RC0RC_1LD1RB_1LF0LE_0LA1LE_---1LB`](1RB1LD_1RC0RC_1LD1RB_1LF0LE_0LA1LE_---1LB/README.md) | open | Shift-overflow bouncer counter | T22 (4) | F08 |  |
| [`1RB1RD_1LC0LC_1RD1LB_1RF0RE_0RA1RE_---1RB`](1RB1RD_1LC0LC_1RD1LB_1RF0RE_0RA1RE_---1RB/README.md) | open | Shift-overflow bouncer counter | T22 (4) | F08 |  |
| [`1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---0RC`](1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---0RC/README.md) | open | Shift-overflow bouncer counter | T128 (2) | F08 |  |
| [`1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---1RE`](1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---1RE/README.md) | open | Shift-overflow bouncer counter | T128 (2) | F08 |  |
| [`1RB0RB_1RC1RA_0LD1LC_0RA1LE_1LF0LC_---1LA`](1RB0RB_1RC1RA_0LD1LC_0RA1LE_1LF0LC_---1LA/README.md) | open | Shift-overflow bouncer counter | - | F08 |  |
| [`1RB1LD_1RC0LE_1LA1RE_0LF1LA_1RB0RB_---0LB`](1RB1LD_1RC0LE_1LA1RE_0LF1LA_1RB0RB_---0LB/README.md) | cryptid | Shift-overflow bouncer counter | - | F12 | DeepMind: reduction |
| [`1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA1RF_---1RD`](1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA1RF_---1RD/README.md) | open | Shift-overflow bouncer counter | - | F08 |  |
| [`1RB1RD_1LC1RA_---1LD_1LE0RA_1LF0LE_0RB0LB`](1RB1RD_1LC1RA_---1LD_1LE0RA_1LF0LE_0RB0LB/README.md) | open | Shift-overflow bouncer counter | - | F08 |  |

### R09. Word map phi with a counter: one table, a race between word and collisions (7 machines)

**Mechanism.** Six machines are one table with A1, F0 or the start changed (plus a separator counter one transition away, `1RB---_1RC0RD_1RD1RA_1LE1RB_0LF0LE_1RF0RD`): a binary counter applies a word map phi twice per step, and anomalies and collision cascades rewrite the word.

**Known.** For `1RB0RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_0LC---` every macro step is proved in Lean as one map on word-and-counter configurations, and Lean proves the machine never halts if that map never fails; it does not fail in 10^8 macro steps.

**Technique.** Port the one-map reduction to the five siblings (same table, so the rules carry over), then look for an invariant of the map. A failure found by running the map would be a halting proof for all members with the same run.

**Odds.** medium-low: the race looks Collatz-like, but the reduction already exists.

| machine | standing | community class | table set | 13 Nov family | notes |
|---|---|---|---|---|---|
| [`1RB---_1RC0RD_1RD1RA_1LE1RB_0LF0LE_1RF0RD`](1RB---_1RC0RD_1RD1RA_1LE1RB_0LF0LE_1RF0RD/README.md) | open | Shift-overflow counter | T5 (7) | F02 |  |
| [`1RB0RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_0LC---`](1RB0RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_0LC---/README.md) | open | Shift-overflow counter | T5 (7) | F03 |  |
| [`1RB0RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_0RB---`](1RB0RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_0RB---/README.md) | open | Shift-overflow counter | T5 (7) | F03 |  |
| [`1RB0RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_1RC---`](1RB0RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_1RC---/README.md) | open | Shift-overflow counter | T5 (7) | F03 |  |
| [`1RB1RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_1RA---`](1RB1RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_1RA---/README.md) | open | Shift-overflow counter | T5 (7) | F03 |  |
| [`1RB1RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_1RC---`](1RB1RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_1RC---/README.md) | open | Shift-overflow counter | T5 (7) | F03 |  |
| [`1RB1RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_1RE---`](1RB1RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_1RE---/README.md) | open | Shift-overflow counter | T5 (7) | F02 |  |

### R10. Visit laws on streams (busycoq PR 59 family) (7 machines)

**Mechanism.** Two binary counters off one engine, read as a rewriting system on streams; the first four rules are those of the PR 59 machines.

**Known.** Busycoq PR 59 claims halting for `1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD0LC_0RC---`, `1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RB_0RC---` and `1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RC---`, and PR 55 non-halting for `1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD1RF_1LA---`; none compiled here. The three open members rewrite 1011 differently and run past round 200,000 (visit law in Lean).

**Technique.** Compile PRs 55 and 59 (four machines). For the three open members, continue the accelerated visit-law run: our two halting proofs from 13 November came from this law.

**Odds.** high for the four pending, low to medium for the three open.

| machine | standing | community class | table set | 13 Nov family | notes |
|---|---|---|---|---|---|
| [`1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD0LC_0RC---`](1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD0LC_0RC---/README.md) | awaiting review | Shift-overflow counter | T31 (3) | - | busycoq PR 59 |
| [`1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RB_0RC---`](1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RB_0RC---/README.md) | awaiting review | Shift-overflow counter | T31 (3) | - | busycoq PR 59 |
| [`1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RC---`](1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RC---/README.md) | awaiting review | Shift-overflow counter | T31 (3) | - | busycoq PR 59; DeepMind: reduction |
| [`1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD1RF_1LA---`](1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD1RF_1LA---/README.md) | awaiting review | Shift-overflow counter | - | - | busycoq PR 55 |
| [`1RB0LB_0RC0LD_1LD1RE_0LA0RF_1RB0RD_0RB---`](1RB0LB_0RC0LD_1LD1RE_0LA0RF_1RB0RD_0RB---/README.md) | open | Shift-overflow counter | - | F02 |  |
| [`1RB0LB_0RC0LF_1LD1RE_0LA0RB_0RD0RF_0LA---`](1RB0LB_0RC0LF_1LD1RE_0LA0RB_0RD0RF_0LA---/README.md) | open | Shift-overflow counter | - | F02 |  |
| [`1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD---`](1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD---/README.md) | open | Shift-overflow counter | - | F02 | DeepMind: acceleration |

### R11. Nested ternary counters (draining odometers) (7 machines)

**Mechanism.** Segments of 111-blocks (or digits between blocks) drained by 3^j per event; segments run out one after another and the counter settles into a new regime.

**Known.** Every rule of `1RB0RF_1LC1RF_1RA0LD_0LC0RE_1LD---_0RC0RD` and `1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RB---` is proved in Lean; `1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RB---` passes round 33,199,619 without a halt, its next event about 2.7·10^12 rounds out.

**Technique.** Exact macro simulators to the first top-level overflow (halt hunting), as for R04.

**Odds.** medium for halts.

| machine | standing | community class | table set | 13 Nov family | notes |
|---|---|---|---|---|---|
| [`1RB---_0RC0LA_1LD0RB_1LE0LF_1RC1LF_0LC0LB`](1RB---_0RC0LA_1LD0RB_1LE0LF_1RC1LF_0LC0LB/README.md) | open | Skelet 1-like Class 1 | T10 (4) | F06 |  |
| [`1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD`](1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD/README.md) | open | Skelet 1-like Class 1 | T10 (4) | F06 |  |
| [`1RB0RF_1LC1RF_1RA0LD_0LC0RE_1LD---_0RC0RD`](1RB0RF_1LC1RF_1RA0LD_0LC0RE_1LD---_0RC0RD/README.md) | open | Skelet 1-like Class 1 | T10 (4) | F06 |  |
| [`1RB1LD_1LC0RE_1LA0LD_0LB0LE_0RB0LF_1RE---`](1RB1LD_1LC0RE_1LA0LD_0LB0LE_0RB0LF_1RE---/README.md) | open | Skelet 1-like Class 1 | T10 (4) | F06 |  |
| [`1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---`](1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/README.md) | open | Skelet 1-like Class 1 | T71 (2) | F06 |  |
| [`1RB0LC_1LA0RD_1RA0LA_1RE1RD_1RA1RF_1LC---`](1RB0LC_1LA0RD_1RA0LA_1RE1RD_1RA1RF_1LC---/README.md) | open | Skelet 1-like Class 1 | T71 (2) | F06 |  |
| [`1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RB---`](1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RB---/README.md) | open | Skelet 1-like Class 1 | - | F06 | DeepMind: acceleration |

### R12. Two-word sweepers: base-3 and binary counters side by side (11 machines)

**Mechanism.** A base-3 counter and binary counters fed by one engine; overflows shift the layout and pile junk into an undecoded middle.

**Known.** The counters are proved in Lean for every size; DeepMind's file classes most of them as cryptids.

**Technique.** Decode the middle first; no multi-machine proof is in sight.

**Odds.** low.

| machine | standing | community class | table set | 13 Nov family | notes |
|---|---|---|---|---|---|
| [`1RB---_1RC0LE_0LD0RF_1LB0RE_0RC0LE_1RD1RA`](1RB---_1RC0LE_0LD0RF_1LB0RE_0RC0LE_1RD1RA/README.md) | open | Shift-overflow counter | T7 (6) | F02 | DeepMind: cryptid |
| [`1RB0LD_0LC0RE_1LA0RD_0RB0LD_1RC1RF_1RA---`](1RB0LD_0LC0RE_1LA0RD_0RB0LD_1RC1RF_1RA---/README.md) | open | Shift-overflow counter | T7 (6) | F02 | DeepMind: cryptid |
| [`1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_0LA---`](1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_0LA---/README.md) | open | Shift-overflow counter | T7 (6) | F03 | DeepMind: cryptid |
| [`1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_0LC---`](1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_0LC---/README.md) | open | Shift-overflow counter | T7 (6) | F02 | DeepMind: cryptid |
| [`1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_1LA---`](1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_1LA---/README.md) | open | Shift-overflow counter | T7 (6) | F02 | DeepMind: cryptid |
| [`1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_1LE---`](1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_1LE---/README.md) | open | Shift-overflow counter | T7 (6) | F02 | DeepMind: cryptid |
| [`1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RA_0LB---`](1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RA_0LB---/README.md) | open | Shift-overflow counter | T91 (2) | F02 | DeepMind: cryptid |
| [`1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RA_0LE---`](1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RA_0LE---/README.md) | open | Shift-overflow counter | T91 (2) | F02 | DeepMind: cryptid |
| [`1RB---_1LC0RF_0RA0LD_1LE1LA_1RF0LF_0LC0RA`](1RB---_1LC0RF_0RA0LD_1LE1LA_1RF0LF_0LC0RA/README.md) | open | Shift-overflow counter | - | F02 | DeepMind: acceleration |
| [`1RB0LD_0LC0RE_1LA0RD_0RB0LF_1RC1LA_0RB---`](1RB0LD_0LC0RE_1LA0RD_0RB0LF_1RC1LA_0RB---/README.md) | open | Shift-overflow counter | - | F03 | DeepMind: cryptid |
| [`1RB0LE_1LC0RE_0RA0LD_1LA0LF_0LC0RA_0RE---`](1RB0LE_1LC0RE_0RA0LD_1LA0LF_0LC0RA_0RE---/README.md) | open | Shift-overflow counter | - | F03 | DeepMind: cryptid |

### R13. Shifted-run quartet (F09) (4 machines)

**Mechanism.** Four tables one transition apart whose runs are one shifted run (observed to 2·10^12 steps): an exact ternary counter whose digits are pairs of long alternating runs read mod 4.

**Known.** The increment and the shuttle are proved in Lean for `1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---`; `1RB1RF_1LC0LB_1RE0LD_1LB0RF_0RA0RC_1RE---` has its own folder (`bb6-1RB1RF_1LC0LB`).

**Technique.** A transfer theory for the shifted run would settle the four at once.

**Odds.** medium-low.

| machine | standing | community class | table set | 13 Nov family | notes |
|---|---|---|---|---|---|
| [`1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---`](1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---/README.md) | open | Unknown | T17 (4) | F09 |  |
| [`1RB0LF_1RC0RB_1LD0RA_0LE0LC_1LB1LF_1LD---`](1RB0LF_1RC0RB_1LD0RA_0LE0LC_1LB1LF_1LD---/README.md) | open | Unknown | T17 (4) | F09 |  |
| [`1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---`](1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---/README.md) | open | Unknown | T17 (4) | F09 |  |
| [`1RB1RF_1LC0LB_1RE0LD_1LB0RF_0RA0RC_1RE---`](../bb6-1RB1RF_1LC0LB/README.md) | open | Unknown | T17 (4) | F09 |  |

### R14. Block lists rewritten like a cellular automaton (blocks of 4k+3 ones) (6 machines)

**Mechanism.** Bouncers whose tape is a list of numbers written as blocks of 4k+3 ones (or a dense and a sparse form), rewritten chaotically on every round trip.

**Known.** Halting patterns only.

**Technique.** None yet; park unless R05 finds a usable closed form.

**Odds.** low.

| machine | standing | community class | table set | 13 Nov family | notes |
|---|---|---|---|---|---|
| [`1RB---_0RC0LA_1LD0RB_1LE0LB_1LF0LC_1LB1RE`](1RB---_0RC0LA_1LD0RB_1LE0LB_1LF0LC_1LB1RE/README.md) | open | Chaotic 1dCA-like in bouncer | T6 (6) | F11 |  |
| [`1RB---_0RC0LA_1LD0RB_1LE1LD_1LF0LC_1LB1RE`](1RB---_0RC0LA_1LD0RB_1LE1LD_1LF0LC_1LB1RE/README.md) | open | Chaotic 1dCA-like in bouncer | T6 (6) | F11 |  |
| [`1RB0LE_1RC0RE_1RD0RA_1RE1LC_0LA0RF_1LE---`](1RB0LE_1RC0RE_1RD0RA_1RE1LC_0LA0RF_1LE---/README.md) | open | Chaotic 1dCA-like in bouncer | T6 (6) | F11 |  |
| [`1RB0RD_1RC0RE_1RD1LB_0LE0RF_1RA0LD_1LD---`](1RB0RD_1RC0RE_1RD1LB_0LE0RF_1RA0LD_1LD---/README.md) | open | Chaotic 1dCA-like in bouncer | T6 (6) | F11 |  |
| [`1RB1LE_0LC0RF_1RD0LB_1RE1RD_1RA0RC_1LB---`](1RB1LE_0LC0RF_1RD0LB_1RE1RD_1RA0RC_1LB---/README.md) | open | Chaotic 1dCA-like in bouncer | T6 (6) | F11 |  |
| [`1RB1RA_1RC0RE_1RD1LB_0LE0RF_1RA0LD_1LD---`](1RB1RA_1RC0RE_1RD1LB_0LE0RF_1RA0LD_1LD---/README.md) | open | Chaotic 1dCA-like in bouncer | T6 (6) | F11 |  |

### R15. Collatz-like maps and cryptids (parked) (98 machines)

**Mechanism.** The run is (provably, for many) the orbit of an explicit Collatz-like map: 3/2 and 4/3 growth with a parity- or residue-driven counter (Antihydra-like), doubling maps modulo a growing number, Euclid-like two-counter games, halving cascades.

**Known.** Lean proves `halts_iff` for an explicit map for many of them (the index's 'proved map' column); DeepMind's file has a map or a cryptid label for most.

**Technique.** No proof technique applies: these are open number-theory questions. Only halting can be decided, by running the proved maps far with big integers when the map is 'probviously halting'.

**Odds.** very low for non-halting; occasional halts.

| machine | standing | community class | table set | 13 Nov family | notes |
|---|---|---|---|---|---|
| [`1RB---_0RC0RB_1LD1LE_1LC1RF_1RB0LE_1RA0RD`](1RB---_0RC0RB_1LD1LE_1LC1RF_1RB0LE_1RA0RD/README.md) | open | Bell-like | T4 (7) | F04 | DeepMind: cryptid |
| [`1RB---_1LC0RB_0LD0LC_1RE1RB_1RD1LF_1LA0LE`](1RB---_1LC0RB_0LD0LC_1RE1RB_1RD1LF_1LA0LE/README.md) | open | Bell-like | T4 (7) | F04 | DeepMind: cryptid |
| [`1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LA---`](1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LA---/README.md) | open | Bell-like | T4 (7) | F04 | DeepMind: cryptid |
| [`1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LC---`](1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LC---/README.md) | open | Bell-like | T4 (7) | F04 | DeepMind: cryptid |
| [`1RB0RE_1RC---_0RD0RC_1LE1LF_1LD1RA_1RC0LF`](1RB0RE_1RC---_0RD0RC_1LE1LF_1LD1RA_1RC0LF/README.md) | open | Bell-like | T4 (7) | F04 | DeepMind: cryptid |
| [`1RB0RF_1LC---_1LF1LD_1RE0LD_0RC0RE_1LC1RA`](1RB0RF_1LC---_1LF1LD_1RE0LD_0RC0RE_1LC1RA/README.md) | open | Bell-like | T4 (7) | F04 | DeepMind: cryptid |
| [`1RB0RF_1LC---_1RD0LC_0RE0RD_1LF1LC_1LE1RA`](1RB0RF_1LC---_1RD0LC_0RE0RD_1LF1LC_1LE1RA/README.md) | open | Bell-like | T4 (7) | F04 | DeepMind: cryptid |
| [`1RB---_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA`](1RB---_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA/README.md) | cryptid | Bell-like | T11 (4) | F04 | DeepMind: reduction |
| [`1RB0LC_1RC1RE_1LA0LD_0RB0RA_1RB1RF_1RD---`](1RB0LC_1RC1RE_1LA0LD_0RB0RA_1RB1RF_1RD---/README.md) | open | Bell-like | T11 (4) | F04 | DeepMind: reduction |
| [`1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`](1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---/README.md) | cryptid | Bell-like | T11 (4) | F04 | DeepMind: reduction |
| [`1RB1RD_1LC0LE_1RA0LB_1RA1RF_0RA0RC_1RE---`](1RB1RD_1LC0LE_1RA0LB_1RA1RF_0RA0RC_1RE---/README.md) | open | Bell-like | T11 (4) | F04 | DeepMind: reduction |
| [`1RB0LC_1LA1RE_1LD1RE_1RE0LA_0RA1RF_0RB---`](1RB0LC_1LA1RE_1LD1RE_1RE0LA_0RA1RF_0RB---/README.md) | open | Bell-like | T34 (3) | F04 |  |
| [`1RB1LC_1LA0RD_0LB1LF_1RE1LC_1LC0RB_0LA---`](1RB1LC_1LA0RD_0LB1LF_1RE1LC_1LC0RB_0LA---/README.md) | open | Bell-like | T34 (3) | F04 |  |
| [`1RB1LC_1LC0RF_0LF1LD_0LE---_1RF1LC_1LE0RA`](1RB1LC_1LC0RF_0LF1LD_0LE---_1RF1LC_1LE0RA/README.md) | open | Bell-like | T34 (3) | F04 |  |
| [`1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE`](1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE/README.md) | cryptid | Quadratic Mess | T38 (3) | F12 | halts-iff map in Lean; DeepMind: map |
| [`1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_---0RE`](1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_---0RE/README.md) | cryptid | Quadratic Mess | T38 (3) | F12 | halts-iff map in Lean; DeepMind: map |
| [`1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_---0LE`](1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_---0LE/README.md) | cryptid | Quadratic Mess | T38 (3) | F12 | halts-iff map in Lean; DeepMind: map |
| [`1RB0RA_0RC0LB_1LD1RF_1LE1RA_1RD1RB_1LA---`](1RB0RA_0RC0LB_1LD1RF_1LE1RA_1RD1RB_1LA---/README.md) | open | Bell-like | T46 (3) | F04 |  |
| [`1RB1LC_1LA1LD_1LD0LC_0LE0RD_1RA1LF_1RC---`](1RB1LC_1LA1LD_1LD0LC_0LE0RD_1RA1LF_1RC---/README.md) | open | Bell-like | T46 (3) | F04 |  |
| [`1RB1LF_1RC1LD_1LB1LE_1LE0LD_0LA0RE_1RD---`](1RB1LF_1RC1LD_1LB1LE_1LE0LD_0LA0RE_1RD---/README.md) | open | Bell-like | T46 (3) | F04 |  |
| [`1RB0RB_1LC1RE_1LF0LD_1RA1LD_1RC1RB_---1LC`](1RB0RB_1LC1RE_1LF0LD_1RA1LD_1RC1RB_---1LC/README.md) | cryptid | Quadratic Mess | T50 (3) | F12 | halts-iff map in Lean; DeepMind: map |
| [`1RB0RF_1RC1RF_1LD0LE_---1LC_1RA1LE_1LC1RB`](1RB0RF_1RC1RF_1LD0LE_---1LC_1RA1LE_1LC1RB/README.md) | cryptid | Quadratic Mess | T50 (3) | F12 | halts-iff map in Lean; DeepMind: map |
| [`1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE`](1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE/README.md) | cryptid | Quadratic Mess | T50 (3) | F12 | halts-iff map in Lean; DeepMind: map |
| [`1RB1LB_0RC0LD_1LD1RE_1RC0LA_1RD1RF_0RD---`](1RB1LB_0RC0LD_1LD1RE_1RC0LA_1RD1RF_0RD---/README.md) | open | Bell-like | T55 (3) | F04 |  |
| [`1RB1LC_1LA0RD_1LB1LF_1LE1RE_0LA0RB_0LB---`](1RB1LC_1LA0RD_1LB1LF_1LE1RE_0LA0RB_0LB---/README.md) | open | Bell-like | T55 (3) | F04 |  |
| [`1RB1RF_1RC0LD_1LB1RA_1RE1LE_0RC0LB_0RB---`](1RB1RF_1RC0LD_1LB1RA_1RE1LE_0RC0LB_0RB---/README.md) | open | Bell-like | T55 (3) | F04 |  |
| [`1RB1LB_1RC1LD_1LA1RE_1RD0LA_0RB0RF_0RA---`](1RB1LB_1RC1LD_1LA1RE_1RD0LA_0RB0RF_0RA---/README.md) | open | Bell-like | T56 (3) | F04 |  |
| [`1RB1LE_1LC1RC_1LA1RD_1LD0RB_0LC0LF_0LB---`](1RB1LE_1LC1RC_1LA1RD_1LD0RB_0LC0LF_0LB---/README.md) | open | Bell-like | T56 (3) | F04 |  |
| [`1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC`](1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC/README.md) | open | Bell-like | T56 (3) | F04 | halts-iff map in Lean |
| [`1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_---0RE`](1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_---0RE/README.md) | cryptid | Cubic Mess | T57 (3) | F12 | halts-iff map in Lean; DeepMind: map |
| [`1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_---0RE`](1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_---0RE/README.md) | cryptid | Cubic Mess | T57 (3) | F12 | halts-iff map in Lean; DeepMind: map |
| [`1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE`](1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE/README.md) | cryptid | Cubic Mess | T57 (3) | F12 | halts-iff map in Lean; DeepMind: map |
| [`1RB---_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD`](1RB---_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD/README.md) | cryptid | Quadratic Mess | T63 (2) | F12 | halts-iff map in Lean; DeepMind: map |
| [`1RB1RF_1LC---_1LE1RD_1RA0RC_0LF0LA_0LD0RB`](1RB1RF_1LC---_1LE1RD_1RA0RC_0LF0LA_0LD0RB/README.md) | cryptid | Quadratic Mess | T63 (2) | F12 | halts-iff map in Lean; DeepMind: map |
| [`1RB0LA_0RC1RD_0LD1RE_1LA0RF_0RD0LD_1RD---`](1RB0LA_0RC1RD_0LD1RE_1LA0RF_0RD0LD_1RD---/README.md) | open | Chaotic Fractal Type 1 | T64 (2) | F04 |  |
| [`1RB0LF_1LC0RB_0LD1LA_0RA1LE_0LA0RA_1LA---`](1RB0LF_1LC0RB_0LD1LA_0RA1LE_0LA0RA_1LA---/README.md) | open | Chaotic Fractal Type 1 | T64 (2) | F04 |  |
| [`1RB0LB_1LC0RE_1LA1LD_0LC---_0RB0RF_1RE1RB`](1RB0LB_1LC0RE_1LA1LD_0LC---_0RB0RF_1RE1RB/README.md) | cryptid | Bell-like | T70 (2) | F12 | halts-iff map in Lean; DeepMind: map |
| [`1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RB---`](1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RB---/README.md) | cryptid | Bell-like | T70 (2) | F12 | halts-iff map in Lean; DeepMind: map |
| [`1RB0LC_1LC0RD_1LF1LA_1LB1RE_1RB1LE_---0LE`](1RB0LC_1LC0RD_1LF1LA_1LB1RE_1RB1LE_---0LE/README.md) | cryptid | Bell-like | T76 (2) | F12 | halts-iff map in Lean; DeepMind: map |
| [`1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_---0LA`](1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_---0LA/README.md) | cryptid | Bell-like | T76 (2) | F12 | halts-iff map in Lean; DeepMind: map |
| [`1RB0LF_0LC0RE_0RA1LD_1LB0LD_0RA1RC_1LA---`](1RB0LF_0LC0RE_0RA1LD_1LB0LD_0RA1RC_1LA---/README.md) | open | Unknown | T92 (2) | F04 |  |
| [`1RB0RA_0RC0LE_0LD1RA_1LB0RF_0LD1LC_1RD---`](1RB0RA_0RC0LE_0LD1RA_1LB0RF_0LD1LC_1RD---/README.md) | open | Unknown | T92 (2) | F04 |  |
| [`1RB0LF_1LC0LD_1RD1LB_---1RE_0RA1RE_1LA0LE`](1RB0LF_1LC0LD_1RD1LB_---1RE_0RA1RE_1LA0LE/README.md) | awaiting review | Quadratic Mess | T97 (2) | - | busycoq PR 67; halts-iff map in Lean; DeepMind: map |
| [`1RB0RE_1LC0RA_1RF0RD_---1LE_0LB1LE_1LE1RC`](1RB0RE_1LC0RA_1RF0RD_---1LE_0LB1LE_1LE1RC/README.md) | awaiting review | Quadratic Mess | T97 (2) | - | busycoq PR 67; DeepMind: map |
| [`1RB0RA_1LC0LE_1RA1LD_0LB1LF_1LD0RC_1LB---`](1RB0RA_1LC0LE_1RA1LD_0LB1LF_1LD0RC_1LB---/README.md) | open | Bell-like | T101 (2) | F04 |  |
| [`1RB0RE_1LC1RD_1LA0LC_0RA1RF_1RD0LB_1RA---`](1RB0RE_1LC1RD_1LA0LC_0RA1RF_1RD0LB_1RA---/README.md) | open | Bell-like | T101 (2) | F04 |  |
| [`1RB0RA_1LC1RA_0LD1LD_0LE0LC_1LA0LF_---1LC`](1RB0RA_1LC1RA_0LD1LD_0LE0LC_1LA0LF_---1LC/README.md) | open | Chaotic Fractal Type 1 | T103 (2) | F04 |  |
| [`1RB1LE_0RC1RC_0RD0RB_1RE0RF_1LA0LE_---1RB`](1RB1LE_0RC1RC_0RD0RB_1RE0RF_1LA0LE_---1RB/README.md) | open | Chaotic Fractal Type 1 | T103 (2) | F04 |  |
| [`1RB0RC_1LC1RF_1RE0LD_1LC1LA_---1RD_0RB0RA`](1RB0RC_1LC1RF_1RE0LD_1LC1LA_---1RD_0RB0RA/README.md) | open | Bell-like | T105 (2) | F04 |  |
| [`1RB1LF_1LC0RD_---1LD_1RB1RE_1LA0LB_0LA0LE`](1RB1LF_1LC0RD_---1LD_1RB1RE_1LA0LB_0LA0LE/README.md) | open | Bell-like | T105 (2) | F04 |  |
| [`1RB1LF_1RC1RF_0LD1RE_---1LC_0RB1RE_1LA0LE`](1RB1LF_1RC1RF_0LD1RE_---1LC_0RB1RE_1LA0LE/README.md) | cryptid | Cubic Mess | T125 (2) | F12 | halts-iff map in Lean; DeepMind: map |
| [`1RB1RF_1LC1LF_0RE1LD_0LB1LD_---1RC_1RA0RD`](1RB1RF_1LC1LF_0RE1LD_0LB1LD_---1RC_1RA0RD/README.md) | cryptid | Cubic Mess | T125 (2) | F12 | halts-iff map in Lean; DeepMind: map |
| [`1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE`](1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE/README.md) | cryptid | Quadratic Mess | T127 (2) | F12 | halts-iff map in Lean; DeepMind: map |
| [`1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD`](1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD/README.md) | cryptid | Quadratic Mess | T127 (2) | F12 | halts-iff map in Lean; DeepMind: map |
| [`1RB---_1LC0LD_0RF0LD_0LE0RA_0LC1RA_1RC1RD`](1RB---_1LC0LD_0RF0LD_0LE0RA_0LC1RA_1RC1RD/README.md) | open | Bell-like | - | F04 | halts-iff map in Lean |
| [`1RB0LC_0LC0RF_1RD1LC_0RA1LE_---0LD_1LF1LA`](1RB0LC_0LC0RF_1RD1LC_0RA1LE_---0LD_1LF1LA/README.md) | cryptid | Bell-like | - | F12 | halts-iff map in Lean; DeepMind: map |
| [`1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_---1RA`](1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_---1RA/README.md) | cryptid | Quadratic Mess | - | F12 | halts-iff map in Lean; DeepMind: map |
| [`1RB0LD_0RC1RB_0RD0RA_1LE0RD_1LF---_0LA1LA`](1RB0LD_0RC1RB_0RD0RA_1LE0RD_1LF---_0LA1LA/README.md) | cryptid | Cubic Mess | - | F12 | DeepMind: map |
| [`1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---`](1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---/README.md) | open | Bell-like | - | F04 | DeepMind: cryptid |
| [`1RB0LD_1RC1RA_1LD0RB_1LE1LA_1RF0RC_---1RE`](1RB0LD_1RC1RA_1LD0RB_1LE1LA_1RF0RC_---1RE/README.md) | cryptid | Bell-like | - | F12 | halts-iff map in Lean; DeepMind: map |
| [`1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA`](1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA/README.md) | cryptid | Quadratic Mess | - | F12 | DeepMind: map |
| [`1RB0LE_1LC0RD_0RA1LD_0LC1RA_1LF1LA_---1LA`](1RB0LE_1LC0RD_0RA1LD_0LC1RA_1LF1LA_---1LA/README.md) | open | Bell-like | - | F04 |  |
| [`1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RC---`](1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RC---/README.md) | cryptid | Cubic Mess | - | F12 | DeepMind: map |
| [`1RB0LE_1RC0RF_0RD0RB_1RE0RC_1LA0LA_1RA---`](1RB0LE_1RC0RF_0RD0RB_1RE0RC_1LA0LA_1RA---/README.md) | open | Bell-like | - | F04 |  |
| [`1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA`](1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA/README.md) | cryptid | Quadratic Mess | - | F01 | halts-iff map in Lean; DeepMind: map |
| [`1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA`](1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA/README.md) | awaiting review | Cubic Mess | - | - | busycoq PR 60; halts-iff map in Lean; DeepMind: map |
| [`1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_---1LB`](1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_---1LB/README.md) | cryptid | Quadratic Mess | - | F12 | halts-iff map in Lean; DeepMind: map |
| [`1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD`](1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD/README.md) | cryptid | Cubic Mess | - | F12 | halts-iff map in Lean; DeepMind: map |
| [`1RB0RD_0RC1RE_1RD0LA_1LE1LC_1RF0LD_---0RA`](1RB0RD_0RC1RE_1RD0LA_1LE1LC_1RF0LD_---0RA/README.md) | cryptid | Bell-like | - | F12 | halts-iff map in Lean; DeepMind: map |
| [`1RB0RE_0LC1LE_0RD1LD_1RA1LF_1LC0RA_0LB---`](1RB0RE_0LC1LE_0RD1LD_1RA1LF_1LC0RA_0LB---/README.md) | open | Bell-like | - | F04 |  |
| [`1RB0RE_1LC1LD_0RA0LD_1LB0LA_1RF1RA_---1LB`](1RB0RE_1LC1LD_0RA0LD_1LB0LA_1RF1RA_---1LB/README.md) | cryptid | Bell-like | - | F12 | halts-iff map in Lean; DeepMind: map |
| [`1RB0RE_1RC0RF_1LD1RA_1LB1LD_1RA1LB_---0LD`](1RB0RE_1RC0RF_1LD1RA_1LB1LD_1RA1LB_---0LD/README.md) | open | Bell-like | - | F04 |  |
| [`1RB0RF_0LC1RE_---1LD_1LE0LB_0RF0LD_1RD1RA`](1RB0RF_0LC1RE_---1LD_1LE0LB_0RF0LD_1RD1RA/README.md) | open | Bell-like | - | F04 |  |
| [`1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_---0LD`](1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_---0LD/README.md) | cryptid | Cubic Mess | - | F12 | halts-iff map in Lean; DeepMind: map |
| [`1RB1LA_1RC0RF_1RD---_0LE1RB_---0LA_1LD1RF`](1RB1LA_1RC0RF_1RD---_0LE1RB_---0LA_1LD1RF/README.md) | open | Cubic Mess | - | F12 | DeepMind: reduction |
| [`1RB1LB_1LC1LA_1RD0LB_1RA1RE_1RF0RD_---1RD`](1RB1LB_1LC1LA_1RD0LB_1RA1RE_1RF0RD_---1RD/README.md) | open | Bell-like | - | F04 | DeepMind: acceleration |
| [`1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC`](1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC/README.md) | cryptid | Cubic Mess | - | F12 | halts-iff map in Lean; DeepMind: map |
| [`1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LF---_0RA1LA`](1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LF---_0RA1LA/README.md) | cryptid | Bell-like | - | F01 | DeepMind: map |
| [`1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RB1RF_---1RD`](1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RB1RF_---1RD/README.md) | cryptid | Quadratic Mess | - | F12 | halts-iff map in Lean; DeepMind: map |
| [`1RB1LD_1RC1RE_0LA1LB_0LD1LC_1RF0RA_---0RC`](1RB1LD_1RC1RE_0LA1LB_0LD1LC_1RF0RA_---0RC/README.md) | cryptid | Bell-like | - | F12 | halts-iff map in Lean; DeepMind: map |
| [`1RB1LE_0LC0LB_1RD1LC_1RD1RA_1RF0LA_---1RE`](1RB1LE_0LC0LB_1RD1LC_1RD1RA_1RF0LA_---1RE/README.md) | cryptid | Bell-like | - | F12 | DeepMind: map |
| [`1RB1LE_1LB1LC_1RD0LE_---0RB_1RF1LA_0RA0RD`](1RB1LE_1LB1LC_1RD0LE_---0RB_1RF1LA_0RA0RD/README.md) | cryptid | Quadratic Mess | - | F12 | DeepMind: map |
| [`1RB1LE_1LC0RA_0RF0LD_1LE1LA_1RC0LB_---1RC`](1RB1LE_1LC0RA_0RF0LD_1LE1LA_1RC0LB_---1RC/README.md) | cryptid | Quadratic Mess | - | F12 | DeepMind: map |
| [`1RB1LF_0RC1RD_1LA1LD_1LE0RA_---1LC_0LA1LA`](1RB1LF_0RC1RD_1LA1LD_1LE0RA_---1LC_0LA1LA/README.md) | cryptid | Quadratic Mess | - | F12 | halts-iff map in Lean; DeepMind: map |
| [`1RB1LF_1LC0RD_---1LA_0LA0RE_1LA1RA_1LB0LD`](1RB1LF_1LC0RD_---1LA_0LA0RE_1LA1RA_1LB0LD/README.md) | open | Bell-like | - | F04 | halts-iff map in Lean |
| [`1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_---1LC`](1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_---1LC/README.md) | cryptid | Cubic Mess | - | F12 | halts-iff map in Lean; DeepMind: map |
| [`1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA`](1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA/README.md) | cryptid | Bell-like | - | F12 | halts-iff map in Lean; DeepMind: map |
| [`1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA0LB_---0LC`](1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA0LB_---0LC/README.md) | cryptid | Bell-like | - | F12 | DeepMind: map |
| [`1RB1RA_1LC0RB_1LD0LB_1RA0LE_---1LF_1LB0LA`](1RB1RA_1LC0RB_1LD0LB_1RA0LE_---1LF_1LB0LA/README.md) | open | Bell-like | - | F04 |  |
| [`1RB1RC_1LC1LE_1RA1RD_0RF0RE_1LA0LB_---1RA`](1RB1RC_1LC1LE_1RA1RD_0RF0RE_1LA0LB_---1RA/README.md) | cryptid | Bell-like | - | F12 | halts-iff map in Lean; DeepMind: map |
| [`1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_---0RE`](1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_---0RE/README.md) | cryptid | Cubic Mess | - | F12 | halts-iff map in Lean; DeepMind: map |
| [`1RB1RD_1LC0RD_1RF1RB_1LE0RA_0LB0LE_---0RC`](1RB1RD_1LC0RD_1RF1RB_1LE0RA_0LB0LE_---0RC/README.md) | cryptid | Bell-like | - | F12 | halts-iff map in Lean; DeepMind: map |
| [`1RB1RE_1LC0RA_0RD1LB_---1RC_1LF1RE_0LB0LE`](1RB1RE_1LC0RA_0RD1LB_---1RC_1LF1RE_0LB0LE/README.md) | cryptid | Quadratic Mess | - | F12 | halts-iff map in Lean; DeepMind: map |
| [`1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_---1RA`](1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_---1RA/README.md) | open | Bell-like | - | F04 | DeepMind: acceleration |
| [`1RB1RE_1LC1LD_---1LA_1LB1LE_0RF0RA_1LD1RF`](1RB1RE_1LC1LD_---1LA_1LB1LE_0RF0RA_1LD1RF/README.md) | cryptid | Bell-like | - | F12 | halts-iff map in Lean; DeepMind: map |
| [`1RB1RE_1LC1RE_---1LD_1LE0LB_0RF0LD_1RD1RA`](1RB1RE_1LC1RE_---1LD_1LE0LB_0RF0LD_1RD1RA/README.md) | open | Bell-like | - | F04 |  |
| [`1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE`](1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE/README.md) | cryptid | Cubic Mess | - | F12 | halts-iff map in Lean; DeepMind: map |
| [`1RB1RF_1LC1RD_1LA1LC_1RA0RE_1RD1LA_---0LE`](1RB1RF_1LC1RD_1LA1LC_1RA0RE_1RD1LA_---0LE/README.md) | open | Bell-like | - | F04 |  |

### R00. Outside proofs awaiting compilation (busycoq PRs 43 to 68) (34 machines)

Compile each pull request on busycoq's BB6 branch with Print Assumptions appended, as was done for PRs 78 to 109 (`holdouts/external.json`), and record it. No research, and it can move every one of these machines from 'awaiting review' to decided here. Machines here that also belong to a family above are listed there too.

| machine | standing | community class | table set | 13 Nov family | notes |
|---|---|---|---|---|---|
| [`1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD0LC_0RC---`](1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD0LC_0RC---/README.md) | awaiting review | Shift-overflow counter | T31 (3) | - | busycoq PR 59 |
| [`1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RB_0RC---`](1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RB_0RC---/README.md) | awaiting review | Shift-overflow counter | T31 (3) | - | busycoq PR 59 |
| [`1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RC---`](1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RC---/README.md) | awaiting review | Shift-overflow counter | T31 (3) | - | busycoq PR 59; DeepMind: reduction |
| [`1RB0LD_0RC---_0RD0RF_1LE0LA_1LF1LE_1RA0RD`](1RB0LD_0RC---_0RD0RF_1LE0LA_1LF1LE_1RA0RD/README.md) | awaiting review | Unknown | T36 (3) | - | busycoq PR 55 |
| [`1RB0RD_1RC1RB_1LD0LA_1LE0RA_0LF---_0LA0LC`](1RB0RD_1RC1RB_1LD0LA_1LE0RA_0LF---_0LA0LC/README.md) | awaiting review | Unknown | T36 (3) | - | busycoq PR 55 |
| [`1RB0RE_1RC0LE_0RD---_0RE0RA_1LF0LB_1LA1LF`](1RB0RE_1RC0LE_0RD---_0RE0RA_1LF0LB_1LA1LF/README.md) | awaiting review | Unknown | T36 (3) | - | busycoq PR 55 |
| [`1RB0RC_0LC0LE_1RA0RD_1LB1RF_1LC1LB_0RA---`](1RB0RC_0LC0LE_1RA0RD_1LB1RF_1LC1LB_0RA---/README.md) | awaiting review | Unknown | T51 (3) | - | busycoq PR 62 |
| [`1RB0RD_1RC0RA_0LA0LE_1LC1RF_1LA1LC_0RB---`](1RB0RD_1RC0RA_0LA0LE_1LC1RF_1LA1LC_0RB---/README.md) | awaiting review | Unknown | T51 (3) | - | busycoq PR 62 |
| [`1RB1RD_1LC0LE_1LD0LB_0RB0RA_1RD1LF_0LC---`](1RB1RD_1LC0LE_1LD0LB_0RB0RA_1RD1LF_0LC---/README.md) | awaiting review | Unknown | T51 (3) | - | busycoq PR 61, 62, 63 |
| [`1RB0LF_1LC0LD_1RD1LB_---1RE_0RA1RE_1LA0LE`](1RB0LF_1LC0LD_1RD1LB_---1RE_0RA1RE_1LA0LE/README.md) | awaiting review | Quadratic Mess | T97 (2) | - | busycoq PR 67; halts-iff map in Lean; DeepMind: map |
| [`1RB0RE_1LC0RA_1RF0RD_---1LE_0LB1LE_1LE1RC`](1RB0RE_1LC0RA_1RF0RD_---1LE_0LB1LE_1LE1RC/README.md) | awaiting review | Quadratic Mess | T97 (2) | - | busycoq PR 67; DeepMind: map |
| [`1RB0LF_1LC0RE_0LD1LC_1LA---_0RB1RA_0LE1LF`](1RB0LF_1LC0RE_0LD1LC_1LA---_0RB1RA_0LE1LF/README.md) | awaiting review | Bell eats counter | T98 (2) | - | busycoq PR 54 |
| [`1RB0LF_1LC0RE_0LD1LC_1LA---_0RB1RA_1LC1LF`](1RB0LF_1LC0RE_0LD1LC_1LA---_0RB1RA_1LC1LF/README.md) | awaiting review | Bell eats counter | T98 (2) | - | busycoq PR 54 |
| [`1RB0RF_1LC1RA_0RD0LC_1LB1RE_---0RA_1RC1RA`](1RB0RF_1LC1RA_0RD0LC_1LB1RE_---0RA_1RC1RA/README.md) | awaiting review | Bell eats counter | T114 (2) | - | busycoq PR 55 |
| [`1RB1RF_0RC0LB_1LD1RE_1LB1RF_---0RF_1RD0RA`](1RB1RF_0RC0LB_1LD1RE_1LB1RF_---0RF_1RD0RA/README.md) | awaiting review | Bell eats counter | T114 (2) | - | busycoq PR 55 |
| [`1RB1LA_1LA1RC_1RD0RB_1LE1LD_---1LF_1RA0LF`](1RB1LA_1LA1RC_1RD0RB_1LE1LD_---1LF_1RA0LF/README.md) | awaiting review | Shift-overflow counter | T117 (2) | - | busycoq PR 43 |
| [`1RB1LC_1LA1RB_1LD0LA_1RE1RD_---1RF_1LB0RF`](1RB1LC_1LA1RB_1LD0LA_1RE1RD_---1RF_1LB0RF/README.md) | awaiting review | Shift-overflow counter | T117 (2) | - | busycoq PR 43 |
| [`1RB---_0RC0RD_1LD1RB_0LE0LC_1RA0LF_1LD1LE`](1RB---_0RC0RD_1LD1RB_0LE0LC_1RA0LF_1LD1LE/README.md) | awaiting review | Cubic Mess | - | - | busycoq PR 60 |
| [`1RB---_1LC1RF_0LE0RD_0RB0LC_1RD0LD_0RC0RA`](1RB---_1LC1RF_0LE0RD_0RB0LC_1RD0LD_0RC0RA/README.md) | awaiting review | Shift-overflow counter | - | - | busycoq PR 44 |
| [`1RB0LA_1LC0RD_0LD1LA_1LF0RE_1LB1RE_1RD---`](1RB0LA_1LC0RD_0LD1LA_1LF0RE_1LB1RE_1RD---/README.md) | awaiting review | Chaotic Ack-like Bell | - | - | busycoq PR 63 |
| [`1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD1RF_1LA---`](1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD1RF_1LA---/README.md) | awaiting review | Shift-overflow counter | - | - | busycoq PR 55 |
| [`1RB0LD_0RC---_0LD0RF_1LE1LD_0LA0RD_0RB1RA`](1RB0LD_0RC---_0LD0RF_1LE1LD_0LA0RD_0RB1RA/README.md) | awaiting review | Bell eats counter | - | - | busycoq PR 54; DeepMind: reduction |
| [`1RB0LE_0RC---_1RD0LA_1RE0RA_0LF1LD_1LC1RF`](1RB0LE_0RC---_1RD0LA_1RE0RA_0LF1LD_1LC1RF/README.md) | awaiting review | Skelet 1-like Class 1 | - | - | busycoq PR 45 |
| [`1RB0LF_1LC0RD_1LA1LC_---0RE_0RB1RA_1LC1LF`](1RB0LF_1LC0RD_1LA1LC_---0RE_0RB1RA_1LC1LF/README.md) | awaiting review | Bell eats counter | - | - | busycoq PR 54 |
| [`1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA`](1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA/README.md) | awaiting review | Cubic Mess | - | - | busycoq PR 60; halts-iff map in Lean; DeepMind: map |
| [`1RB0RB_0LC1RA_1RD1LC_1LA1LE_1LF0LD_---0LA`](1RB0RB_0LC1RA_1RD1LC_1LA1LE_1LF0LD_---0LA/README.md) | awaiting review | Shift-overflow bouncer counter | - | - | busycoq PR 64 |
| [`1RB0RC_1RC---_1LD1RE_1LE0LD_1RA0LF_0RC0RB`](1RB0RC_1RC---_1LD1RE_1LE0LD_1RA0LF_0RC0RB/README.md) | awaiting review | Quadratic Mess | - | - | busycoq PR 55 |
| [`1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC`](1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC/README.md) | awaiting review | Shift-overflow bouncer counter | - | - | busycoq PR 66; DeepMind: acceleration |
| [`1RB1LC_0RC0RB_1LD0LA_1LE---_1LF1RA_1LA1LC`](1RB1LC_0RC0RB_1LD0LA_1LE---_1LF1RA_1LA1LC/README.md) | awaiting review | Shift-overflow counter | - | - | busycoq PR 58 |
| [`1RB1LE_0RC1RA_0LD0RB_1LA1LF_0LC1RF_---0LA`](1RB1LE_0RC1RA_0LD0RB_1LA1LF_0LC1RF_---0LA/README.md) | awaiting review | Shift-overflow counter | - | - | busycoq PR 43 |
| [`1RB1LE_1RC0RB_1LD1RC_1LA1LE_1LF0LA_1LC---`](1RB1LE_1RC0RB_1LD1RC_1LA1LE_1LF0LA_1LC---/README.md) | awaiting review | Shift-overflow counter | - | - | busycoq PR 57 |
| [`1RB1LF_1RC1RB_1RD0RB_0LE0LF_---1LD_0LE1LA`](1RB1LF_1RC1RB_1RD0RB_0LE0LF_---1LD_0LE1LA/README.md) | awaiting review | Chaotic Fractal Others | - | - | busycoq PR 68 |
| [`1RB1RB_0LC0LD_0LE1LD_1LB0RE_1RA0RF_1RD---`](1RB1RB_0LC0LD_0LE1LD_1LB0RE_1RA0RF_1RD---/README.md) | awaiting review | Unknown | - | - | busycoq PR 56 |
| [`1RB1RC_0LC1RE_1RA0LD_1LB0RD_0RF---_0RA0RF`](1RB1RC_0LC1RE_1RA0LD_1LB0RD_0RF---_0RA0RF/README.md) | awaiting review | Unknown | - | - | busycoq PR 46 |

## The rest, by their 13 November family

No technique shared by several of these is in sight; they are listed so that every undecided machine has a place.

### F01 Periodic blocks driven by a bounded engine (rest) (41 machines)

| machine | standing | community class | table set | 13 Nov family | notes |
|---|---|---|---|---|---|
| [`1RB---_1RC1RE_1LD0LE_1RF0LC_0RD0RA_0RB1RD`](1RB---_1RC1RE_1LD0LE_1RF0LC_0RD0RA_0RB1RD/README.md) | open | Bell-like | T13 (4) | F01 |  |
| [`1RB0LD_0RC1RA_1RD1RE_1LA0LE_0RA0RF_1RC---`](1RB0LD_0RC1RA_1RD1RE_1LA0LE_0RA0RF_1RC---/README.md) | open | Bell-like | T13 (4) | F01 |  |
| [`1RB0RE_1LC0RA_0LD1LB_1LA1LE_0LB0LF_1LD---`](1RB0RE_1LC0RA_0LD1LB_1LA1LE_0LB0LF_1LD---/README.md) | open | Bell-like | T13 (4) | F01 |  |
| [`1RB1RE_1LC0LE_1RD0LB_0RA1RC_0RC0RF_1RA---`](1RB1RE_1LC0LE_1RD0LB_0RA1RC_0RC0RF_1RA---/README.md) | open | Bell-like | T13 (4) | F01 |  |
| [`1RB0LE_1RC1RA_1RD0RF_1RE0RA_1LA1LD_1RA---`](1RB0LE_1RC1RA_1RD0RF_1RE0RA_1LA1LD_1RA---/README.md) | open | Unknown | T18 (4) | F01 |  |
| [`1RB0RC_1LC1LA_1RD0LB_1RE1RC_1RA0RF_1RC---`](1RB0RC_1LC1LA_1RD0LB_1RE1RC_1RA0RF_1RC---/README.md) | open | Unknown | T18 (4) | F01 |  |
| [`1RB0RF_1RC0RD_1LD1LB_1RE0LC_1RA1RD_1RD---`](1RB0RF_1RC0RD_1LD1LB_1RE0LC_1RA1RD_1RD---/README.md) | open | Unknown | T18 (4) | F01 |  |
| [`1RB1RE_1LC0RA_1LD1LB_1LE0LF_1LA0LB_1LB---`](1RB1RE_1LC0RA_1LD1LB_1LE0LF_1LA0LB_1LB---/README.md) | open | Unknown | T18 (4) | F01 |  |
| [`1RB0LA_1RC0RE_0LD0RF_1LA1LD_0RA1RE_---0LC`](1RB0LA_1RC0RE_0LD0RF_1LA1LD_0RA1RE_---0LC/README.md) | open | Bell-like | T29 (3) | F01 |  |
| [`1RB0RE_0LC0RF_1LD1LC_1RA0LD_0RD1RE_---0LB`](1RB0RE_0LC0RF_1LD1LC_1RA0LD_0RD1RE_---0LB/README.md) | open | Bell-like | T29 (3) | F01 |  |
| [`1RB1RA_1LC0RB_1LE0LD_0LB1LD_0RA0LF_---0RE`](1RB1RA_1LC0RB_1LE0LD_0LB1LD_0RA0LF_---0RE/README.md) | open | Bell-like | T29 (3) | F01 |  |
| [`1RB0LD_0RC1RA_1RD1RB_1RE1LE_1LF0LA_---1LA`](1RB0LD_0RC1RA_1RD1RB_1RE1LE_1LF0LA_---1LA/README.md) | open | Unknown | T37 (3) | F01 |  |
| [`1RB1LB_1LC0LD_---1LD_1RE0LA_0RF1RD_1RA1RE`](1RB1LB_1LC0LD_---1LD_1RE0LA_0RF1RD_1RA1RE/README.md) | open | Unknown | T37 (3) | F01 |  |
| [`1RB1RF_1RC1LC_1LD0LE_---1LE_1RF0LB_0RA1RE`](1RB1RF_1RC1LC_1LD0LE_---1LE_1RF0LB_0RA1RE/README.md) | open | Unknown | T37 (3) | F01 |  |
| [`1RB0RB_1LC0LF_1RD0LB_1RE1RC_0RA---_1LA1RE`](1RB0RB_1LC0LF_1RD0LB_1RE1RC_0RA---_1LA1RE/README.md) | open | Quadratic Mess | T49 (3) | F01 |  |
| [`1RB0RF_1LC0RA_1LD1LB_0LE---_1LA0LA_1RE1LD`](1RB0RF_1LC0RA_1LD1LB_0LE---_1LA0LA_1RE1LD/README.md) | open | Quadratic Mess | T49 (3) | F01 |  |
| [`1RB1RE_0RC---_1RD0RD_1LE0LF_1RA0LD_1LC1RB`](1RB1RE_0RC---_1RD0RD_1LE0LF_1RA0LD_1LC1RB/README.md) | open | Quadratic Mess | T49 (3) | F01 |  |
| [`1RB---_0RC1RA_1RD1RF_1LE0LF_1RB0LD_0RE0LC`](1RB---_0RC1RA_1RD1RF_1LE0LF_1RB0LD_0RE0LC/README.md) | open | Shift-overflow structural counter | T59 (2) | F01 |  |
| [`1RB1RF_1LC0LF_1RD0LB_0RA1RE_1RD---_0RC0LA`](1RB1RF_1LC0LF_1RD0LB_0RA1RE_1RD---_0RC0LA/README.md) | open | Shift-overflow structural counter | T59 (2) | F01 |  |
| [`1RB0LA_1RC---_1RD1RA_0RE1LC_1LF0RF_1LD0RC`](1RB0LA_1RC---_1RD1RA_0RE1LC_1LF0RF_1LD0RC/README.md) | open | Unknown | T67 (2) | F01 |  |
| [`1RB0LB_1RC0LD_0LA1RD_1LC1LE_1LF0RE_1LD---`](1RB0LB_1RC0LD_0LA1RD_1LC1LE_1LF0RE_1LD---/README.md) | open | Unknown | T67 (2) | F01 |  |
| [`1RB0LC_1LA1RD_1LA1LF_0RE---_1RA1RE_0RB0LA`](1RB0LC_1LA1RD_1LA1LF_0RE---_1RA1RE_0RB0LA/README.md) | open | Unknown | T75 (2) | F01 |  |
| [`1RB1LC_1LA0RE_0LD---_1LB1LD_1RB1RF_0LA0RB`](1RB1LC_1LA0RE_0LD---_1LB1LD_1RB1RF_0LA0RB/README.md) | open | Unknown | T75 (2) | F01 |  |
| [`1RB0LD_0RC0RF_1LD0RB_1LE---_0LA0LB_0LE0RA`](1RB0LD_0RC0RF_1LD0RB_1LE---_0LA0LB_0LE0RA/README.md) | open | Quadratic Mess | T85 (2) | F01 |  |
| [`1RB0LE_1RC---_0RD0RE_1LE0RB_0LA0LF_0RC0LD`](1RB0LE_1RC---_0RD0RE_1LE0RB_0LA0LF_0RC0LD/README.md) | open | Quadratic Mess | T85 (2) | F01 |  |
| [`1RB0LD_0RC1RA_1RD1RF_1LA0LE_0RA0LC_0RA---`](1RB0LD_0RC1RA_1RD1RF_1LA0LE_0RA0LC_0RA---/README.md) | open | Shift-overflow structural counter | T86 (2) | F01 |  |
| [`1RB0RE_1LC0RA_0LD1LB_1LA1LF_0LB0RD_0LB---`](1RB0RE_1LC0RA_0LD1LB_1LA1LF_0LB0RD_0LB---/README.md) | open | Shift-overflow structural counter | T86 (2) | F01 |  |
| [`1RB0LF_1LC0LA_---1RD_1RF1RE_1LF1RD_1LB0RE`](1RB0LF_1LC0LA_---1RD_1RF1RE_1LF1RD_1LB0RE/README.md) | open | Bouncer + Chaotic Edge | T95 (2) | F01 |  |
| [`1RB1RF_1LC0RF_1LE0LD_1RC0LB_---1RA_1LB1RA`](1RB1RF_1LC0RF_1LE0LD_1RC0LB_---1RA_1LB1RA/README.md) | open | Bouncer + Chaotic Edge | T95 (2) | F01 |  |
| [`1RB0RE_1LC0LE_---1LD_1LE1LB_1RA0LF_0RD1LA`](1RB0RE_1LC0LE_---1LD_1LE1LB_1RA0LF_0RD1LA/README.md) | open | Quadratic Mess | T109 (2) | F01 |  |
| [`1RB1RD_1LC0RF_1LD0LB_1RE0RB_---1RA_0LA1RC`](1RB1RD_1LC0RF_1LD0LB_1RE0RB_---1RA_0LA1RC/README.md) | open | Quadratic Mess | T109 (2) | F01 |  |
| [`1RB0RF_1LC0RC_0LD1LC_1RE1LB_1RF---_1LE1RA`](1RB0RF_1LC0RC_0LD1LC_1RE1LB_1RF---_1LE1RA/README.md) | open | Chaotic Ack-like Bell | T113 (2) | F01 |  |
| [`1RB1LC_1LA---_1LD0LA_1RE0LE_0RF1RE_1LB1RD`](1RB1LC_1LA---_1LD0LA_1RE0LE_0RF1RE_1LB1RD/README.md) | open | Chaotic Ack-like Bell | T113 (2) | F01 |  |
| [`1RB1LD_0LC1RC_1RA1RD_1LE0RB_---1LF_0LC0LA`](1RB1LD_0LC1RC_1RA1RD_1LE0RB_---1LF_0LC0LA/README.md) | open | Bell-like | T122 (2) | F01 |  |
| [`1RB1RD_1RC1LD_0LA1RA_1LE0RC_---1LF_0LA0LB`](1RB1RD_1RC1LD_0LA1RA_1LE0RC_---1LF_0LA0LB/README.md) | open | Bell-like | T122 (2) | F01 |  |
| [`1RB1RF_1LC1RD_1RA1LD_1RE0LA_---0RC_0LC1RB`](1RB1RF_1LC1RD_1RA1LD_1RE0LA_---0RC_0LC1RB/README.md) | open | Skelet 1-like Class 1 | T123 (2) | F01 |  |
| [`1RB0RC_1LC0RB_1RE1LD_0LB0LF_---0RA_1LB1LD`](1RB0RC_1LC0RB_1RE1LD_0LB0LF_---0RA_1LB1LD/README.md) | open | Spaghetti | - | F01 |  |
| [`1RB1LC_1LC0RD_0LE1LA_0RF1RA_1LA0LA_---0RB`](1RB1LC_1LC0RD_0LE1LA_0RF1RA_1LA0LA_---0RB/README.md) | open | Quadratic Mess | - | F01 |  |
| [`1RB1LD_0RC1RC_1RD0RE_0LA0LF_0RF---_1RA1LA`](1RB1LD_0RC1RC_1RD0RE_0LA0LF_0RF---_1RA1LA/README.md) | open | Bell-like | - | F01 |  |
| [`1RB1LD_1LC0RC_0RF1RA_0LE1LA_1RC0LA_---0RB`](1RB1LD_1LC0RC_0RF1RA_0LE1LA_1RC0LA_---0RB/README.md) | open | Quadratic Mess | - | F01 |  |
| [`1RB1RE_1RC0LD_1LB---_1RA1LD_1RA0RF_1RE0LC`](1RB1RE_1RC0LD_1LB---_1RA1LD_1RA0RF_1RE0LC/README.md) | open | Bouncer + Chaotic Edge | - | F01 |  |

### F02 Clock-and-word and two-counter shift-overflow counters (rest) (22 machines)

| machine | standing | community class | table set | 13 Nov family | notes |
|---|---|---|---|---|---|
| [`1RB---_0LC0RB_1RA1LD_0RD1LE_1LF0LA_1LB0LE`](1RB---_0LC0RB_1RA1LD_0RD1LE_1LF0LA_1LB0LE/README.md) | open | Shift-overflow counter | T9 (4) | F02 |  |
| [`1RB---_0LC0RB_1RA1LD_1LE1LF_1LB0LF_0RC0LA`](1RB---_0LC0RB_1RA1LD_1LE1LF_1LB0LF_0RC0LA/README.md) | open | Shift-overflow counter | T9 (4) | F02 |  |
| [`1RB1RF_1RC0RF_0RD0LC_1LE1RA_1LC---_0LD0RE`](1RB1RF_1RC0RF_0RD0LC_1LE1RA_1LC---_0LD0RE/README.md) | open | Shift-overflow counter | T9 (4) | F02 |  |
| [`1RB1RF_1RC0RF_0RD0LC_1LE1RA_1LC---_1RB0RE`](1RB1RF_1RC0RF_0RD0LC_1LE1RA_1LC---_1RB0RE/README.md) | open | Shift-overflow counter | T9 (4) | F02 |  |
| [`1RB1RA_1LC1LE_1RA1LD_0LB0LC_1LF0RE_1LB---`](1RB1RA_1LC1LE_1RA1LD_0LB0LC_1LF0RE_1LB---/README.md) | open | Shift-overflow counter | T14 (4) | F02 |  |
| [`1RB---_1RC0LF_1RD1RD_1RE1RA_1LF0RC_1LC1LB`](1RB---_1RC0LF_1RD1RD_1RE1RA_1LF0RC_1LC1LB/README.md) | open | Shift-overflow counter | T62 (2) | F02 |  |
| [`1RB0LA_0RC1RF_0LD1RE_1LA0RB_0RD---_1RA1RD`](1RB0LA_0RC1RF_0LD1RE_1LA0RB_0RD---_1RA1RD/README.md) | open | Shift-overflow counter | T65 (2) | F02 |  |
| [`1RB0LC_1RC0RA_1LD1LA_1RE1LD_---1RF_0RD1RA`](1RB0LC_1RC0RA_1LD1LA_1RE1LD_---1RF_0RD1RA/README.md) | open | Shift-overflow counter | T79 (2) | F02 |  |
| [`1RB0RF_1LC1LF_1RD1LC_---1RE_0RC1RF_1RA0LB`](1RB0RF_1LC1LF_1RD1LC_---1RE_0RC1RF_1RA0LB/README.md) | open | Shift-overflow counter | T79 (2) | F02 |  |
| [`1RB1LB_1RC1LE_1RD0LF_0LA0RD_---1LD_0LD1LF`](1RB1LB_1RC1LE_1RD0LF_0LA0RD_---1LD_0LD1LF/README.md) | open | Shift-overflow counter | T88 (2) | F02 |  |
| [`1RB1LC_1RC0LF_0LD0RC_1RA1LE_---1LA_0LC1LF`](1RB1LC_1RC0LF_0LD0RC_1RA1LE_---1LA_0LC1LF/README.md) | open | Shift-overflow counter | T121 (2) | F02 |  |
| [`1RB1LE_1RC1LD_1RD0LF_0LA0RD_---1LB_0LD1LF`](1RB1LE_1RC1LD_1RD0LF_0LA0RD_---1LB_0LD1LF/README.md) | open | Shift-overflow counter | T121 (2) | F02 |  |
| [`1RB---_1LC1RE_0LD0LC_1RD0RB_1RF0RB_0LF1RA`](1RB---_1LC1RE_0LD0LC_1RD0RB_1RF0RB_0LF1RA/README.md) | open | Shift-overflow counter | - | F02 |  |
| [`1RB0LA_0RC---_1RD0LE_0LC0RE_1RF0RB_1LA1RD`](1RB0LA_0RC---_1RD0LE_0LC0RE_1RF0RB_1LA1RD/README.md) | open | Shift-overflow counter | - | F02 |  |
| [`1RB0LD_0RC---_1LD0RF_0LE0RA_0RA1LF_0LA1LB`](1RB0LD_0RC---_1LD0RF_0LE0RA_0RA1LF_0LA1LB/README.md) | open | Shift-overflow counter | - | F02 | DeepMind: reduction |
| [`1RB0LD_1LC1RE_1LF0RA_1LA1LD_1RC0RE_---1LC`](1RB0LD_1LC1RE_1LF0RA_1LA1LD_1RC0RE_---1LC/README.md) | open | Shift-overflow counter | - | F02 |  |
| [`1RB0LD_1RC0RB_1LA0RD_1LA0RE_1RF---_0LC0LF`](1RB0LD_1RC0RB_1LA0RD_1LA0RE_1RF---_0LC0LF/README.md) | open | Shift-overflow counter | - | F02 |  |
| [`1RB0LE_0LC0RA_1LE0RD_0RB---_0LF0LD_1LA0LF`](1RB0LE_0LC0RA_1LE0RD_0RB---_0LF0LD_1LA0LF/README.md) | open | Shift-overflow counter | - | F02 |  |
| [`1RB0LF_1LC1RC_0RA0LD_0LE1RE_0RF0LC_1RC---`](1RB0LF_1LC1RC_0RA0LD_0LE1RE_0RF0LC_1RC---/README.md) | open | Shift-overflow counter | - | F02 |  |
| [`1RB0RC_1LC1RE_0LE0LD_1LC0LB_0RA0RF_1RA---`](1RB0RC_1LC1RE_0LE0LD_1LC0LB_0RA0RF_1RA---/README.md) | open | Shift-overflow counter | - | F02 |  |
| [`1RB0RD_1LC1RE_0LD1LC_1RA0LA_1RF0RC_---1RA`](1RB0RD_1LC1RE_0LD1LC_1RA0LA_1RF0RC_---1RA/README.md) | open | Shift-overflow counter | - | F02 |  |
| [`1RB0RD_1LC1RE_1LD0LC_0LE0LC_0RA0RF_1RA---`](1RB0RD_1LC1RE_1LD0LC_0LE0LC_0RA0RF_1RA---/README.md) | open | Shift-overflow counter | - | F02 |  |

### F03 Binary counters with markers, epochs and resets (rest) (9 machines)

| machine | standing | community class | table set | 13 Nov family | notes |
|---|---|---|---|---|---|
| [`1RB0RC_1LC0RE_0LD0LB_1RA1LE_1LB1RF_---0RD`](1RB0RC_1LC0RE_0LD0LB_1RA1LE_1LB1RF_---0RD/README.md) | open | Shift-overflow counter | T41 (3) | F03 |  |
| [`1RB1LE_1RC0RD_1LD0RE_0LA0LC_1LC1RF_---0RA`](1RB1LE_1RC0RD_1LD0RE_0LA0LC_1LC1RF_---0RA/README.md) | open | Shift-overflow counter | T41 (3) | F03 |  |
| [`1RB1RD_1LC0RD_1RE0LD_0RE0LF_0LB0RA_0LC---`](1RB1RD_1LC0RD_1RE0LD_0RE0LF_0LB0RA_0LC---/README.md) | open | Shift-overflow counter | T129 (2) | F03 |  |
| [`1RB1RF_1LC0RD_1RE0LD_0RE0LF_0LB0RA_0LC---`](1RB1RF_1LC0RD_1RE0LD_0RE0LF_0LB0RA_0LC---/README.md) | open | Shift-overflow counter | T129 (2) | F03 |  |
| [`1RB1LC_1LA1RD_1LA0LA_1LD0RE_0RF1RB_---0RC`](1RB1LC_1LA1RD_1LA0LA_1LD0RE_0RF1RB_---0RC/README.md) | open | Shift-overflow counter | - | F03 |  |
| [`1RB1LD_1LC0RD_0LA0RB_0LE1LF_1RF0LC_0RB---`](1RB1LD_1LC0RD_0LA0RB_0LE1LF_1RF0LC_0RB---/README.md) | open | Shift-overflow counter | - | F03 |  |
| [`1RB1LD_1RC0RB_1LA1LE_1LC0LA_1LF0RD_0LB---`](1RB1LD_1RC0RB_1LA1LE_1LC0LA_1LF0RD_0LB---/README.md) | open | Shift-overflow counter | - | F03 |  |
| [`1RB1LE_0RC0RB_1RD1RF_1LA0LE_0LD0LB_---0RD`](1RB1LE_0RC0RB_1RD1RF_1LA0LE_0LD0LB_---0RD/README.md) | open | Shift-overflow counter | - | F03 |  |
| [`1RB1LE_1LC0LF_1LA1RD_1LB0RD_0LC0LA_---1RA`](1RB1LE_1LC0LF_1LA1RD_1LB0RD_0LC0LA_---1RA/README.md) | open | Shift-overflow counter | - | F03 |  |

### F06 Other block-list countdown counters (Skelet 1-like) (rest) (22 machines)

| machine | standing | community class | table set | 13 Nov family | notes |
|---|---|---|---|---|---|
| [`1RB0LB_1LC1RE_1LA1LD_0RB1LF_1LA0RC_---1LC`](1RB0LB_1LC1RE_1LA1LD_0RB1LF_1LA0RC_---1LC/README.md) | open | Skelet 1-like Class 1 | T15 (4) | F06 |  |
| [`1RB0LD_1RC1RE_1LA0LD_1LB1LC_0RA1RF_1RA---`](1RB0LD_1RC1RE_1LA0LD_1LB1LC_0RA1RF_1RA---/README.md) | open | Skelet 1-like Class 1 | T16 (4) | F06 |  |
| [`1RB0RE_1LC0RE_1LA1LD_0LB1LF_1RC1RA_1LB---`](1RB0RE_1LC0RE_1LA1LD_0LB1LF_1RC1RA_1LB---/README.md) | open | Skelet 1-like Class 1 | T16 (4) | F06 |  |
| [`1RB1RC_1LC1LE_1RD0RA_1LB0RA_0LD1LF_1LD---`](1RB1RC_1LC1LE_1RD0RA_1LB0RA_0LD1LF_1LD---/README.md) | open | Skelet 1-like Class 1 | T16 (4) | F06 |  |
| [`1RB1RE_1LC0LD_1RA0LD_1LA1LB_0RC1RF_1RC---`](1RB1RE_1LC0LD_1RA0LD_1LA1LB_0RC1RF_1RC---/README.md) | open | Skelet 1-like Class 1 | T16 (4) | F06 |  |
| [`1RB---_1RC0RA_1LD0RB_0LE0LC_1RE1LF_0RD0RB`](1RB---_1RC0RA_1LD0RB_0LE0LC_1RE1LF_0RD0RB/README.md) | open | Chaotic Ack-like Bell | T28 (3) | F06 |  |
| [`1RB0LE_0RC0RA_1LC1RD_0LB0LE_1LA0LF_1LE---`](1RB0LE_0RC0RA_1LC1RD_0LB0LE_1LA0LF_1LE---/README.md) | open | Chaotic Ack-like Bell | T28 (3) | F06 |  |
| [`1RB0RF_1LC0RA_0LD0LB_1RD1LE_0RC0RA_1RA---`](1RB0RF_1LC0RA_0LD0LB_1RD1LE_0RC0RA_1RA---/README.md) | open | Skelet 1-like Class 1 | T28 (3) | F06 |  |
| [`1RB0LD_1RC0RF_0LD0LE_1RF1LC_0LB1LE_0RA---`](1RB0LD_1RC0RF_0LD0LE_1RF1LC_0LB1LE_0RA---/README.md) | open | Skelet 1-like Class 1 | T40 (3) | F06 |  |
| [`1RB0RD_0LC0LF_1RD1LB_0RE---_1RA0LC_0LA1LF`](1RB0RD_0LC0LF_1RD1LB_0RE---_1RA0LC_0LA1LF/README.md) | open | Skelet 1-like Class 1 | T40 (3) | F06 |  |
| [`1RB0RE_0RC1RE_1RD1LE_0LE---_1RA1LF_1RF0LC`](1RB0RE_0RC1RE_1RD1LE_0LE---_1RA1LF_1RF0LC/README.md) | open | Skelet 1-like Class 1 | T52 (3) | F06 | DeepMind: acceleration |
| [`1RB1LC_0LC---_1RE1LD_1RD0LA_1RF0RC_0RA1RC`](1RB1LC_0LC---_1RE1LD_1RD0LA_1RF0RC_0RA1RC/README.md) | open | Skelet 1-like Class 1 | T52 (3) | F06 |  |
| [`1RB1LF_1RC0RA_0RD1RA_1RE1LA_0LA---_1RF0LD`](1RB1LF_1RC0RA_0RD1RA_1RE1LA_0LA---_1RF0LD/README.md) | open | Skelet 1-like Class 1 | T52 (3) | F06 |  |
| [`1RB0LB_1RC0LA_1RD---_0RE1LD_1LF0RF_1LA1RB`](1RB0LB_1RC0LA_1RD---_0RE1LD_1LF0RF_1LA1RB/README.md) | open | Skelet 1-like Class 1 | T72 (2) | F06 |  |
| [`1RB0LB_1RC1LD_1LD0RD_1LE0RC_1LF---_0LA1RF`](1RB0LB_1RC1LD_1LD0RD_1LE0RC_1LF---_0LA1RF/README.md) | open | Skelet 1-like Class 1 | T72 (2) | F06 |  |
| [`1RB0LC_1LC0RE_1LD1LB_1LA1LD_1RF0RA_---1RE`](1RB0LC_1LC0RE_1LD1LB_1LA1LD_1RF0RA_---1RE/README.md) | open | Skelet 1-like Class 1 | T77 (2) | F06 |  |
| [`1RB0LC_1RC0RC_1LD0RB_1LA0LE_1LD1LF_1LD---`](1RB0LC_1RC0RC_1LD0RB_1LA0LE_1LD1LF_1LD---/README.md) | open | Skelet 1-like Class 2 | T80 (2) | F06 |  |
| [`1RB0RE_1LC0RD_1LD0LD_1RA0LC_1RA1RF_1RA---`](1RB0RE_1LC0RD_1LD0LD_1RA0LC_1RA1RF_1RA---/README.md) | open | Skelet 1-like Class 2 | T80 (2) | F06 |  |
| [`1RB0LF_0RC0LC_1LA1LD_1RE1LC_---1RA_0LC0RD`](1RB0LF_0RC0LC_1LA1LD_1RE1LC_---1RA_0LC0RD/README.md) | open | Skelet 1-like Class 1 | T93 (2) | F06 |  |
| [`1RB1RD_1LC0RF_0LA0RA_1LE1RA_---1LB_0RA0LD`](1RB1RD_1LC0RF_0LA0RA_1LE1RA_---1LB_0RA0LD/README.md) | open | Skelet 1-like Class 1 | T93 (2) | F06 |  |
| [`1RB1LA_1RC1RE_1RD0RD_1LA1RC_1RF0LE_1RA---`](1RB1LA_1RC1RE_1RD0RD_1LA1RC_1RF0LE_1RA---/README.md) | open | Shift-overflow structural counter | T120 (2) | F06 |  |
| [`1RB0LD_1LC1RE_1LA1RC_1RA0LC_0RF---_0LD1RB`](1RB0LD_1LC1RE_1LA1RC_1RA0LC_0RF---_0LD1RB/README.md) | open | Skelet 1-like Class 1 | - | F06 |  |

### F07 Chaotic bells over block lists (rest) (27 machines)

| machine | standing | community class | table set | 13 Nov family | notes |
|---|---|---|---|---|---|
| [`1RB---_0RC0LF_1LD0RE_1RC0LB_1RD1RA_1LB0LC`](1RB---_0RC0LF_1LD0RE_1RC0LB_1RD1RA_1LB0LC/README.md) | open | Monotone list | T25 (3) | F07 |  |
| [`1RB0LC_1LA0RD_0RB0LF_1RA1RE_1RC---_1LC0LB`](1RB0LC_1LA0RD_0RB0LF_1RA1RE_1RC---_1LC0LB/README.md) | open | Monotone list | T25 (3) | F07 |  |
| [`1RB0LC_1LA0RD_1LB1LF_0LA0RE_1RD0RA_1LD---`](1RB0LC_1LA0RD_1LB1LF_0LA0RE_1RD0RA_1LD---/README.md) | open | Monotone list | T25 (3) | F07 |  |
| [`1RB---_0RC0RD_1LD0RF_0LE0LC_1RA0LC_1RC0RA`](1RB---_0RC0RD_1LD0RF_0LE0LC_1RA0LC_1RC0RA/README.md) | open | Chaotic Bell Class 2 | T26 (3) | F07 |  |
| [`1RB0LD_1RC---_0RD0RE_1LE0RF_0LA0LD_1RD0RB`](1RB0LD_1RC---_0RD0RE_1LE0RF_0LA0LD_1RD0RB/README.md) | open | Chaotic Bell Class 2 | T26 (3) | F07 |  |
| [`1RB0RE_1LC0RA_0LD0LB_1RE0LB_1RF---_0RB0RC`](1RB0RE_1LC0RA_0LD0LB_1RE0LB_1RF---_0RB0RC/README.md) | open | Chaotic Bell Class 2 | T26 (3) | F07 |  |
| [`1RB0LC_1LA0RD_0LD1LF_0RE0RA_1LB1RE_0LB---`](1RB0LC_1LA0RD_0LD1LF_0RE0RA_1LB1RE_0LB---/README.md) | open | Chaotic Bell Class 3 | T33 (3) | F07 |  |
| [`1RB0LC_1LA0RE_0LD0LB_1RA1LD_0RC1RF_0RA---`](1RB0LC_1LA0RE_0LD0LB_1RA1LD_0RC1RF_0RA---/README.md) | open | Chaotic Bell Class 3 | T33 (3) | F07 |  |
| [`1RB1LA_1RC0LD_1LB0RE_0LA0LC_0RD1RF_0RB---`](1RB1LA_1RC0LD_1LB0RE_0LA0LC_0RD1RF_0RB---/README.md) | open | Chaotic Bell Class 3 | T33 (3) | F07 |  |
| [`1RB0LE_0RC1RA_1RD0RF_0LE1LD_1RA1LC_---0RE`](1RB0LE_0RC1RA_1RD0RF_0LE1LD_1RA1LC_---0RE/README.md) | open | Chaotic Bell Class 1 | T42 (3) | F07 |  |
| [`1RB0RF_0LC1LB_1RD1LA_1RE0LC_0RA1RD_---0RC`](1RB0RF_0LC1LB_1RD1LA_1RE0LC_0RA1RD_---0RC/README.md) | open | Chaotic Bell Class 1 | T42 (3) | F07 |  |
| [`1RB1LD_1RC0LA_0RD1RB_1RE0RF_0LA1LE_---0RA`](1RB1LD_1RC0LA_0RD1RB_1RE0RF_0LA1LE_---0RA/README.md) | open | Chaotic Bell Class 1 | T42 (3) | F07 |  |
| [`1RB0RB_0LC0RA_1LE1LD_0LE---_1LF0LC_1RA1LB`](1RB0RB_0LC0RA_1LE1LD_0LE---_1LF0LC_1RA1LB/README.md) | open | Bell eats counter | T48 (3) | F07 |  |
| [`1RB0RE_1LC1RD_1LD0LD_0RE0LC_1RA1RF_0RA---`](1RB0RE_1LC1RD_1LD0LD_0RE0LC_1RA1RF_0RA---/README.md) | open | Bell eats counter | T48 (3) | F07 |  |
| [`1RB1RF_1RC0RA_1LD1RE_1LE0LE_0RA0LD_0RB---`](1RB1RF_1RC0RA_1LD1RE_1LE0LE_0RA0LD_0RB---/README.md) | open | Bell eats counter | T48 (3) | F07 |  |
| [`1RB---_1LC0LD_1RD0LB_0RF1RE_1RF0RA_0LE0RC`](1RB---_1LC0LD_1RD0LB_0RF1RE_1RF0RA_0LE0RC/README.md) | open | Chaotic Bell Class 2 | T60 (2) | F07 |  |
| [`1RB0LF_0RC1RD_0LD0RA_1RC0RE_1RF---_1LA0LB`](1RB0LF_0RC1RD_0LD0RA_1RC0RE_1RF---_1LA0LB/README.md) | open | Chaotic Bell Class 2 | T60 (2) | F07 |  |
| [`1RB0LA_1LC1RF_---1LD_1RE0LA_1RA0RB_1RE0RF`](1RB0LA_1LC1RF_---1LD_1RE0LA_1RA0RB_1RE0RF/README.md) | open | Bell eats counter | T66 (2) | F07 |  |
| [`1RB0RA_1RC0RD_1RD0LC_1LE1RA_---1LF_1RB0LC`](1RB0RA_1RC0RD_1RD0LC_1LE1RA_---1LF_1RB0LC/README.md) | open | Bell eats counter | T66 (2) | F07 |  |
| [`1RB0LB_0LC0RD_1LA1LB_0RE---_0RF1RD_1RB1RE`](1RB0LB_0LC0RD_1LA1LB_0RE---_0RF1RD_1RB1RE/README.md) | open | Chaotic Ack-like Bell | T68 (2) | F07 |  |
| [`1RB1RC_1LC0RC_0RA0LD_0LE---_0LF1LD_1LC1LE`](1RB1RC_1LC0RC_0RA0LD_0LE---_0LF1LD_1LC1LE/README.md) | open | Chaotic Ack-like Bell | T68 (2) | F07 |  |
| [`1RB0LE_0RC---_1RD0LA_1RE0RA_1LC0LF_0RC1LC`](1RB0LE_0RC---_1RD0LA_1RE0RA_1LC0LF_0RC1LC/README.md) | open | Monotone list | T89 (2) | F07 |  |
| [`1RB0RF_1LC0RD_1LA0LD_1LE0RA_0LB---_0LB1RB`](1RB0RF_1LC0RD_1LA0LD_1LE0RA_0LB---_0LB1RB/README.md) | open | Monotone list | T89 (2) | F07 |  |
| [`1RB0LA_0LC0RD_0RE1LA_0RC1LB_1LE0LF_1RD---`](1RB0LA_0LC0RD_0RE1LA_0RC1LB_1LE0LF_1RD---/README.md) | open | Monotone list | - | F07 |  |
| [`1RB0LF_1LC1RF_---1LD_0LE0LB_0RA0LA_0RA1RB`](1RB0LF_1LC1RF_---1LD_0LE0LB_0RA0LA_0RA1RB/README.md) | open | Chaotic Bell Class 3 | - | F07 |  |
| [`1RB1RA_0LC1RF_0LD1LD_1LE1LC_0RB0RA_---1RE`](1RB1RA_0LC1RF_0LD1LD_1LE1LC_0RB0RA_---1RE/README.md) | open | Chaotic Bell Class 3 | - | F07 |  |
| [`1RB1RF_1LC1LB_1RD1LD_1RE0RA_---0LB_0LF0RC`](1RB1RF_1LC1LB_1RD1LD_1RE0RA_---0LB_0LF0RC/README.md) | open | Chaotic Bell Class 2 | - | F07 |  |

### F08 Counter beside a chaotic edge or wall (rest) (39 machines)

| machine | standing | community class | table set | 13 Nov family | notes |
|---|---|---|---|---|---|
| [`1RB---_1RC1RB_1LD0RB_1LE0LD_0LF0LC_1LA1RA`](1RB---_1RC1RB_1LD0RB_1LE0LD_0LF0LC_1LA1RA/README.md) | open | Structural counter + chaotic edge | T12 (4) | F08 |  |
| [`1RB0LF_1RC0RB_0RD0RA_1RE0LD_1LF---_1LA1LF`](1RB0LF_1RC0RB_0RD0RA_1RE0LD_1LF---_1LA1LF/README.md) | open | Structural counter + chaotic edge | T12 (4) | F08 |  |
| [`1RB0LF_1RC0RB_0RD0RA_1RE1LE_1RF---_1LA1LF`](1RB0LF_1RC0RB_0RD0RA_1RE1LE_1RF---_1LA1LF/README.md) | open | Structural counter + chaotic edge | T12 (4) | F08 |  |
| [`1RB1RA_1LC0RA_1LD0LC_0LE0LB_1LF1RF_1LA---`](1RB1RA_1LC0RA_1LD0LC_0LE0LB_1LF1RF_1LA---/README.md) | open | Structural counter + chaotic edge | T12 (4) | F08 |  |
| [`1RB0RA_1RC0RF_1RD1LE_1RE---_1LF1LE_1RA0LE`](1RB0RA_1RC0RF_1RD1LE_1RE---_1LF1LE_1RA0LE/README.md) | open | Structural counter + chaotic edge | T21 (4) | F08 |  |
| [`1RB0RD_1RC1LE_1LD---_1RF0LE_1LD1LE_1RA0RF`](1RB0RD_1RC1LE_1LD---_1RF0LE_1LD1LE_1RA0RF/README.md) | open | Structural counter + chaotic edge | T21 (4) | F08 |  |
| [`1RB1LC_1RC---_1LD1LC_1RE0LC_1RF0RE_1RA0RD`](1RB1LC_1RC---_1LD1LC_1RE0LC_1RF0RE_1RA0RD/README.md) | open | Structural counter + chaotic edge | T21 (4) | F08 |  |
| [`1RB1LD_1LC---_1RE0LD_1LC1LD_1RF0RE_1RA0RC`](1RB1LD_1LC---_1RE0LD_1LC1LD_1RF0RE_1RA0RC/README.md) | open | Structural counter + chaotic edge | T21 (4) | F08 |  |
| [`1RB---_0RC0LA_1LD0RB_1LE0RF_1LF1LC_1LB0LD`](1RB---_0RC0LA_1LD0RB_1LE0RF_1LF1LC_1LB0LD/README.md) | open | Shift-overflow bouncer counter | T24 (3) | F08 |  |
| [`1RB0LC_1RC1RE_1RD0RA_0LE0RF_1RA0LD_1LD---`](1RB0LC_1RC1RE_1RD0RA_0LE0RF_1RA0LD_1LD---/README.md) | open | Shift-overflow bouncer counter | T24 (3) | F08 |  |
| [`1RB0LE_1RC0LD_1RD1RA_1RE0RB_0LA0RF_1LE---`](1RB0LE_1RC0LD_1RD1RA_1RE0RB_0LA0RF_1LE---/README.md) | open | Shift-overflow bouncer counter | T24 (3) | F08 |  |
| [`1RB0LA_1RC1RA_1RD1RE_1LC---_0RB1LF_1RA0LE`](1RB0LA_1RC1RA_1RD1RE_1LC---_0RB1LF_1RA0LE/README.md) | open | Counter Class 2 | T30 (3) | F08 |  |
| [`1RB0LF_1RC0LB_1RD1RB_1RE1RF_1LA---_0RC1LA`](../bb6-1RB0LF_1RC0LB/README.md) | open | Counter Class 2 | T30 (3) | F08 |  |
| [`1RB1RD_1LC---_1RF0LD_0RE1LC_1RA1RF_1RE0LF`](1RB1RD_1LC---_1RF0LD_0RE1LC_1RA1RF_1RE0LF/README.md) | open | Counter Class 2 | T30 (3) | F08 |  |
| [`1RB0LC_1LC0RE_1RA1LD_1LA1LC_1RF0RA_---0LA`](1RB0LC_1LC0RE_1RA1LD_1LA1LC_1RF0RA_---0LA/README.md) | open | Bouncer + Chaotic Edge | T35 (3) | F08 |  |
| [`1RB0LE_1LC1RD_1LA0RB_1RC1RB_1LF0LC_---0RC`](1RB0LE_1LC1RD_1LA0RB_1RC1RB_1LF0LC_---0RC/README.md) | open | Bouncer + Chaotic Edge | T35 (3) | F08 |  |
| [`1RB1LD_1RC0LA_1LA0RE_1LB1LA_1RF0RB_---0LB`](1RB1LD_1RC0LA_1LA0RE_1LB1LA_1RF0RB_---0LB/README.md) | open | Bouncer + Chaotic Edge | T35 (3) | F08 |  |
| [`1RB0LE_0RC0RA_1LD0LC_1LA0LB_1RA1LF_---0LC`](1RB0LE_0RC0RA_1LD0LC_1LA0LB_1RA1LF_---0LC/README.md) | open | Shift-overflow bouncer counter | T41 (3) | F08 |  |
| [`1RB0RA_0RC0RE_1LD1LF_1LE0LC_1RA0LD_0RA---`](1RB0RA_0RC0RE_1LD1LF_1LE0LC_1RA0LD_0RA---/README.md) | open | Shift-overflow bouncer counter | T100 (2) | F08 |  |
| [`1RB0RE_1LC0RA_1LD0LC_0LE0LB_1RA1RF_0LC---`](1RB0RE_1LC0RA_1LD0LC_0LE0LB_1RA1RF_0LC---/README.md) | open | Shift-overflow bouncer counter | T100 (2) | F08 |  |
| [`1RB0RA_1LC0RD_0LD0LB_1RA0LE_1LF---_0RD1LB`](1RB0RA_1LC0RD_0LD0LB_1RA0LE_1LF---_0RD1LB/README.md) | open | Structural counter + chaotic edge | T102 (2) | F08 |  |
| [`1RB0RC_1RC1RA_1LD0RA_0LE1RA_---1LF_1RB0LF`](1RB0RC_1RC1RA_1LD0RA_0LE1RA_---1LF_1RB0LF/README.md) | open | Bouncer + Chaotic Edge | T106 (2) | F08 |  |
| [`1RB1RD_1LC0RD_0LE1RD_1RA0RB_---1LF_1RA0LF`](1RB1RD_1LC0RD_0LE1RD_1RA0RB_---1LF_1RA0LF/README.md) | open | Bouncer + Chaotic Edge | T106 (2) | F08 |  |
| [`1RB0RD_1LC0RA_1LF1LD_0RE0LC_---1LB_1RB1RC`](1RB0RD_1LC0RA_1LF1LD_0RE0LC_---1LB_1RB1RC/README.md) | open | Shift-overflow bouncer counter | T107 (2) | F08 |  |
| [`1RB1RE_1LC1LA_1RA0LD_1LC0LE_0LF0RA_---1RC`](1RB1RE_1LC1LA_1RA0LD_1LC0LE_0LF0RA_---1RC/README.md) | open | Shift-overflow bouncer counter | T107 (2) | F08 |  |
| [`1RB1RA_0LC0RF_1LD1LC_1RE1LB_---0RA_1RF0RD`](1RB1RA_0LC0RF_1LD1LC_1RE1LB_---0RA_1RF0RD/README.md) | open | Bouncer + Chaotic Edge | T126 (2) | F08 |  |
| [`1RB1RA_1LC1RE_---0LD_1LE1LD_0RA0LF_1LF0LB`](1RB1RA_1LC1RE_---0LD_1LE1LD_0RA0LF_1LF0LB/README.md) | open | Bouncer + Chaotic Edge | T126 (2) | F08 |  |
| [`1RB0LA_1RC---_0LD1RD_0RA0RE_0RF1RC_1LF0LA`](1RB0LA_1RC---_0LD1RD_0RA0RE_0RF1RC_1LF0LA/README.md) | open | Translated Counter | - | F08 |  |
| [`1RB0LA_1RC---_0LD1RD_0RB0RE_0RF0LD_1LF0LA`](1RB0LA_1RC---_0LD1RD_0RB0RE_0RF0LD_1LF0LA/README.md) | open | Translated Counter | - | F08 |  |
| [`1RB0LD_0RC1RA_1LD1RC_1LE0RF_---1LA_1LF0LA`](1RB0LD_0RC1RA_1LD1RC_1LE0RF_---1LA_1LF0LA/README.md) | open | Bouncer + Chaotic Edge | - | F08 |  |
| [`1RB0LD_1RC0RD_1LA0RC_1RE1LB_1LF0LA_---0LE`](1RB0LD_1RC0RD_1LA0RC_1RE1LB_1LF0LA_---0LE/README.md) | open | Bouncer + Chaotic Edge | - | F08 |  |
| [`1RB0LF_1RC1RB_0RD0RC_1LE1LF_1LD---_0LB1LA`](1RB0LF_1RC1RB_0RD0RC_1LE1LF_1LD---_0LB1LA/README.md) | open | Sync bouncer counter | - | F08 |  |
| [`1RB0RA_1LC0RC_1LF0RD_1RA1LE_0LC---_1LD0LA`](1RB0RA_1LC0RC_1LF0RD_1RA1LE_0LC---_1LD0LA/README.md) | open | Structural counter + chaotic edge | - | F08 |  |
| [`1RB0RA_1RC0RF_0RD1LE_0LE---_1LF1LE_1RA0LC`](1RB0RA_1RC0RF_0RD1LE_0LE---_1LF1LE_1RA0LC/README.md) | open | Structural counter + chaotic edge | - | F08 |  |
| [`1RB0RB_1LC1RA_0LE1LD_0RE1LF_---1LA_1LD0LC`](1RB0RB_1LC1RA_0LE1LD_0RE1LF_---1LA_1LD0LC/README.md) | open | Shift-overflow bouncer counter | - | F08 |  |
| [`1RB0RB_1LC1RA_0LF0LD_1LE1RB_1RA1LC_---1LA`](1RB0RB_1LC1RA_0LF0LD_1LE1RB_1RA1LC_---1LA/README.md) | open | Shift-overflow bouncer counter | - | F08 |  |
| [`1RB0RC_1LC0RB_1LD0LD_1RA1LE_---0LF_1LB1LF`](1RB0RC_1LC0RB_1LD0LD_1RA1LE_---0LF_1LB1LF/README.md) | open | Bouncer + Chaotic Edge | - | F08 |  |
| [`1RB1LD_1RC0RC_1LD0RE_0LB0LA_0RF1LA_---1RC`](1RB1LD_1RC0RC_1LD0RE_0LB0LA_0RF1LA_---1RC/README.md) | open | Bouncer + Chaotic Edge | - | F08 |  |
| [`1RB1RF_0RC1RD_1LC1LA_0LE1RE_1RA0RB_---0LC`](1RB1RF_0RC1RD_1LC1LA_0LE1RE_1RA0RB_---0LC/README.md) | open | Translated Counter | - | F08 |  |

### F09 Bouncers over lists of counters (rest) (12 machines)

| machine | standing | community class | table set | 13 Nov family | notes |
|---|---|---|---|---|---|
| [`1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE`](1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE/README.md) | open | Unknown | T61 (2) | F09 |  |
| [`1RB0RA_0LC0RF_0LB1RD_1LE---_1RA0LF_1LE0RC`](1RB0RA_0LC0RF_0LB1RD_1LE---_1RA0LF_1LE0RC/README.md) | open | Unknown | T61 (2) | F09 |  |
| [`1RB0LB_1RC1LC_1LD1RE_---0LA_1LE0RF_1RA0LF`](1RB0LB_1RC1LC_1LD1RE_---0LA_1LE0RF_1RA0LF/README.md) | open | Unknown | T73 (2) | F09 |  |
| [`1RB0LB_1RC1LC_1LD1RE_---0LA_1RE0RF_1RA0LF`](1RB0LB_1RC1LC_1LD1RE_---0LA_1RE0RF_1RA0LF/README.md) | open | Unknown | T73 (2) | F09 |  |
| [`1RB0LC_0RC0RF_1RD0LE_1LA1RA_1LC1RB_0RB---`](1RB0LC_0RC0RF_1RD0LE_1LA1RA_1LC1RB_0RB---/README.md) | open | Unknown | T74 (2) | F09 |  |
| [`1RB1LB_1LC0RE_0LE0LD_0LC---_1LA0RF_1RE1LC`](1RB1LB_1LC0RE_0LE0LD_0LC---_1LA0RF_1RE1LC/README.md) | open | Unknown | T74 (2) | F09 |  |
| [`1RB0LD_1RC1RB_1RD0RA_0LE1LF_---1LA_1LA0LC`](1RB0LD_1RC1RB_1RD0RA_0LE1LF_---1LA_1LA0LC/README.md) | open | Unknown | - | F09 |  |
| [`1RB0RC_1RC1LB_1LD1RA_1LE0LB_---1LF_0LF0LC`](1RB0RC_1RC1LB_1LD1RA_1LE0LB_---1LF_0LF0LC/README.md) | open | Unknown | - | F09 |  |
| [`1RB0RD_1LC0LE_0RA0LB_1RC1RF_1LB1RD_0RC---`](1RB0RD_1LC0LE_0RA0LB_1RC1RF_1LB1RD_0RC---/README.md) | open | Unknown | - | F09 |  |
| [`1RB0RD_1LC1LB_---1LD_1RA0RE_1RD0LF_1LE0LD`](1RB0RD_1LC1LB_---1LD_1RA0RE_1RD0LF_1LE0LD/README.md) | open | Unknown | - | F09 |  |
| [`1RB1RA_1RC0RE_0RD1LE_0LE---_1LF0LC_0RA1LC`](1RB1RA_1RC0RE_0RD1LE_0LE---_1LF0LC_0RA1LC/README.md) | open | Unknown | - | F09 |  |
| [`1RB1RF_1LC0RB_1RD0LC_1LE1RA_0RC1LB_---1RE`](1RB1RF_1LC0RB_1RD0LC_1LE1RA_0RC1LB_---1RE/README.md) | open | Unknown | - | F09 |  |

### F10 Block-splitting 'mess' machines (rest) (39 machines)

| machine | standing | community class | table set | 13 Nov family | notes |
|---|---|---|---|---|---|
| [`1RB0LC_1LC0RE_1LD1LC_1LA1RD_1RF1RB_---0RB`](1RB0LC_1LC0RE_1LD1LC_1LA1RD_1RF1RB_---0RB/README.md) | open | Cubic Mess | T78 (2) | F10 |  |
| [`1RB1RA_1RC1LB_1LD0RA_1LB0LE_1LF1LD_---0LD`](../bb6-1RB1RA_1RC1LB_1LD0RA_1LB0LE/README.md) | open | Cubic Mess | T78 (2) | F10 |  |
| [`1RB0LC_1RC1RA_0LD0LF_0LB0LE_1LA1LD_---0RA`](1RB0LC_1RC1RA_0LD0LF_0LB0LE_1LA1LD_---0RA/README.md) | open | Quadratic Mess | T81 (2) | F10 |  |
| [`1RB1RE_0LC0LF_0LA0LD_1LE1LC_1RA0LB_---0RE`](1RB1RE_0LC0LF_0LA0LD_1LE1LC_1RA0LB_---0RE/README.md) | open | Quadratic Mess | T81 (2) | F10 |  |
| [`1RB0LD_1RC1RE_1LA0RA_1LE1LC_1RF1RC_---1RA`](1RB0LD_1RC1RE_1LA0RA_1LE1LC_1RF1RC_---1RA/README.md) | open | Quadratic Mess | T87 (2) | F10 |  |
| [`1RB1RF_1LC1LF_---1LD_1LE0RA_1RE1LB_1RD0LD`](1RB1RF_1LC1LF_---1LD_1LE0RA_1RE1LB_1RD0LD/README.md) | open | Quadratic Mess | T87 (2) | F10 | DeepMind: acceleration |
| [`1RB0RA_1RC1RD_1LD1LB_0RF1LE_1LE0LC_---1RA`](1RB0RA_1RC1RD_1LD1LB_0RF1LE_1LE0LC_---1RA/README.md) | open | Quadratic Mess | T104 (2) | F10 |  |
| [`1RB1RE_0LC1RF_---1LD_1LE0LD_1LA1LB_1RF0RA`](1RB1RE_0LC1RF_---1LD_1LE0LD_1LA1LB_1RF0RA/README.md) | open | Quadratic Mess | T104 (2) | F10 |  |
| [`1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LD1RE`](../bb6-holdout/README.md) | open | Cubic Mess | T110 (2) | F10 |  |
| [`1RB1RD_1LC0LE_1RA0LB_1RB---_0LF0RC_0RA1LE`](1RB1RD_1LC0LE_1RA0LB_1RB---_0LF0RC_0RA1LE/README.md) | open | Cubic Mess | T110 (2) | F10 |  |
| [`1RB1LA_1LC0RE_---0LD_1LA0LF_1RA1RE_1LA0LB`](1RB1LA_1LC0RE_---0LD_1LA0LF_1RA1RE_1LA0LB/README.md) | open | Cubic Mess | T118 (2) | F10 |  |
| [`1RB1LA_1LC0RE_---0LD_1RE0LF_1RA1RE_1LA0LB`](1RB1LA_1LC0RE_---0LD_1RE0LF_1RA1RE_1LA0LB/README.md) | open | Cubic Mess | T118 (2) | F10 | DeepMind: acceleration |
| [`1RB---_0RC0LD_1LB1RC_0LE0LF_1RD1LE_1RF1RA`](1RB---_0RC0LD_1LB1RC_0LE0LF_1RD1LE_1RF1RA/README.md) | open | Cubic Mess | - | F10 | DeepMind: acceleration |
| [`1RB---_1RC0LD_0LB0RE_1LB1LC_1RD1RF_1RD1RA`](1RB---_1RC0LD_0LB0RE_1LB1LC_1RD1RF_1RD1RA/README.md) | open | Cubic Mess | - | F10 |  |
| [`1RB0LA_0RC---_0RD0RF_1LD0LE_0LA1LE_0RA0LA`](1RB0LA_0RC---_0RD0RF_1LD0LE_0LA1LE_0RA0LA/README.md) | open | Cubic Mess | - | F10 |  |
| [`1RB0LA_0RC---_0RD0RF_1LD0LE_0LA1LE_1RA0RE`](1RB0LA_0RC---_0RD0RF_1LD0LE_0LA1LE_1RA0RE/README.md) | open | Cubic Mess | - | F10 |  |
| [`1RB0LA_0RC0RF_0RD0RA_1LD0LE_0LA1LE_---1LB`](1RB0LA_0RC0RF_0RD0RA_1LD0LE_0LA1LE_---1LB/README.md) | open | Cubic Mess | - | F10 |  |
| [`1RB0LC_1LC0RE_1LD1LC_1LA1RD_---0RF_0LB0RD`](1RB0LC_1LC0RE_1LD1LC_1LA1RD_---0RF_0LB0RD/README.md) | open | Cubic Mess | - | F10 | DeepMind: reduction |
| [`1RB0LC_1RC0RF_1LA0LD_0LE0RA_0RB1LD_0LA---`](1RB0LC_1RC0RF_1LA0LD_0LE0RA_0RB1LD_0LA---/README.md) | open | Cubic Mess | - | F10 |  |
| [`1RB0LD_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF`](1RB0LD_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF/README.md) | open | Cubic Mess | - | F10 | DeepMind: acceleration |
| [`1RB0LE_0RC0RD_1LC0RB_0RE1RD_1LF1LE_0LA---`](1RB0LE_0RC0RD_1LC0RB_0RE1RD_1LF1LE_0LA---/README.md) | open | Cubic Mess | - | F10 |  |
| [`1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_---0RB`](1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_---0RB/README.md) | open | Quadratic Mess | - | F10 | DeepMind: acceleration |
| [`1RB0LF_1LC1RA_0RD1LB_0LA0RE_1RC1RB_---0LD`](1RB0LF_1LC1RA_0RD1LB_0LA0RE_1RC1RB_---0LD/README.md) | open | Quadratic Mess | - | F10 |  |
| [`1RB0RB_1RC0LE_1LD1LA_---0LC_1RF1LE_1RA0RA`](1RB0RB_1RC0LE_1LD1LA_---0LC_1RF1LE_1RA0RA/README.md) | open | Cubic Mess | - | F10 | DeepMind: acceleration |
| [`1RB1LA_1LA0RC_1RD1RC_1LE0RC_---0LF_1LE0LA`](1RB1LA_1LA0RC_1RD1RC_1LE0RC_---0LF_1LE0LA/README.md) | open | Cubic Mess | - | F10 | DeepMind: acceleration |
| [`1RB1LA_1LC0RA_0LF0LD_1RE1LD_1RE0RB_---0LC`](1RB1LA_1LC0RA_0LF0LD_1RE1LD_1RE0RB_---0LC/README.md) | open | Cubic Mess | - | F10 |  |
| [`1RB1LC_1LC0RD_0LE1LA_---1RA_1RF0LA_0RF0RB`](1RB1LC_1LC0RD_0LE1LA_---1RA_1RF0LA_0RF0RB/README.md) | open | Quadratic Mess | - | F10 |  |
| [`1RB1LD_0RC0RF_1LC0LA_0LE1LD_1LA---_0RB0LF`](1RB1LD_0RC0RF_1LC0LA_0LE1LD_1LA---_0RB0LF/README.md) | open | Cubic Mess | - | F10 |  |
| [`1RB1LD_0RC1LE_1RD0LA_1RE0RF_1LF0LC_---1LB`](1RB1LD_0RC1LE_1RD0LA_1RE0RF_1LF0LC_---1LB/README.md) | open | Quadratic Mess | - | F10 |  |
| [`1RB1RA_1LC0RC_---0LD_0LE0RF_1RE0RA_0LF1LB`](1RB1RA_1LC0RC_---0LD_0LE0RF_1RE0RA_0LF1LB/README.md) | open | Cubic Mess | - | F10 | DeepMind: reduction |
| [`1RB1RA_1LC0RC_1RE0LD_0RE0LF_1RA---_1RB1LF`](1RB1RA_1LC0RC_1RE0LD_0RE0LF_1RA---_1RB1LF/README.md) | open | Cubic Mess | - | F10 | DeepMind: reduction |
| [`1RB1RA_1LC1LB_1RE0LD_1RA0LB_---0RF_1RC0RA`](1RB1RA_1LC1LB_1RE0LD_1RA0LB_---0RF_1RC0RA/README.md) | open | Cubic Mess | - | F10 |  |
| [`1RB1RA_1LC1LD_1LD0LB_1RE0RF_---1RD_1RA1RB`](../bb6-1RB1RA_1LC1LD/README.md) | open | Cubic Mess | - | F10 |  |
| [`1RB1RA_1RC---_1RD0LD_1LE1RF_0RA1LD_0RC0LC`](1RB1RA_1RC---_1RD0LD_1LE1RF_0RA1LD_0RC0LC/README.md) | open | Cubic Mess | - | F10 |  |
| [`1RB1RA_1RC1LB_1LD0RA_---0LE_1LC0LF_1RE0LB`](../bb6-1RB1RA_1RC1LB/README.md) | open | Cubic Mess | - | F10 | DeepMind: acceleration |
| [`1RB1RC_1LC0LE_1RD1RC_1LB0RA_---0LF_1RD1LF`](1RB1RC_1LC0LE_1RD1RC_1LB0RA_---0LF_1RD1LF/README.md) | open | Cubic Mess | - | F10 | DeepMind: reduction |
| [`1RB1RD_0RC0RD_0LD1LE_1LC0RB_1LF---_1LA0LE`](1RB1RD_0RC0RD_0LD1LE_1LC0RB_1LF---_1LA0LE/README.md) | open | Cubic Mess | - | F10 |  |
| [`1RB1RF_1LC0LA_---0LD_1LE1RB_0RA0LB_1RE0RE`](1RB1RF_1LC0LA_---0LD_1LE1RB_0RA0LB_1RE0RE/README.md) | open | Quadratic Mess | - | F10 |  |
| [`1RB1RF_1RC0RB_0RD1LF_1LE1RE_1LA---_1RA0LC`](1RB1RF_1RC0RB_0RD1LF_1LE1RE_1LA---_1RA0LC/README.md) | open | Cubic Mess | - | F10 |  |

### F11 Defect gases, particle seas and cellular-automaton zones (rest) (46 machines)

| machine | standing | community class | table set | 13 Nov family | notes |
|---|---|---|---|---|---|
| [`1RB---_0RC1RC_1RD0LE_1RE0RB_1LF0RA_1LC1LF`](1RB---_0RC1RC_1RD0LE_1RE0RB_1LF0RA_1LC1LF/README.md) | open | Unknown | T27 (3) | F11 |  |
| [`1RB0LF_1RC1RB_1LD0RA_1LA0LE_0LC1LC_1LE---`](1RB0LF_1RC1RB_1LD0RA_1LA0LE_0LC1LC_1LE---/README.md) | open | Unknown | T27 (3) | F11 |  |
| [`1RB1RA_1LC0RE_1LE0LD_0LB1LB_1RA0LF_1LD---`](1RB1RA_1LC0RE_1LE0LD_0LB1LB_1RA0LF_1LD---/README.md) | open | Unknown | T27 (3) | F11 |  |
| [`1RB0LD_1RC0RB_1RD1RF_1LE0LD_1RB1LA_---0RE`](1RB0LD_1RC0RB_1RD1RF_1LE0LD_1RB1LA_---0RE/README.md) | open | Unknown | T39 (3) | F11 |  |
| [`1RB0RA_1RC1RF_1LD0LC_1RA1LE_1RA0LC_---0RD`](1RB0RA_1RC1RF_1LD0LC_1RA1LE_1RA0LC_---0RD/README.md) | open | Unknown | T39 (3) | F11 |  |
| [`1RB1RF_1LC0LB_1RE1LD_1RE0LB_1RA0RE_---0RC`](1RB1RF_1LC0LB_1RE1LD_1RE0LB_1RA0RE_---0RC/README.md) | open | Unknown | T39 (3) | F11 |  |
| [`1RB0RE_1LC---_0RA0LD_1LC1LD_1RF0LA_1RC1RE`](1RB0RE_1LC---_0RA0LD_1LC1LD_1RF0LA_1RC1RE/README.md) | open | Unknown | T53 (3) | F11 |  |
| [`1RB1RA_0LC0RA_1LF0LD_1LE0RC_1LB1LD_1RB---`](1RB1RA_0LC0RA_1LF0LD_1LE0RC_1LB1LD_1RB---/README.md) | open | Unknown | T53 (3) | F11 |  |
| [`1RB1RF_0RC0LE_1RD0RF_1LB---_1LB1LE_1RA0LC`](1RB1RF_0RC0LE_1RD0RF_1LB---_1LB1LE_1RA0LC/README.md) | open | Unknown | T53 (3) | F11 |  |
| [`1RB0RF_1LC1RD_1LA1LC_1RA1RE_1RB0RB_---0LC`](1RB0RF_1LC1RD_1LA1LC_1RA1RE_1RB0RB_---0LC/README.md) | open | Spaghetti | T54 (3) | F11 |  |
| [`1RB1RA_1LC0LF_1RA1LD_1LB1LE_1LC0LC_---0RA`](1RB1RA_1LC0LF_1RA1LD_1LB1LE_1LC0LC_---0RA/README.md) | open | Spaghetti | T54 (3) | F11 |  |
| [`1RB1RE_1RC0RF_1LD1RA_1LB1LD_1RC0RC_---0LD`](1RB1RE_1RC0RF_1LD1RA_1LB1LD_1RC0RC_---0LD/README.md) | open | Spaghetti | T54 (3) | F11 |  |
| [`1RB---_0RC0RF_0RD0RA_1RE0LB_1LF0LE_1RC0LE`](1RB---_0RC0RF_0RD0RA_1RE0LB_1LF0LE_1RC0LE/README.md) | open | Unknown | T58 (2) | F11 |  |
| [`1RB0RA_1LC0RA_0LF0LD_1LE---_0LC0LB_1LA0RE`](1RB0RA_1LC0RA_0LF0LD_1LE---_0LC0LB_1LA0RE/README.md) | open | Unknown | T58 (2) | F11 |  |
| [`1RB0LE_1LC0RA_1RD0RC_1LA0LD_1LB0LF_1LC---`](1RB0LE_1LC0RA_1RD0RC_1LA0LD_1LB0LF_1LC---/README.md) | open | Unknown | T90 (2) | F11 |  |
| [`1RB0RF_1RC0LE_1LD0LC_1RE0RD_1LB0RA_1RC---`](1RB0RF_1RC0LE_1LD0LC_1RE0RD_1LB0RA_1RC---/README.md) | open | Unknown | T90 (2) | F11 |  |
| [`1RB0LF_0RC0RB_1LC1LD_1RE0RD_---0RA_1LA0LF`](1RB0LF_0RC0RB_1LC1LD_1RE0RD_---0RA_1LA0LF/README.md) | open | Unknown | T94 (2) | F11 |  |
| [`1RB0RA_1LC0RA_0LD0LC_1RD1RE_1LF0LE_---0LB`](1RB0RA_1LC0RA_0LD0LC_1RD1RE_1LF0LE_---0LB/README.md) | open | Unknown | T94 (2) | F11 |  |
| [`1RB0RA_1LC0RD_0LD0LB_1RA0LE_1LF---_0RA1LB`](1RB0RA_1LC0RD_0LD0LB_1RA0LE_1LF---_0RA1LB/README.md) | open | Unknown | T102 (2) | F11 |  |
| [`1RB0RF_1LC1RD_1LA1LC_1RA1RE_0RB0LD_---0LC`](1RB0RF_1LC1RD_1LA1LC_1RA1RE_0RB0LD_---0LC/README.md) | open | Spaghetti | T115 (2) | F11 |  |
| [`1RB1RA_1LC0LF_1RA1LD_1LB1LE_0LC0RD_---0RA`](1RB1RA_1LC0LF_1RA1LD_1LB1LE_0LC0RD_---0RA/README.md) | open | Spaghetti | T115 (2) | F11 |  |
| [`1RB---_0RC1RD_1LD1LF_1LE0RB_1RF1LD_1LA0LC`](1RB---_0RC1RD_1LD1LF_1LE0RB_1RF1LD_1LA0LC/README.md) | open | Chaotic 1dCA-like in bouncer | - | F11 |  |
| [`1RB---_1LC0RF_1RF0LD_0LE1LC_0RC0LC_1RB0RA`](1RB---_1LC0RF_1RF0LD_0LE1LC_0RC0LC_1RB0RA/README.md) | open | Unknown | - | F11 |  |
| [`1RB0LA_0LC0RA_1LA1LD_1LC0LE_1RF0LF_0RB---`](1RB0LA_0LC0RA_1LA1LD_1LC0LE_1RF0LF_0RB---/README.md) | open | Unknown | - | F11 |  |
| [`1RB0LA_0RC1LF_0RD0LA_1LD0LE_1RB1LF_---1LA`](1RB0LA_0RC1LF_0RD0LA_1LD0LE_1RB1LF_---1LA/README.md) | open | Spaghetti | - | F11 |  |
| [`1RB0LB_1RC1LE_1LD0RF_---1LB_0LA0LC_1LB1RA`](1RB0LB_1RC1LE_1LD0RF_---1LB_0LA0LC_1LB1RA/README.md) | open | Spaghetti | - | F11 |  |
| [`1RB0LC_0LA1RD_1LA0RE_1RE0RF_1LF---_1LB1RF`](1RB0LC_0LA1RD_1LA0RE_1RE0RF_1LF---_1LB1RF/README.md) | open | Spaghetti | - | F11 |  |
| [`1RB0LC_1LC0RF_1LD1RC_1LA0RE_1LB1RD_---0RD`](1RB0LC_1LC0RF_1LD1RC_1LA0RE_1LB1RD_---0RD/README.md) | open | Chaotic 1dCA-like in bouncer | - | F11 |  |
| [`1RB0LC_1RC1RA_0RD1LE_1RE1RF_1LC0RB_---1RD`](1RB0LC_1RC1RA_0RD1LE_1RE1RF_1LC0RB_---1RD/README.md) | open | Unknown | - | F11 |  |
| [`1RB0LD_1LC0RE_---1LD_1LE1LA_1RA0LF_1LC1RE`](1RB0LD_1LC0RE_---1LD_1LE1LA_1RA0LF_1LC1RE/README.md) | open | Spaghetti | - | F11 |  |
| [`1RB0LE_0LC0RF_1LD1LC_1RA0RD_0LA1LA_1RD---`](1RB0LE_0LC0RF_1LD1LC_1RA0RD_0LA1LA_1RD---/README.md) | open | Spaghetti | - | F11 |  |
| [`1RB0LE_0RC0RA_1RD1RB_0LA0RB_1LF---_1LD1LF`](1RB0LE_0RC0RA_1RD1RB_0LA0RB_1LF---_1LD1LF/README.md) | open | Unknown | - | F11 | DeepMind: acceleration |
| [`1RB0LF_0LC1LB_0RD1LA_1RE0RA_---1RD_1RC1LF`](1RB0LF_0LC1LB_0RD1LA_1RE0RA_---1RD_1RC1LF/README.md) | open | Unknown | - | F11 |  |
| [`1RB0RA_1LC0RD_---0LD_1LE1LF_1RA1LB_1RC0LD`](1RB0RA_1LC0RD_---0LD_1LE1LF_1RA1LB_1RC0LD/README.md) | open | Spaghetti | - | F11 |  |
| [`1RB0RC_0LA0RA_0LD0RA_1LE---_0LF1LB_1LA1LD`](1RB0RC_0LA0RA_0LD0RA_1LE---_0LF1LB_1LA1LD/README.md) | open | Chaotic 1dCA-like in bouncer | - | F11 |  |
| [`1RB0RD_0LC1LD_1RA1LA_1RE1LB_---0RF_1RA1RF`](1RB0RD_0LC1LD_1RA1LA_1RE1LB_---0RF_1RA1RF/README.md) | open | Spaghetti | - | F11 |  |
| [`1RB0RE_1RC0RE_1LD1RB_1LA0LA_1RF0LC_---0RC`](1RB0RE_1RC0RE_1LD1RB_1LA0LA_1RF0LC_---0RC/README.md) | open | Spaghetti | - | F11 |  |
| [`1RB0RE_1RC1RE_1LD1LC_0RB0LC_1RF0RB_---1RA`](1RB0RE_1RC1RE_1LD1LC_0RB0LC_1RF0RB_---1RA/README.md) | open | Chaotic 1dCA-like in bouncer | - | F11 | DeepMind: acceleration |
| [`1RB0RF_1RC1RE_0LD---_1LE1LD_1RF0RF_0RA0LB`](1RB0RF_1RC1RE_0LD---_1LE1LD_1RF0RF_0RA0LB/README.md) | open | Spaghetti | - | F11 |  |
| [`1RB1LA_1RC1RD_0LA0LD_1RE1LC_0RF0LF_---0RA`](1RB1LA_1RC1RD_0LA0LD_1RE1LC_0RF0LF_---0RA/README.md) | open | Spaghetti | - | F11 |  |
| [`1RB1LD_0LC0RA_1RA1LC_1RE0LC_---1RF_0RD0RB`](1RB1LD_0LC0RA_1RA1LC_1RE0LC_---1RF_0RD0RB/README.md) | open | Unknown | - | F11 |  |
| [`1RB1LE_0RC0RA_0RD1RF_1LD1LA_0LA0LE_0LB---`](1RB1LE_0RC0RA_0RD1RF_1LD1LA_0LA0LE_0LB---/README.md) | open | Spaghetti | - | F11 |  |
| [`1RB1LE_1RC1RF_0RD0LB_1LD0RA_0LA0LE_0RC---`](1RB1LE_1RC1RF_0RD0LB_1LD0RA_0LA0LE_0RC---/README.md) | open | Unknown | - | F11 |  |
| [`1RB1RD_1LC0LC_0RD0LB_1RF0LE_0RD---_0RA1RC`](1RB1RD_1LC0LC_0RD0LB_1RF0LE_0RD---_0RA1RC/README.md) | open | Chaotic 1dCA-like in bouncer | - | F11 |  |
| [`1RB1RE_1LC0RA_---1LD_1LA0LF_0LB0LC_1RB0LB`](1RB1RE_1LC0RA_---1LD_1LA0LF_0LB0LC_1RB0LB/README.md) | open | Chaotic 1dCA-like in bouncer | - | F11 | DeepMind: acceleration |
| [`1RB1RE_1LC1RC_0RF1LD_1LE0LB_1LB0RA_---1RA`](1RB1RE_1LC1RC_0RF1LD_1LE0LB_1LB0RA_---1RA/README.md) | open | Unknown | - | F11 |  |
