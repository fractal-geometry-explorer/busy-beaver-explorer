# Ranking the undecided holdouts by closeness to a decision (21 November 2026)

All **522** holdouts that are undecided here (open, cryptid, or covered only by an outside proof not yet compiled), ranked by how close each is to being decided and what the next concrete step is, so that new compute and proof work goes to the likeliest wins. Written by [`rank.py`](rank.py) from what the repository records about each machine; machine-readable in [`ranking.json`](ranking.json); sortable page: [`pages/holdouts/ranking.html`](../pages/holdouts/ranking.html). The score is a judgement, not a probability and not a result.

## How the score is made

Each machine is put on one rung of a ladder of *what is left*, which sets the base score, and then gets up to 10 points for work already proved (kernel-checked Lean claims beyond the three every folder starts with, a halts-iff map, a Lean no-halt bound past 10^7 steps) and up to 2 for undecided machines on the same table set (one proof often carries over). Cryptids off the halting route lose 3. The rung comes from the machine's family (`families.json`), the Collatz triage bucket (`tools/collatz/triage.json`), the number-theory tier (`tools/number-theory/ranking.json`) and, for 15 machines, a judgement read from their README after the latest pull requests (`OVERRIDES` in `rank.py`).

| rung | base | machines | meaning |
|---|---:|---:|---|
| Outside proof to compile | 92 | 2 | A complete outside proof exists; only checking it is left. |
| Halt reported elsewhere | 80 | 7 | Another group reports the halting step; a checked proof of it is left. |
| One named gap | 62 | 2 | A Lean reduction covers every case but one or two named ones. |
| Finite or inequality question | 46 | 31 | The macro model is proved; what is left is one invariant or inequality with no number theory in sight. |
| Halt hunt | 36 | 41 | An exact macro simulator exists and halting looks plausible; a long run could find the halt. |
| Model partly proved | 25 | 75 | Part of the macro structure is proved; the rule that decides halting is not. |
| Collatz-type question | 14 | 57 | Halting is reduced to an orbit of an explicit map that behaves like a Collatz problem. |
| Not decoded yet | 10 | 249 | The behaviour is described but its rules are not decoded. |
| Cryptid | 5 | 58 | A community cryptid: an open number-theory problem. |

## Top 10 recommended attacks

Each attack is one piece of work that would settle the machines listed with it. Ordered by the best-ranked machine it settles, then by how many it settles.

1. **Finish compiling busycoq PR 60** (2 machines, halting, compute). Two complete Rocq halting proofs (credited to Yeyito on the bbchallenge wiki). The framework files compile and sample jobs pass; what is left is about 555 core-hours of native_compute jobs, now running in shards. A finished run moves both machines to decided. *Resource:* Core-hours (a large machine would finish it in days).
   - [`1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA`](1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA/README.md)
   - [`1RB---_0RC0RD_1LD1RB_0LE0LC_1RA0LF_1LD1LE`](1RB---_0RC0RD_1LD1RB_0LE0LC_1RA0LF_1LD1LE/README.md)
2. **Prove the reported vampire-family halts** (7 machines, halting, compute). Seven machines on four orbits. Lean already proves each halts iff its orbit of an explicit map reaches a halting context, and Thomas Reus's repository reports the halts at Bell 7.3·10^11 to 2.0·10^12. Left: list the contexts up to the halt (one long orbit.c run per orbit), and a chunked 2-adic check written in Lean with a soundness proof, evaluated by native_decide. *Resource:* One large-memory machine for the orbit runs (the numbers reach 7·10^11 bits) and the Lean evaluation.
   - [`1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LC---`](1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LC---/README.md)
   - [`1RB0RF_1LC---_1RD0LC_0RE0RD_1LF1LC_1LE1RA`](1RB0RF_1LC---_1RD0LC_0RE0RD_1LF1LC_1LE1RA/README.md)
   - [`1RB---_0RC0RB_1LD1LE_1LC1RF_1RB0LE_1RA0RD`](1RB---_0RC0RB_1LD1LE_1LC1RF_1RB0LE_1RA0RD/README.md)
   - [`1RB---_1LC0RB_0LD0LC_1RE1RB_1RD1LF_1LA0LE`](1RB---_1LC0RB_0LD0LC_1RE1RB_1RD1LF_1LA0LE/README.md)
   - [`1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LA---`](1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LA---/README.md)
   - [`1RB0RE_1RC---_0RD0RC_1LE1LF_1LD1RA_1RC0LF`](1RB0RE_1RC---_0RD0RC_1LE1LF_1LD1RA_1RC0LF/README.md)
   - [`1RB0RF_1LC---_1LF1LD_1RE0LD_0RC0RE_1LC1RA`](1RB0RF_1LC---_1LF1LD_1RE0LD_0RC0RE_1LC1RA/README.md)
3. **Close the Pascal machines' last two cases** (5 machines, non-halting, Lean proof). Lean proves a bounce is a row of Pascal's triangle mod 2 and covers every right turn except an even head block meeting a walled zone and the crossing phase. Closing those makes the observed 2-cell-letter invariant a theorem: the two same-start machines never halt, the two mirrored starts follow by porting, and the slowed-down twin needs one more no-break argument.
   - [`1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF`](1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF/README.md)
   - [`1RB0LE_1RC1RB_1RD0RA_0RE---_1LF1LA_1LA1LF`](1RB0LE_1RC1RB_1RD0RA_0RE---_1LF1LA_1LA1LF/README.md)
   - [`1RB1RA_1LC0RF_1LD1LC_1LE0LB_0LF---_1RA1RB`](1RB1RA_1LC0RF_1LD1LC_1LE0LB_0LF---_1RA1RB/README.md)
   - [`1RB0RE_1RC0RC_1LD---_0LB1LE_1RF0LD_1RA1RF`](1RB0RE_1RC0RC_1LD---_0LB1LE_1RF0LD_1RA1RF/README.md)
   - [`1RB1RC_1RC1RB_1LD0RA_1LE1LD_1LF0LC_0LA---`](1RB1RC_1RC1RB_1LD0RA_1LE1LD_1LF0LC_0LA---/README.md)
4. **Rule 102 machine: no danger pattern** (1 machine, non-halting, Lean proof). The round trip, the jump and its clock are in Lean, and so is which gaps can reach the danger pattern: under shielded sweeps the rows of Pascal's triangle mod 2, at the next jump one rest per jump length (mask L). Left: control the words that enter the gap at the wall between jumps, and show no new bulk 10 is born.
   - [`1RB1LB_1LC0RD_0LE1LA_0RF1RA_1LE0LA_---0RB`](1RB1LB_1LC0RD_0LE1LA_0RF1RA_1LE0LA_---0RB/README.md)
5. **Stack invariant for the wall-stack machine** (1 machine, non-halting, Lean proof). Ranked first of the 40 map-reduced machines because no number theory is needed: the stack rules are in Lean, and an invariant that keeps each counter far above the one below would finish it.
   - [`1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC`](1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC/README.md)
6. **Automaton search on the clock-and-word maps (R02)** (15 machines, non-halting, solver search). The clock lemma is in Lean for six tables. Left is one finite-state question per machine: a regular language of words that the word map P keeps and that never triggers the halting rebuild. A SAT search on the word alone is far smaller than the whole-tape search that failed. *Resource:* Solver time (many CPU-hours of SAT, easy to parallelise).
   - [`1RB---_1RC1RF_1LD1RE_1LB1LD_0RB0RC_1RA0LF`](1RB---_1RC1RF_1LD1RE_1LB1LD_0RB0RC_1RA0LF/README.md)
   - [`1RB0LA_1RC---_1RD1RA_1LE1RF_1LC1LE_0RC0RD`](1RB0LA_1RC---_1RD1RA_1LE1RF_1LC1LE_0RC0RD/README.md)
   - [`1RB0RA_1RC0RC_1LD0LE_1RA1LC_1LC0LF_0LC---`](1RB0RA_1RC0RC_1LD0LE_1RA1LC_1LC0LF_0LC---/README.md)
   - [`1RB0RB_1LC0LE_1RD1LB_1RA0RD_1LB0LF_0LB---`](1RB0RB_1LC0LE_1RD1LB_1RA0RD_1LB0LF_0LB---/README.md)
   - [`1RB0LC_1LC0RB_0LE1LD_1LB1LA_0RA1LF_0LA---`](1RB0LC_1LC0RB_0LE1LD_1LB1LA_0RA1LF_0LA---/README.md)
   - [`1RB0RE_1LC1RA_1LD0LC_1LA0LA_1RA0RF_0RA---`](1RB0RE_1LC1RA_1LD0LC_1LA0LA_1RA0RF_0RA---/README.md)
   - [`1RB0RF_1RC0RA_1LD1RB_1LE0LD_1LB0LB_0RB---`](1RB0RF_1RC0RA_1LD1RB_1LE0LD_1LB0LB_0RB---/README.md)
   - [`1RB1RE_1LC1RD_1LA1LC_0RA0RB_1RF0LE_1RA---`](1RB1RE_1LC1RD_1LA1LC_0RA0RB_1RF0LE_1RA---/README.md)
   - [`1RB0LE_0LC0RB_1RD1LD_1RA1LF_0LB1LE_---1LB`](1RB0LE_0LC0RB_1RD1LD_1RA1LF_0LB1LE_---1LB/README.md)
   - [`1RB1LC_1LA1RE_0RD0LA_---1LB_1LD0RF_0RE1RB`](1RB1LC_1LA1RE_0RD0LA_---1LB_1LD0RF_0RE1RB/README.md)
   - [`1RB1RF_1LC0RE_1LE1LD_1RE0LC_1RA1RA_1RD---`](1RB1RF_1LC0RE_1LE1LD_1RE0LC_1RA1RA_1RD---/README.md)
   - [`1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE`](1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/README.md)
   - [`1RB1LD_1LC0RE_1LA1RC_0LC0LA_0RF0RC_---0RB`](1RB1LD_1LC0RE_1LA1RC_0LC0LA_0RF0RC_---0RB/README.md)
   - [`1RB0RE_1LC1RA_1LD0LC_0RE0LA_1RA1RF_0RA---`](1RB0RE_1LC1RA_1LD0LC_0RE0LA_1RA1RF_0RA---/README.md)
   - [`1RB1RF_1RC0RA_1LD1RB_1LE0LD_0RA0LB_0RB---`](1RB1RF_1RC0RA_1LD1RB_1LE0LD_0RA0LB_0RB---/README.md)
7. **Rebuild maps and the wall invariant (R07)** (9 machines, either, Lean proof). Up/down counters and two binary counters with rebuilds. The rebuilds are explicit closed maps (checked, not proved); prove them in Lean and extend the PR 57/58 wall invariant to rebuilds that read only part of the counter. What remains after that is a number-theoretic inequality.
   - [`1RB1LD_1RC0RB_1LA1RC_1LE0LA_1LF---_1LC---`](1RB1LD_1RC0RB_1LA1RC_1LE0LA_1LF---_1LC---/README.md)
   - [`1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RF0LE_1RA---`](1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RF0LE_1RA---/README.md)
   - [`1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RF1RC_1RA---`](1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RF1RC_1RA---/README.md)
   - [`1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB0RF_0RB---`](1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB0RF_0RB---/README.md)
   - [`1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB0RF_1RC---`](1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB0RF_1RC---/README.md)
   - [`1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LB`](1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LB/README.md)
   - [`1RB0RF_1RC1LB_1LD1RE_1LB0LD_1RF0RC_1RA---`](1RB0RF_1RC1LB_1LD1RE_1LB0LD_1RF0RC_1RA---/README.md)
   - [`1RB1LE_1RC0RB_1RD1LF_1LA0LC_1LD0LA_---0RE`](1RB1LE_1RC0RB_1RD1LF_1LA0LC_1LD0LA_---0RE/README.md)
   - [`1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---`](1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---/README.md)
8. **Binary counters with doublers: defects die out** (2 machines, non-halting, Lean proof). A tape with one travelling defect cannot halt. Prove that every defect disappears before the next round (one inequality on irregular digits) and the pair is non-halting.
   - [`1RB0LE_0LC0RA_1LE0RD_0RB---_0LF0LD_1LA0LF`](1RB0LE_0LC0RA_1LE0RD_0RB---_0LF0LD_1LA0LF/README.md)
   - [`1RB0LF_1LC1RC_0RA0LD_0LE1RE_0RF0LC_1RC---`](1RB0LF_1LC1RC_0RA0LD_0LE1RE_0RF0LC_1RC---/README.md)
9. **Halt hunts on the countdown counters (R04, R11)** (22 machines, halting, compute). Base-4 and ternary odometers with countdown timers. Short-timer tapes of this shape are proved to halt, and this kind of family gave half the decisions of the week of 13 November. Exact odometer jumps (the PR 83 / 89 method) to the first top-level overflow; the collapse pair has an exact cycle law already. *Resource:* Long CPU runs, one machine each.
   - [`1RB0RF_1LC1RF_1RA0LD_0LC0RE_1LD---_0RC0RD`](1RB0RF_1LC1RF_1RA0LD_0LC0RE_1LD---_0RC0RD/README.md)
   - [`1RB1LD_1LC0RE_1LA0LD_0LB0LE_0RB0LF_1RE---`](1RB1LD_1LC0RE_1LA0LD_0LB0LE_0RB0LF_1RE---/README.md)
   - [`1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RB---`](1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RB---/README.md)
   - [`1RB1LD_1RC1RE_1LA0RA_1RC0LB_0LA1RF_---1RD`](1RB1LD_1RC1RE_1LA0RA_1RC0LB_0LA1RF_---1RD/README.md)
   - [`1RB1RE_1LC0RC_1RA1LD_1RB0LA_0LC1RF_---1RD`](1RB1RE_1LC0RC_1RA1LD_1RB0LA_0LC1RF_---1RD/README.md)
   - [`1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---`](1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/README.md)
   - [`1RB0LC_1LA0RD_1RA0LA_1RE1RD_1RA1RF_1LC---`](1RB0LC_1LA0RD_1RA0LA_1RE1RD_1RA1RF_1LC---/README.md)
   - [`1RB1LA_0LC0RE_1LD1LB_1RE1LF_1RC0RA_0RC---`](1RB1LA_0LC0RE_1LD1LB_1RE1LF_1RC0RA_0RC---/README.md)
   - [`1RB1LE_1RC1LF_0RD1RD_1LE0RE_0LA0LB_---1LE`](1RB1LE_1RC1LF_0RD1RD_1LE0RE_0LA0LB_---1LE/README.md)
   - [`1RB1LF_1LC1RB_1LF1LD_1LE0RD_1LB---_1LA0LA`](1RB1LF_1LC1RB_1LF1LD_1LE0RD_1LB---_1LA0LA/README.md)
   - [`1RB---_1LC0LC_1RD1LB_1LE1RD_0LA1LF_1LD0RF`](1RB---_1LC0LC_1RD1LB_1LE1RD_0LA1LF_1LD0RF/README.md)
   - [`1RB0LF_1LC0RC_1RA1LD_0RB0LE_1LC0LB_---1LA`](1RB0LF_1LC0RC_1RA1LD_0RB0LE_1LC0LB_---1LA/README.md)
   - [`1RB---_0RC0LA_1LD0RB_1LE0LF_1RC1LF_0LC0LB`](1RB---_0RC0LA_1LD0RB_1LE0LF_1RC1LF_0LC0LB/README.md)
   - [`1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD`](1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD/README.md)
   - [`1RB1LD_1RC1RE_1LA0RA_1RC0LB_0LA1RF_---1RB`](1RB1LD_1RC1RE_1LA0RA_1RC0LB_0LA1RF_---1RB/README.md)
   - [`1RB1LD_1RC1RF_1LA1RD_1RE0LB_---0RA_0LA1RC`](1RB1LD_1RC1RF_1LA1RD_1RE0LB_---0RA_0LA1RC/README.md)
   - [`1RB1LF_0RC1RC_1LD0RD_0LE0LA_1RA0LB_---1LD`](1RB1LF_0RC1RC_1LD0RD_0LE0LA_1RA0LB_---1LD/README.md)
   - [`1RB1LF_1LC1RB_1LE1LD_1LB0RD_1LF---_1LA0LA`](1RB1LF_1LC1RB_1LE1LD_1LB0RD_1LF---_1LA0LA/README.md)
   - [`1RB0RE_1LC1LF_1RA1LD_0LB---_1RF1LE_0LB0RA`](1RB0RE_1LC1LF_1RA1LD_0LB---_1RF1LE_0LB0RA/README.md)
   - [`1RB1LE_0RC---_1RD0LA_1RE0RB_0LA0LF_0LD1LF`](1RB1LE_0RC---_1RD0LA_1RE0RB_0LA0LF_0LD1LF/README.md)
   - [`1RB---_1RC1RF_1LD1RA_1LB0LE_1LF1LF_0RB0LD`](1RB---_1RC1RF_1LD1RA_1LB0LE_1LF1LF_0RB0LD/README.md)
   - [`1RB1RE_1LC0RF_1LA0LD_1LE1LC_0RA0LC_1RA---`](1RB1RE_1LC0RF_1LA0LD_1LE1LC_0RA0LC_1RA---/README.md)
10. **Front speed of the cascade for the four R08 machines** (4 machines, either, new idea). The leftmost-zone reduction and the two-zone cascade are proved in Lean; halting is one explicit cascade of one-bit cells. A bound on the speed of the front (measured: 3.3 cells per doubling) would give huge no-halt bounds; deciding needs a new idea about the old zone once the front reaches it.
   - [`1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA`](1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA/README.md)
   - [`1RB0RB_1LC1RA_1LF0LD_0LE1LD_1RA1LC_---1LA`](1RB0RB_1LC1RA_1LF0LD_0LE1LD_1RA1LC_---1LA/README.md)
   - [`1RB1LD_1RC0RC_1LD1RB_1LF0LE_0LA1LE_---1LB`](1RB1LD_1RC0RC_1LD1RB_1LF0LE_0LA1LE_---1LB/README.md)
   - [`1RB0RB_1RC1RA_0LD1LC_0RA1LE_1LF0LC_---1LA`](1RB0RB_1RC1RA_0LD1LC_0RA1LE_1LF0LC_---1LA/README.md)

## The 40 closest machines

| rank | machine | score | what is left | route | next step |
|---:|---|---:|---|---|---|
| 1 | `1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA` | 99 | Outside proof to compile | halting | Finish the native_compute jobs of busycoq PR 60 for this machine (the framework compiles and sample jobs pass; the two machines need about 555 core-hours together), then record the decision. |
| 2 | `1RB---_0RC0RD_1LD1RB_0LE0LC_1RA0LF_1LD1LE` | 92.0 | Outside proof to compile | halting | Finish the native_compute jobs of busycoq PR 60 for this machine (the framework compiles and sample jobs pass; the two machines need about 555 core-hours together), then record the decision. |
| 3 | `1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LC---` | 86.7 | Halt reported elsewhere | halting | Run bb6-vampire-family/c/orbit.c to the reported halting pass with context counting, regenerate the table, then evaluate a chunked (2-adic) check in Lean with native_decide on a large machine. |
| 4 | `1RB0RF_1LC---_1RD0LC_0RE0RD_1LF1LC_1LE1RA` | 82.8 | Halt reported elsewhere | halting | Run c/orbit.c to the reported halting pass with context counting, extend the table to those contexts, and evaluate a chunked (2-adic) check in Lean; or decode the general context rewrite (it looks like a counter with carries) to drop the table. |
| 5 | `1RB---_0RC0RB_1LD1LE_1LC1RF_1RB0LE_1RA0RD` | 82.0 | Halt reported elsewhere | halting | Run c/orbit.c to the reported halting pass with context counting, extend the table to those contexts, and evaluate a chunked (2-adic) check in Lean; or decode the general context rewrite (it looks like a counter with carries) to drop the table. |
| 6 | `1RB---_1LC0RB_0LD0LC_1RE1RB_1RD1LF_1LA0LE` | 82.0 | Halt reported elsewhere | halting | Run c/orbit.c to the reported halting pass with context counting, extend the table to those contexts, and evaluate a chunked (2-adic) check in Lean; or decode the general context rewrite (it looks like a counter with carries) to drop the table. |
| 7 | `1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LA---` | 82.0 | Halt reported elsewhere | halting | Run c/orbit.c to the reported halting pass with context counting, extend the table to those contexts, and evaluate a chunked (2-adic) check in Lean; or decode the general context rewrite (it looks like a counter with carries) to drop the table. |
| 8 | `1RB0RE_1RC---_0RD0RC_1LE1LF_1LD1RA_1RC0LF` | 82.0 | Halt reported elsewhere | halting | Run c/orbit.c to the reported halting pass with context counting, extend the table to those contexts, and evaluate a chunked (2-adic) check in Lean; or decode the general context rewrite (it looks like a counter with carries) to drop the table. |
| 9 | `1RB0RF_1LC---_1LF1LD_1RE0LD_0RC0RE_1LC1RA` | 82.0 | Halt reported elsewhere | halting | Run c/orbit.c to the reported halting pass with context counting, extend the table to those contexts, and evaluate a chunked (2-adic) check in Lean; or decode the general context rewrite (it looks like a counter with carries) to drop the table. |
| 10 | `1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF` | 70.4 | One named gap | non-halting | Prove the two right-turn cases Lean does not cover yet: an even head block meeting a walled zone, and the crossing phase (the block-lengths-mod-4 summary that the abstraction in py/absz.py lacks). With them the observed 2-cell-letter invariant becomes a theorem and the machine never halts. |
| 11 | `1RB0LE_1RC1RB_1RD0RA_0RE---_1LF1LA_1LA1LF` | 66.4 | One named gap | non-halting | Port Absorb.lean as Pascal.lean was ported, then the same two cases: prove the two right-turn cases Lean does not cover yet: an even head block meeting a walled zone, and the crossing phase (the block-lengths-mod-4 summary that the abstraction in py/absz.py lacks). With them the observed 2-cell-letter invariant becomes a theorem and the machine never halts. |
| 12 | `1RB1LB_1LC0RD_0LE1LA_0RF1RA_1LE0LA_---0RB` | 52.4 | Finite or inequality question | non-halting | Show the run never builds the danger pattern: a gap reaches all y only if it is a row of Pascal's triangle mod 2, so bound which gaps the defect jumps create. |
| 13 | `1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC` | 51.7 | Finite or inequality question | non-halting | Prove an invariant on the stack (each counter far above the one below, e.g. at least 5 times), which with the Lean stack rules gives non-halting. |
| 14 | `1RB---_1RC1RF_1LD1RE_1LB1LD_0RB0RC_1RA0LF` | 51.2 | Finite or inequality question | non-halting | Prove the tick of the second regime (1^N 0 1 0 at the end, the block N growing by 4: the same induction with the left context 1 0 in the mirror) and add it to the accelerated run; then describe what a phase end does to the word, where the halting context B> 1 0 1 would have to appear. |
| 15 | `1RB0LA_1RC---_1RD1RA_1LE1RF_1LC1LE_0RC0RD` | 50.4 | Finite or inequality question | non-halting | Automaton invariant for the word map P alone, plus the clock lemma in Lean. |
| 16 | `1RB0RA_1RC0RC_1LD0LE_1RA1LC_1LC0LF_0LC---` | 50.4 | Finite or inequality question | non-halting | Describe P^(2^k) on the words of the run in closed form (the word holds a counter that P counts down), accelerate a phase end, and read off the map from one phase to the next. |
| 17 | `1RB0RB_1LC0LE_1RD1LB_1RA0RD_1LB0LF_0LB---` | 50.4 | Finite or inequality question | non-halting | Describe P^(2^k) on the words of the run in closed form (the word holds a counter that P counts down), accelerate a phase end, and read off the map from one phase to the next. |
| 18 | `1RB1LD_1RC0RB_1LA1RC_1LE0LA_1LF---_1LC---` | 50.4 | Finite or inequality question | either | Prove the closed rebuild maps; extend the PR 57/58 wall invariant. |
| 19 | `1RB1RA_1LC0RF_1LD1LC_1LE0LB_0LF---_1RA1RB` | 50.4 | Finite or inequality question | non-halting | Port Pascal.lean, Lucas.lean and Absorb.lean with the tape sides exchanged, then close the same two cases as the Pascal machine. |
| 20 | `1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RF0LE_1RA---` | 49.6 | Finite or inequality question | either | Prove the closed rebuild maps; extend the PR 57/58 wall invariant. |
| 21 | `1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RF1RC_1RA---` | 49.6 | Finite or inequality question | either | Prove the closed rebuild maps; extend the PR 57/58 wall invariant. |
| 22 | `1RB0LC_1LC0RB_0LE1LD_1LB1LA_0RA1LF_0LA---` | 49.4 | Finite or inequality question | non-halting | Prove the second-level tick (1^a 0 D>0 1^(3+3j) 0 W, the left context 1^a 0 instead of 0 0 0) the same way and add it to the accelerated run, to follow the run past 1.4·10^13 steps; then describe P in closed form. |
| 23 | `1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB0RF_0RB---` | 49.4 | Finite or inequality question | either | Prove the closed rebuild maps; extend the PR 57/58 wall invariant. |
| 24 | `1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB0RF_1RC---` | 49.4 | Finite or inequality question | either | Prove the closed rebuild maps; extend the PR 57/58 wall invariant. |
| 25 | `1RB0RE_1LC1RA_1LD0LC_1LA0LA_1RA0RF_0RA---` | 48.8 | Finite or inequality question | non-halting | Automaton invariant for the word map P alone, plus the clock lemma in Lean. |
| 26 | `1RB0RE_1RC0RC_1LD---_0LB1LE_1RF0LD_1RA1RF` | 48.8 | Finite or inequality question | non-halting | Once the Pascal machine is proved non-halting, prove that no break comes (the twin's halt F> 0 0 1 1 is not the Pascal machine's). |
| 27 | `1RB0RF_1RC0RA_1LD1RB_1LE0LD_1LB0LB_0RB---` | 48.8 | Finite or inequality question | non-halting | Automaton invariant for the word map P alone, plus the clock lemma in Lean. |
| 28 | `1RB1RE_1LC1RD_1LA1LC_0RA0RB_1RF0LE_1RA---` | 48.8 | Finite or inequality question | non-halting | Automaton invariant for the word map P alone, plus the clock lemma in Lean. |
| 29 | `1RB0LE_0LC0RB_1RD1LD_1RA1LF_0LB1LE_---1LB` | 48.6 | Finite or inequality question | non-halting | Describe P^(2^k) on the words of the run in closed form, accelerate a phase end, and read off the map from one phase to the next. |
| 30 | `1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LB` | 48.4 | Finite or inequality question | either | Prove the closed rebuild maps; extend the PR 57/58 wall invariant. |
| 31 | `1RB1LC_1LA1RE_0RD0LA_---1LB_1LD0RF_0RE1RB` | 48.3 | Finite or inequality question | non-halting | Automaton invariant for the word map P alone, plus the clock lemma in Lean. |
| 32 | `1RB0RF_1RC1LB_1LD1RE_1LB0LD_1RF0RC_1RA---` | 48.0 | Finite or inequality question | either | Prove the closed rebuild maps; extend the PR 57/58 wall invariant. |
| 33 | `1RB1RC_1RC1RB_1LD0RA_1LE1LD_1LF0LC_0LA---` | 48.0 | Finite or inequality question | non-halting | Port Pascal.lean, Lucas.lean and Absorb.lean with the tape sides exchanged, then close the same two cases as the Pascal machine. |
| 34 | `1RB0LE_0LC0RA_1LE0RD_0RB---_0LF0LD_1LA0LF` | 47.6 | Finite or inequality question | non-halting | Prove that every travelling defect disappears before the next round (one inequality on the irregular digits), then the round map in Lean. |
| 35 | `1RB1RF_1LC0RE_1LE1LD_1RE0LC_1RA1RA_1RD---` | 47.0 | Finite or inequality question | non-halting | Automaton invariant for the word map P alone, plus the clock lemma in Lean. |
| 36 | `1RB0LF_1LC1RC_0RA0LD_0LE1RE_0RF0LC_1RC---` | 46.8 | Finite or inequality question | non-halting | Prove that every travelling defect disappears before the next round, as for its variant. |
| 37 | `1RB1LE_1RC0RB_1RD1LF_1LA0LC_1LD0LA_---0RE` | 46.8 | Finite or inequality question | either | Prove the closed rebuild maps; extend the PR 57/58 wall invariant. |
| 38 | `1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE` | 46.4 | Finite or inequality question | non-halting | Describe P^(2^k) on the words of the run in closed form (the word holds a counter that P counts down), accelerate a phase end, and read off the map from one phase to the next. |
| 39 | `1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---` | 46.0 | Finite or inequality question | either | Prove the closed rebuild maps; extend the PR 57/58 wall invariant. |
| 40 | `1RB1LD_1LC0RE_1LA1RC_0LC0LA_0RF0RC_---0RB` | 46.0 | Finite or inequality question | non-halting | Automaton invariant for the word map P alone, plus the clock lemma in Lean. |

The other 482 are in the page and in `ranking.json`.
