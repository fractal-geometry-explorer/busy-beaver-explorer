# t4-variants: the T4 engine (DeepMind PR 93, our T4 retargeting) on four near-T4 holdouts

Thread t4-variants, 19 Nov 2026. Evidence levels as in the brief: proved / computed / observed.

## Normal forms (brute force over renamings and mirroring, `sim/iso.py`)

All four machines are T4 = `1RB1RA_1LC0RD_1LD1LB_1RA0LE_0LB0LF_0RA---` with the D0 detour `1LF` (F0 = 0RA) and a changed E1:

| machine | normal form | start | E1 |
|---|---|---|---|
| 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB0LF | U = `1RB1RA_1LC0RD_1LD1LB_1LF0LE_0LB0LE_0RA---` | A (E/F swapped) | 0LE |
| 1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE0RF | U (same table) | C, mirrored; perm A>D B>E C>A D>B E>F F>C | 0LE |
| 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1LF | V3 = `1RB1RA_1LC0RD_1LD1LB_1LF0LE_0LB1LE_0RA---` | A | 1LE |
| 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE | V4 = `1RB1RA_1LC0RD_1LD1LB_1LF0LE_0LB1RF_0RA---` | A | 1RF |

So machines 1 and 2 are **one table** (U) from two starts.

Common fact (all four): F is entered only by the D0 detour (in V4 also by E1, but E1 is always reached from D1, so F
then reads the 0 that D1 wrote). So the **only way any of them halts** is the detour: D reading 0 with a 1 to its left.
D0 after B1 always has a 0 to its left, so a halt needs `B0, C0, D0` on the tape pattern `1 0 0 [B:0]`, an internal
run of exactly three 0s entered by B from the right.

## Key observation for U (machines 1, 2): U is T3 (PR 93's table) with F merged into E

T3 = `1RB1RA_1LC0RD_1LD1LB_1RA0LE_0LB0LF_0LB---` (PR 93's src_tm). T3's E1 = 0LF and F0 = 0LB; U's E1 = 0LE, E0 = 0LB.
With pS(F) = E these agree on every step except T3's halt F1 (U: E1, keeps erasing left) and D0 (U: detour). So define
W = T3 with F1 := 0LF (no halting transition). Every step of W is a step of U under pS, except D0, which U does in 3 steps
(1LF, 0RA, 1RA) or halts on when the left cell is 1. All of PR 93's macro rules are W-rules unchanged (they never use
F1), so **no engine rule needs restating for U**; only the soundness of "None" changes.

Checked:
- *computed*: none of PR 93's 34 base rules (scans, rule_*, zeroL_*) contains a D0 whose left cell is 1 or the unknown
  left context l (`sim/rules.py`, 272 parameter instances). So U never halts inside a macro rule; the engine sees every
  possible halt in a raw step (it is complete for halting, not only sound).
- *proved (Coq 8.20.1, run_ok admitted)*: `proof/mkU.py` turns PR 93's file into a proof skeleton for either machine:
  src_tm := W, `HaltsU c := halts U (pS c)` replaces `halts src_tm`, rawStep returns None on D0 with left cell 1
  (lemma `haltsU_D0`), `det_step : c -[W]-> c' -> HaltsU c' -> HaltsU c` (the PR 109 detour lemma made step-local),
  `perm_U`/`haltsU_iso` to the holdout. With `run_ok` admitted both files compile in about 65 s and Print Assumptions
  shows only run_ok. A halt of the engine run would make them complete proofs (only the vm_compute remains).
- *computed*: the extracted W engine (`engine/`, exactly the Coq definitions of the proof file) agrees with direct
  simulation of U through 3·10^9 steps from both starts (`validateW`, 1087 / 998 fast steps).
- *computed*: the unpatched PR 93 engine reproduces PR 93's halt (T3 from C stops at fast step 2,452,241, 2^1400
  cells), and **T3 from A halts quickly**: fast step 4,452, tape about 2^41 cells (not a holdout; PR 93 engine).

Result of running the W engine (the U accelerator) from both starts: **no halt**. Machine 1 (start A) passes T3's halting
configuration at fast step 4,452 and continues; machine 2 (start C) passes T3's halt (PR 93's) near fast step 2.45M and
continues. Last counts: see "Runs" below. In the first 10^6 fast steps from A there were 2 T3-halt events (W's F1: E
erases a few 1s and leaves a short 0 run that the engine re-absorbs) and only 1 raw D0 entered from C0, none with a 1 on
the left. Direct simulation (3·10^9 steps each) never produced an internal `00` to the left of a B reading 0 (only at the
left blank end). So halting needs a rare defect; the runs give no sign of it. Evidence level: computed (no halt up to
the stated engine step), *not* a non-halting proof (the method cannot give one).

## V3 (machine 3, E1 = 1LE)

Breaks exactly the four T3 rules through E1 (same set as T4; `sim/cmp.py`). Restated forms, checked by direct
simulation on 532 instances (parameters 0..24, random right tails of D words; `sim/v3rules.py`), *computed*:

| T3 rule | T3 result | V3 result |
|---|---|---|
| collision `CfgL (l <* 001101) (D n r)` | `CfgJ l (1111 D n r)` = `CfgJ l (11 D(n+1) r)` | `CfgJ l (D(n+1) 10 r)` (needs r to start with a D word) |
| collide `CfgR l (10 D0 D0 r)` | `CfgJ l (D2 10 r)` | `CfgJ l (D1 10 10 r)` |
| finishP `CfgL (l <* S0 <* 01 <* (10)^(1+b)) r` | `CfgJ l (D(1+b) r)` | `CfgJ l (D b 10 r)` |
| defect0 `CfgR l (10 D0 1 (11)^m 0 r)` | `CfgJ l (1111 D m 1 r)` | `CfgJ l (D(1+m) 10 1 r)` |

Uniformly: T3's carry `11 · D k` (= D(k+1)) becomes `D k · 10`. Unlike T3 -> T4 (carry moved to the next digit, still a
pure digit list), this inserts `10` defects between digits: the collision call becomes
`D j 10 D0 D0 r -> D(1+j) D1 10 10 r`, and the next round then meets `(10)^2 D0` (rule_paired), so PR 93's batched
collision chain (calls_collision: 2k D0 -> D3^(k-1) D2 plus a carry; `doCallsD`, digit lists d_front/d_back) does not
apply. Patching the engine would mean a new macro analysis of this counter (new batched rules for `10`-separated
digits), not a substitution like patch.py. Not done.

## V4 (machine 4, E1 = 1RF)

Same four rules break, but their V4 forms are not local: the collision, finishP and defect0 runs turn right and run into
the right context (they end in state D, A or B on the far side of the next one or two digits, with the outcome depending
on those digits; `sim/four.py` and the table in this thread's log). No restatement of the CfgJ/CfgL kind exists; the
technique does not transfer without a new analysis. Not attempted further.

## Runs

See the end of this file (updated when the runs were stopped).

## Files

- `engine/`: `mkeng.py`/`build1.sh` (PR 93 definitions with a chosen raw table), `mkeng2.py`/`buildW.sh` (engine
  extracted from the U proof file itself), `validateW.ml` (validate with F identified with E), `run.ml` (saves a final
  checkpoint). Build: busycoq BB6 branch, Coq 8.20.1 and OCaml 4.14 from nix (`nix build nixpkgs#coq_8_20`).
- `proof/mkU.py PR93.v OUT.v MACHINE START K [fast]`: writes the Coq proof for machine 1 (`... A K`) or 2 (`... C K`).
- `sim/`: iso.py (normal forms), rules.py (no hidden detour halts in base rules), cmp.py / four.py / v3rules.py (which
  rules break and their V3/V4 forms), near.c (near-halt counter), c0.c, cnt.c, run.c, tr.py.

### Runs (stopped 19 Nov, after about 3.1 h of engine time each, 4-core container)

| machine | engine | last fast step | tape | halt? |
|---|---|---|---|---|
| 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB0LF (U from A) | W (proof-file engine) | 10,968,362 | about 2^3532 cells | no |
| 1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE0RF (U from C) | W | 15,364,760 | about 2^3676 cells | no |
| (reference) T3 from C = PR 93 | PR 93 engine | 2,452,241 | 2^1400 | halts (reproduced) |
| (reference) T3 from A | PR 93 engine | 4,452 | 2^41 | halts |

For comparison the T4 halts came at 2^2410 (start B), 2^3562 (A), 2^4360 (C). Checkpoints (OCaml Marshal of
(FastState, step), for `run`/`peek` built by `engine/buildW.sh`) are in `runs/` (saved at fast steps 10,642,446 and
14,116,972); `run A|C N runs/ck...` resumes. Run with `ulimit -s unlimited`.

## What would come next

- U: keep running the W engine (resume from runs/); if it ever stops, `proof/mkU.py ... A|C K` with 2^K above the stop
  step gives the complete Coq proof (only `run_ok` by vm_compute remains; at 10^7 steps with 2^3500-cell numbers that
  would be many hours of Coq time). A halt needs the rare pattern `1 0 0 [B:0]`; no sign of one so far.
- V3: a new macro analysis of the `D k 10` carry (batched rules for 10-separated digits), then an engine.
- V4: new rules that look ahead into the right tape at each E1 event; the PR 93 engine structure does not cover it.
