# Techniques: group misc (busycoq PRs 92, 97, 103, 105, 106; Alex Havrilla, DeepMind)

All five are single Rocq files that import only `Individual62` (97 also `Longitudinal`), are compiled here with Coq 8.20.1
and use no axioms. 92 and 106 are mostly certificates; 97 and 103 are hand-written invariants; 105 is mixed.

## PR 92: 1RB0RE_1LC0LB_1RD0LB_1RF0LA_1RC---_0RA0LD (nonhalting; 6,362 lines, 6.5 MB, 269 s here)

- Checkpoint `tailTape`: `B` on the last 1 at the right end, tape = `tl Q^K mid P^M 111001`. `P = 1110111010` (block), `Q` is a
  20-cell half-unit (two kinds, `S_Q8`/`S_W5` by a bit `bt`), `mid` is an A/B-word junction, and `tl` is a finite "tail" (engine)
  code stored as a base-4 `N`.
- Macro step `checkTailStep`: one round trip rewrites only the tail end through a lookup of 94,207 suffix rules (`SufBucket`,
  hashed P32768 trees). It gives M+1 and K - borrow + add. The middle is crossed by symbolic sweep lemmas. 7,632 "ways" chain into
  6 tail cycles (`TCEntry`: period `per`, loss `decK`, with `12*decK <= per`), so the potential M + 12K is nondecreasing.
- The cycle is iterated q = (K - minK)/decK times by division with remainder. The exit per remainder r (`TCExit`) is followed by
  block-to-stack conversion rules: 3,652 `SK`, 6,322 `PF` (affine in M, split by M mod 2), 1,566 `FMD` and 100 `NK3A`.
- `InInv`: 3 mid words × TC ids, plus an `NK3` family whose junction carries X copies of Q3. X < 1500 is enumerated; X >= 1500
  is symbolic mod 2. Side condition: M + 12K >= 4500. Stage A runs from c0 into `InInv` symbolically. Everything (tables,
  closure, Stage A) is decided by one `vm_cast_no_check (eq_refl true)` over VLQ-compressed byte strings.
- Generality: works for "engine + stack of units + growing block" epoch counters where the engine is a finite-state transducer on
  a bounded suffix and the epoch transition depends only on (engine, junction, small residue of a count). It needs a linear
  potential that the cycles do not decrease. The heavy part is generating the tables (done in Lean/Python offline), not the Rocq.

## PR 97: 1RB0LE_1RC0LB_1RD0RC_1LA1RC_---1LF_1LB1LD (nonhalting; 1,103 lines, 5 s)

- busycoq `Longitudinal` (segment/side relations `segRLs`, `sideRLs`, `sideLRs`). `Wall m r := sideRLs (hf^m) r (00 *> r)`:
  r answers m consecutive C-in/B-out bounces, then reads 00 r.
- Tiles: `seg_X` (X = 1101 passes a bounce unchanged) and `seg_0X` (0X turns 1 bounce into 2). From them, `wall_cons_even`
  (Wall m r, n >= 2, m+n = 2k gives Wall k (0 X^n r)) and `wall_cons_odd` (k bounces then a C->F exit rewriting 0 -> 101).
- The left boundary is a period-3 counter on `Dr = 1100` blocks (`left_plain_3j`, `left100_3t`).
- `Inv`: `z0 <B X^a r` (a >= 1) or `z0 <B X 0 X^(3q+2) r`, with `Wall (3d-1) r`, d >= 1. The cases split on the parity of a+d and
  of d+q, everything by `lia`. Opening: c0 -> X^2 -> X^4 -> X^7 -> X 0 X^10 (step 746), d = 2. No computation beyond tiles.
- Generality: the strongest idea of the five. It avoids the exact Collatz-like rest map entirely by proving only that the
  right-hand list is a wall of known capacity (a "bounce count" abstraction) and that parities route back into the invariant.
  It needs a list of blocks whose response to repeated bounces composes linearly (capacity halves per block plus the block
  length), a left-end counter of fixed period, and halting only possible when the list is empty or small.

## PR 103: 1RB1LF_0RC0RB_0LD1RB_1LE0LB_0LA1LC_0LB--- (nonhalting; 1,799 lines, 4 s)

- Macro machine `step284` on `Mode{br,br1,dl} × list (nat × Ones) × list RSym`. Left tokens are `0^(a+1) 1^o` (o <= 3); right
  tokens are 01/011/0011. There are 24 clauses, each certified by 2-6 raw steps (`runWinPlus`). The 3 undefined clauses (dl on
  (1,o2), (1,o3), (2,o3)) are the only routes to F1.
- Counter: `encB` bijective base 2 (digit 1 = `1010`, digit 2 = `1000`, LSB nearest the head) with `valB`, `valW`, and
  `valB u + 1 = 2^|u| + valW u`. Carry "calls" `Call1`/`Call0` double across each block `repBlk` (`call0N_repBlk`).
  `call1N_erase_0`: m >= 2^|u| + 2 valW u calls erase a `(0,o1)` defect into a clean `encB v`.
- `Inv284`: 16 constructors `mkBR/mkBR1 (ones m) (blocks k) body` with bounds valB <= c·(m+c')·2^k (fuel >= counter). Proof by
  strong case analysis (`BitDecomp`, 4 leading-run shapes) and `nia`. Opening: 1 + 682 macro steps (`vm_compute`), step 2,210.
- Generality: fits "counter fed by a doubling clock" machines (Shift-overflow counter class, G11/G12) where the danger is a
  defect or junk digit in a counter, and where one can prove that the number of increments per phase exceeds the counter's value.
  It needs exact per-token macro steps (small windows) plus an inequality invariant between counter and fuel.

## PR 105: 1RB1LE_1LC1RE_1LE1LD_1LC0LA_1RF0LA_---0RA (halts; 4,044 lines, 13 s)

- Tape as `enc1 : list nat`, a -> `1^(a+1) 0` (4 = background `111110`, 2 = wall `1110`). Hub = `B` at the right end, state
  `encHub pfx bs` with pfx in {0, 03, 05, 055} and domain lengths bs in binary `N`.
- Stage 1: `stepHub` (proved sound) runs 11,120 hubs in 15 `vm_compute` chunks, about 1.49e33 steps. At H11120 the state is
  055 | 156691, 3931792, 19317108, 19849176, +13 more (up to 1.24e16).
- Stage 2 is analytic: potential `wf`/`W`/`psi` on the uncompressed tail. `mCL_bump_spec`, by nested strong induction on
  (psi M, |M|), bounds the tail damage. `cycle_3_iter 17410` (a0 -= 9, a1 -= 28 per 3 hubs, a2 kept >= 2W + 117n), then
  `hub_055_one`, `hub_052_2`, `cycle_2_iter 382700`, `hub_03_halt` give E>0 at the right end, then F0, at H = 1,211,452
  (far more than 1e80 steps).
- Generality: a template for halting "countdown" machines whose leading counters shrink by constant amounts per hub cycle while
  deeper digits get messy. It needs (a) an exact list stepper to reach a regime, (b) cycle lemmas with constant decrements, and
  (c) a potential that bounds how much the deeper part can lose. That fits Skelet-1-like / 111110-background machines once a hub
  representation is found.

## PR 106: 1RB0LD_0RC0LE_1RD1RA_0RE1RF_1LF0RC_0LA--- (halts; 115,070 lines, 2.7 MB, 383 s)

- Hub `b0 E> 001 0 1 encItems 0101`. Items: `RIsingle a h s0 seg` = (001)^a [01001] (01011)^s0 ..., `RItranspRun`,
  `RIpairRun`, `RIraw`, over 7 tokens; counts in binary `N` (up to 1e47).
- `CertOp` has 14 operators, each with a soundness lemma (`stepCert1_sound`): the 1-hub step, raw-window bridges, normalizers,
  a base-3 odometer (`stepOdoD0`, `stepOdoRelay`), an eater, `stepSlicer12`, `stepWave402` (symbolic front-carry, 6 regimes),
  `stepMirror3752` and `stepMirror162`.
- Certificate: 58 raw steps to cp_0, then 90,940 ops in 20 `vm_compute` parts (about 9.59e11 hubs, about 4.25e47 steps), then
  `runPipeRawHalt` to F1. The last hub shows a-counts in ratio 3 (126,800,055, 42,266,685, 14,088,895, ...).
- Generality: an "accelerated simulator with proved macros" (like busycoq's exact halting certificates, but with nested-counter
  operators). It works for any halter whose run, though astronomically long, is covered by a finite set of parametric macros;
  the operator library is machine-specific. Best reused on same-family F06/F09 "block-list / nested counter" machines.

## Candidates (decision "open")

- `1RB1LC_1LA1RE_0RD0LA_---1LB_1LD0RF_0RE1RB` (G12, Shift-overflow counter): two binary counters fed by one clock, each overflow
  of L adds 2^z to R, and a halt needs a specific sweep end. This is the fuel-versus-counter inequality of PR 103 (same group G12).
- `1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD1RF_1LA---` (G11, Shift-overflow counter): two counters off one engine, junk between digits,
  and it halts only if a carry finds a 1 where it always found a 0. That is PR 103's defect-erasure lemma (`call1N_erase_0`) in another form.
  The same family has siblings `1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD0LC_0RC---`, `1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RB_0RC---` and `1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RC---`.
- `1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC` (Bell-like): N copies of 110 moved across a junction "two in, three out"
  (N -> (3N+c)/2), with parity rewriting a left wall that holds smaller counters. This is the closest analogue of PR 97's two-in/three-out
  blocks plus a wall; try a capacity-style `Wall` invariant instead of the orbit.
- `1RB1RA_1LC0RB_1LD0LB_1RA0LE_---1LF_1LB0LA` (Bell-like): z -> about 3z/2 by z mod 4, with a stack of blocks recording residues.
  This is a PR 97-type list that only needs to stay non-empty or well-formed under parity cases.
- `1RB1RE_1LC0LE_1RD0LB_0RA1RC_0RC0RF_1RA---` (G07, Bell-like): a nested run counter (x10/3 per epoch, mod-3 branching), already
  twelve Lean rules on two stacks and a 200M-case excursion check, but no closed invariant. This is PR 92's recipe: a finite
  (engine, junction, residue) table plus a linear potential, closed by `vm_compute`.
- `1RB---_0RC0RD_1LD0RF_0LE0LC_1RA0LC_1RC0RA` (Chaotic Bell Class 2): a stack of counters at the right end, the top block converted
  per visit, and each pop starts a top about 2.5x larger. Epoch structure as in PR 92 (stack, conversion, growth factor).
- `1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA` (G05, Shift-overflow bouncer counter): a counter zone rewritten by passes from a
  growing block of `111110` words. The background is PR 105's; a hub list stepper plus a potential on the zone could close it (or find a halt).
- `1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_1LD---` (G01, Skelet 1-like Class 1): a base-5 nested block counter with visit rules for every
  depth already in Lean; halting needs a rare F-event. This suits PR 106-style proved odometer operators plus an exact certificate
  run (if it halts), or a PR 103-style invariant (if not).
