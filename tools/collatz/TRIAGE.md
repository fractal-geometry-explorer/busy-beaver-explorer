# Triage of the Collatz-like holdouts (family R15)

The 98 machines of family R15 in [`holdouts/FAMILIES.md`](../../holdouts/FAMILIES.md): runs that are, provably or apparently, the orbit of an explicit Collatz-like map. Each is sorted by its most useful next step. The records are read from each machine's `status.json` and `README.md` (`triage.json`); the sort is a judgement, not a result. Interactive version, with a map runner: [`pages/holdouts/collatz-family.html`](../../pages/holdouts/collatz-family.html). Written by `build.py`; edit `triage.json` or `hunts.json` and rebuild.

| bucket | machines | meaning |
|---|---|---|
| Halt hunt | 13 | The map is fixed (proved, or checked against the machine) and a halt, if there is one, might come early enough to compute. Run it far. |
| Outside proof | 2 | A busycoq pull request claims a decision. Compile it. |
| Prove the map | 8 | The map is explicit but not yet a Lean halts-iff. Proof engineering would make the question exactly a question about the map. |
| Decode | 29 | The round or phase map is not closed yet and has to be read off the machine first. |
| Number theory | 46 | Lean already reduces halting to the map. What is left is a Collatz-type question about one orbit, beyond current methods; only a lucky halt hunt could change that. |

## Halt hunts run for this triage

| machine | what was run | before | now |
|---|---|---|---|
| `1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LC---` | the E-pass map, 2-adic divide and conquer (holdouts/.../c/orbit.c), 2^33 passes | 2^32 passes (4.3e9); a halt then had probability 0.4% under the fair-bit model | 2^33 passes (8.6e9), no halt; 36 minutes, about 7.5 GB (memory caps this run; a halt is expected near 2^40 under the fair-bit model) |
| `1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC` | the A(a, b) rules (tools/collatz/c/amap.c), 10^12 visits | 10^8 Lean frames (685 visits checked against the run) | 10^12 visits, no halt; a, b reach 3.5e12, about 6.8e35 machine steps; values grow about linearly, so a hit b = a + 4 (a even) stays possible |
| `1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RC---` | DeepMind's map C(m, k, b) (tools/collatz/c/dm9516.c), 10^12 accelerated steps | 120 map steps | 10^12 accelerated steps (more than 10^18 steps of the map, which counts the chain rule one cell at a time), no halt; m, k, b reach 10^12, growing about linearly |
| `1RB1LF_1RC1RF_0LD1RE_---1LC_0RB1RE_1LA0LE` | the doubling map (holdouts/.../c/fast.c), 10^12 operations | 10^11 operations (modulus about 5e10); the next targets are moduli 2^37 - 36 and 2^38 - 37 | 10^12 operations, no halt: modulus about 4.8e11, past both targets 2^37 - 36 and 2^38 - 37; 36 odd events |

## Halt hunt (13)

The map is fixed (proved, or checked against the machine) and a halt, if there is one, might come early enough to compute. Run it far.

### [`1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LC---`](../../holdouts/1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LC---/README.md)

*reduced, outlook halts-late, table set T4*

- **Map:** E-event (c, n) = c E> 1^n with context word c: the pass gives c C> 1^(3k+2) (k = ceil(n/2) even) or c 1 C> 1^(3k+2) (k odd), then a context rewrite c C> 1^m -> c' E> 1^(m+a); so n -> (3n+d)/2 with c -> c' decided by c and n mod 4 (110 rules over 55 contexts, binary-counter-like).
- **Halts when:** Halts if the orbit reaches context 11111 or 1111011 with ceil(n/2) odd; never halts if it stays in the proved table forever (leaving the table is not covered).
- **From blank tape:** (c = 1, n = 19) at step 153
- **Proved:** nextE_sound (lean/Orbit.lean), pass0-pass3 (lean/Pass.lean), tbl_sound (lean/Ctx.lean), halts_of_orbit and not_halts_of_forall (kernel): halting criterion both ways for the 55 tabled contexts.
- **Checked:** 10,000 passes kernel (10^1700 steps); 2^18 passes native_decide (10^45000 steps; 2^22 also checked outside check.sh); 2^32 = 4.3e9 passes C/GMP (c/orbit.c, n with 2.5e9 bits).
- **Odds:** absorption rate 8.87e-13 per pass; halt expected after ~1.1e12 passes (~10^(7*10^10) steps); 0.4% chance it would have halted in the 4.3e9 passes checked
- **Next step:** Extend c/orbit.c (divide and conquer on low bits of n) toward 10^11-10^12 passes, the only route to finding the expected halt.

### [`1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RC---`](../../holdouts/1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RC---/README.md)

*reduced, outlook unclear, table set T190*

- **Map:** Only via DeepMind's cited map on C(m,k,b) = 0^inf 1^m (10)^k C> 1^b 0^inf: (m,k,0)->(m+1,0,2k+2); (0,k,1)->(2k+3,0,2); (0,k,b+2)->(2k+2,1,b); (1,0,b+1)->(0,0,b+3); (1,k+1,1)->(2k+7,0,2); (1,k+1,b+2)->(2k+6,1,b); (2,0,1)->(0,1,0); (2,1,b+1)->(0,1,b+1); (2,k+2,1)->(2k+7,0,2); (2,k+2,b+2)->(2k+6,1,b); (m+3,k,b+1)->(m,k+2,b). Repo's own decoding: two-part shape only.
- **Halts when:** DeepMind map reaches none: state C(2,0,b) with b >= 2 (machine-level: E>1 1, E reading a 1 with a 1 to its right).
- **From blank tape:** C(0,0,2) (DeepMind start; step not stated)
- **Proved:** Repo Lean: only step_none_iff and 10^7 steps (lean/Blank.lean); halts-iff is deepmind_halts_iff in lean/DeepMindMap.lean, a cited axiom (DeepMind's theorem compiled here, translation unchecked).
- **Checked:** 7.07e14 steps Quick_Sim and 10^9 steps C (trusted); 10^7 steps native_decide; DeepMind map run only 120 steps here (to compare with theirs).
- **Odds:** not stated (width grows like t^(1/3), no heuristic for a halt)
- **Next step:** Iterate the DeepMind map with big integers far beyond 120 steps and prove it on the repo's definitions (as done for 1RB1RD_1LC0RD_1RF1RB_1LE0RA_0LB0LE_---0RC).

### [`1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD`](../../holdouts/1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD/README.md)

*reduced, outlook unclear, table set T222*

- **Map:** Frame map next on 8 tape shapes (alternating block and solid block trading lengths, e.g. (806,336) -> (672,604) -> (540,874) -> (722,513)), 78 cases in lean/Phases.lean; not stated as closed formulas in the summary.
- **Halts when:** Halts iff an iterate of next from Ph.z 0 0 2 is undefined: .z 1 1 1, .w l 0 1, .w l 1 0, .W l 0 1, .W l 1 0.
- **From blank tape:** Ph.z 0 0 2 at step 2
- **Proved:** halts_iff and next_sound in lean/Phases.lean (kernel), none_halts for the undefined cases.
- **Checked:** 10^8 frames native_decide (~4.5e11 steps); 3.58e22 steps rleaccel C++.
- **Odds:** not stated
- **Next step:** Derive a closed-form (z/w/W) frame map from the 78 cases and a heuristic for how often block sizes reach the small undefined cases; iterate it far beyond 10^8 frames.

### [`1RB0RE_0LC1LE_0RD1LD_1RA1LF_1LC0RA_0LB---`](../../holdouts/1RB0RE_0LC1LE_0RD1LD_1RA1LF_1LC0RA_0LB---/README.md)

*map-partial, outlook unclear, table set T231*

- **Map:** Phase starts PS(D,Z) = D 0^Z 1 0 0 E>: Z -> (3Z + c)/2 with c and next word D' depending only on D and Z mod 4 (extrapolated). Counter D(a,b) = 0 1 0^a 1 0 1 (001)^b: Z=1 (mod 4) leaves D, Z=3 gives D(a-1,b+1); at a=0, Z=3 resets to D(3b+4,0) if Z=3 (mod 8), else leaves the family (nested levels).
- **Halts when:** The residues along the real orbit build a halting word D (e.g. 0 1 0 0 1 1 1 0 1 with Z = 3 mod 4); 7,145 halting (word, residue) pairs reachable with free residues; nearest halting class 6 rounds away (remainders 3 2 3 2 3^2).
- **From blank tape:** 16 phase starts checked from blank to step 8.7e7; counter resets at phases 5, 29, 92, 332, leaves family at phase 1001 (Z 178 digits)
- **Proved:** Sweeps of a phase only (sweep, wall_left in lean/Rules.lean; sweeps in lean/Sweeps.lean, kernel); no halts_iff.
- **Checked:** 1,500 phases of extrapolated phase map (far past 10^350 steps, trusted); 2,930 class-map rounds (~10^520 steps, heuristic); 3.50e139210 steps region-memo accelerator (trusted).
- **Odds:** not stated; halting words exist but the real orbit has not produced one
- **Next step:** Iterate the phase/class map much further with exact integers and prove the phase ends for D(a,b) in Lean, then describe the nested second level.

### [`1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC`](../../holdouts/1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC/README.md)

*reduced, outlook unclear, table set T258*

- **Map:** A(a,b) = 0^inf 1^a 0 C> 1^b 0^inf: a even, b>=a+3: (2a+4, b-a-1); a odd, b>=a+4: (2a+3, b-a); a odd, b=a+3: (2a+1, 9); b=a+2 (a>=2): (1, 2a+7); b=a+1 (a>=3): (4, 2a+4); a>=b>=4: (a-b+1, 2b+3); b=2 (a>=4): (a-3, 7); b=3: halt. (Lean proves the finer 6-frame map next, 30 cases.)
- **Halts when:** Halts iff the orbit from A(2,9) reaches some A(a,3) (a>=2); in Lean: iff iterating next from Ph.e 1 0 reaches .b l j 2, .d l 0 1 or .d l 1 0.
- **From blank tape:** A(2,9) at step 52 (Lean: Ph.e 1 0 after 1 step)
- **Proved:** halts_iff, next_sound, none_halts in lean/Phases.lean (kernel); the A(a,b) rules themselves are checked by py/rules.py, not stated in Lean.
- **Checked:** 10^8 frames native_decide (~5.95x10^11 steps); macro sim 10^15 steps; rleaccel 2.65x10^22 steps trusted.
- **Odds:** not stated
- **Next step:** Iterate the A(a,b) rules much further and look for an invariant excluding b = 3 (a quick 3x10^6-visit run done during this triage, not in the files, reached only ~22-bit values with no halt).

### [`1RB1LF_1RC1RF_0LD1RE_---1LC_0RB1RE_1LA0LE`](../../holdouts/1RB1LF_1RC1RF_0LD1RE_---1LC_0RB1RE_1LA0LE/README.md)

*reduced, outlook probviously-nonhalting, table set T125*

- **Map:** Right-end visits T(c,a,b) = [1^2 0 (10)^c] 1^a 0 (10)^b B> 0; doubling map op on even states (c,u,v), u = b+2, v = a/2+b+3: 2u < v -> (2u, v+1); 2u > v -> (2u-v, v); 2u=v -> odd pool (c, 2v-3, 0). Odd pools A = 2i+3 double down, then leave a bracket or merge (explicit cases, e.g. b = i+r, no bracket, r>=3 -> bracket A+1, restart (r-2, r)).
- **Halts when:** Halts iff the orbit reaches an odd pool without bracket A = 2^(k+2) - 2k - 3 (e.g. from 2u = v at v = 2^(k+1) - k, no bracket), i.e. T(none, 1, b).
- **From blank tape:** T(none, 2, 0) at step 7; op from (none, 2, 4)
- **Proved:** halts_iff / halts_iff_T1 in lean/Map.lean and halts_iff_pool in lean/Doubling.lean (kernel), both layers.
- **Checked:** 10^11 map operations in C (5x10^10 visits, ~10^31 steps, 35 odd pools, 18 without bracket, closest 989 vs 1005); 10^4 nodes native_decide, 100 kernel.
- **Odds:** ~10^-11 in total for the targets still ahead (k >= 36)
- **Next step:** Run the C map on past v ~ 2^37 (5x10^10 reached) to clear the next targets k = 36, 37; otherwise pure number theory.

### [`1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE`](../../holdouts/1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE/README.md)

*reduced, outlook unclear, table set T325*

- **Map:** Frame map next on 11 tape shapes (Ph.e, E, f, g, h, i, k, K, ...), 66 cases (in lean/Phases.lean; formulas not restated in status/README): a solid block of p ones at the right becomes about p/2 copies of 10 at the left, then the alternating block about doubles at the solid block's expense.
- **Halts when:** Orbit reaches a frame where next is undefined: .e l 0 0, .E l 0 0, .f 0 1, .h l 0 1, .i l 0 1, .k l 0, .K l 0 (machine: D reads 0).
- **From blank tape:** Ph.g 0 1 at step 6
- **Proved:** halts_iff, next_sound and none_halts in lean/Phases.lean (kernel); no_halt_phases: 10^8 frames by native_decide.
- **Checked:** 10^8 frames native_decide (~9.7e11 steps); 10^15 steps exact macro sim and 6.66e22 steps rle accelerator (trusted).
- **Odds:** not stated
- **Next step:** Port the frame map to C/GMP and iterate far beyond 10^8 frames (as done for the doubling machines), and characterise which frames lead to the halting cases.

### [`1RB---_0RC0RB_1LD1LE_1LC1RF_1RB0LE_1RA0RD`](../../holdouts/1RB---_0RC0RB_1LD1LE_1LC1RF_1RB0LE_1RA0RD/README.md)

*reduced, outlook halts-late, table set T4*

- **Map:** Vampire family (bb6-vampire-family/README.md): E-events (c, n) = c E> 1^n with a context word c; the E-pass halves the block, then a context rewrite decided by (c, b = q mod 2) gives the next E-event, so n -> about 3n/2 with c -> c' (a counter-like rewriting of c). The rewrite is proved for the 99 contexts of the table; the rule for a general context is not decoded.
- **Halts when:** The orbit reaches a halting table entry (c, b); the machine halts iff it does, as long as the orbit stays in the table.
- **From blank tape:** first E-event at step 139, context 11, n = 17
- **Proved:** bb6-vampire-family/lean (kernel): Core.drain, Core.tbl_sound (99 contexts), nextE_sound, haltE_sound, and for this machine halts_of_check and not_halts_of_forall: a halting criterion both ways for orbits that stay in the table; orbit_kernel, 10,000 passes in the table.
- **Checked:** 2^18 passes native_decide (no halt, more than 10^45000 steps); c/orbit.c agrees with the outside repository's checkpoints. Outside report (not reproduced): orbit O4 halts at Bell 1,941,376,761,248.
- **Odds:** high: halting rate about 8.9e-13 per pass in the Markov model; the outside repository reports a halt near 10^12 passes.
- **Next step:** Run c/orbit.c to the reported halting pass with context counting, extend the table to those contexts, and evaluate a chunked (2-adic) check in Lean; or decode the general context rewrite (it looks like a counter with carries) to drop the table.

### [`1RB---_1LC0RB_0LD0LC_1RE1RB_1RD1LF_1LA0LE`](../../holdouts/1RB---_1LC0RB_0LD0LC_1RE1RB_1RD1LF_1LA0LE/README.md)

*reduced, outlook halts-late, table set T4*

- **Map:** Vampire family (bb6-vampire-family/README.md): E-events (c, n) = c E> 1^n with a context word c; the E-pass halves the block, then a context rewrite decided by (c, b = q mod 2) gives the next E-event, so n -> about 3n/2 with c -> c' (a counter-like rewriting of c). The rewrite is proved for the 99 contexts of the table; the rule for a general context is not decoded.
- **Halts when:** The orbit reaches a halting table entry (c, b); the machine halts iff it does, as long as the orbit stays in the table.
- **From blank tape:** first E-event at step 105, context 1, n = 15
- **Proved:** bb6-vampire-family/lean (kernel): Core.drain, Core.tbl_sound (99 contexts), nextE_sound, haltE_sound, and for this machine halts_of_check and not_halts_of_forall: a halting criterion both ways for orbits that stay in the table; orbit_kernel, 10,000 passes in the table.
- **Checked:** 2^18 passes native_decide (no halt, more than 10^45000 steps); c/orbit.c agrees with the outside repository's checkpoints. Outside report (not reproduced): orbit O1 halts at Bell 747,242,483,684.
- **Odds:** high: halting rate about 8.9e-13 per pass in the Markov model; the outside repository reports a halt near 10^12 passes.
- **Next step:** Run c/orbit.c to the reported halting pass with context counting, extend the table to those contexts, and evaluate a chunked (2-adic) check in Lean; or decode the general context rewrite (it looks like a counter with carries) to drop the table.

### [`1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LA---`](../../holdouts/1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LA---/README.md)

*reduced, outlook halts-late, table set T4*

- **Map:** Vampire family (bb6-vampire-family/README.md): E-events (c, n) = c E> 1^n with a context word c; the E-pass halves the block, then a context rewrite decided by (c, b = q mod 2) gives the next E-event, so n -> about 3n/2 with c -> c' (a counter-like rewriting of c). The rewrite is proved for the 99 contexts of the table; the rule for a general context is not decoded.
- **Halts when:** The orbit reaches a halting table entry (c, b); the machine halts iff it does, as long as the orbit stays in the table.
- **From blank tape:** first E-event at step 123, context 11, n = 15
- **Proved:** bb6-vampire-family/lean (kernel): Core.drain, Core.tbl_sound (99 contexts), nextE_sound, haltE_sound, and for this machine halts_of_check and not_halts_of_forall: a halting criterion both ways for orbits that stay in the table; orbit_kernel, 10,000 passes in the table.
- **Checked:** 2^18 passes native_decide (no halt, more than 10^45000 steps); c/orbit.c agrees with the outside repository's checkpoints. Outside report (not reproduced): orbit O3 halts at Bell 1,961,935,897,288.
- **Odds:** high: halting rate about 8.9e-13 per pass in the Markov model; the outside repository reports a halt near 10^12 passes.
- **Next step:** Run c/orbit.c to the reported halting pass with context counting, extend the table to those contexts, and evaluate a chunked (2-adic) check in Lean; or decode the general context rewrite (it looks like a counter with carries) to drop the table.

### [`1RB0RF_1LC---_1LF1LD_1RE0LD_0RC0RE_1LC1RA`](../../holdouts/1RB0RF_1LC---_1LF1LD_1RE0LD_0RC0RE_1LC1RA/README.md)

*reduced, outlook halts-late, table set T4*

- **Map:** Vampire family (bb6-vampire-family/README.md): E-events (c, n) = c E> 1^n with a context word c; the E-pass halves the block, then a context rewrite decided by (c, b = q mod 2) gives the next E-event, so n -> about 3n/2 with c -> c' (a counter-like rewriting of c). The rewrite is proved for the 99 contexts of the table; the rule for a general context is not decoded.
- **Halts when:** The orbit reaches a halting table entry (c, b); the machine halts iff it does, as long as the orbit stays in the table.
- **From blank tape:** first E-event at step 27, context 1, n = 7
- **Proved:** bb6-vampire-family/lean (kernel): Core.drain, Core.tbl_sound (99 contexts), nextE_sound, haltE_sound, and for this machine halts_of_check and not_halts_of_forall: a halting criterion both ways for orbits that stay in the table; orbit_kernel, 10,000 passes in the table.
- **Checked:** 2^18 passes native_decide (no halt, more than 10^45000 steps); c/orbit.c agrees with the outside repository's checkpoints. Outside report (not reproduced): orbit O4 halts at Bell 1,941,376,761,248.
- **Odds:** high: halting rate about 8.9e-13 per pass in the Markov model; the outside repository reports a halt near 10^12 passes.
- **Next step:** Run c/orbit.c to the reported halting pass with context counting, extend the table to those contexts, and evaluate a chunked (2-adic) check in Lean; or decode the general context rewrite (it looks like a counter with carries) to drop the table.

### [`1RB0RF_1LC---_1RD0LC_0RE0RD_1LF1LC_1LE1RA`](../../holdouts/1RB0RF_1LC---_1RD0LC_0RE0RD_1LF1LC_1LE1RA/README.md)

*reduced, outlook halts-late, table set T4*

- **Map:** Vampire family (bb6-vampire-family/README.md): E-events (c, n) = c E> 1^n with a context word c; the E-pass halves the block, then a context rewrite decided by (c, b = q mod 2) gives the next E-event, so n -> about 3n/2 with c -> c' (a counter-like rewriting of c). The rewrite is proved for the 99 contexts of the table; the rule for a general context is not decoded.
- **Halts when:** The orbit reaches a halting table entry (c, b); the machine halts iff it does, as long as the orbit stays in the table.
- **From blank tape:** first E-event at step 80, context 10001, n = 9
- **Proved:** bb6-vampire-family/lean (kernel): Core.drain, Core.tbl_sound (99 contexts), nextE_sound, haltE_sound, and for this machine halts_of_check and not_halts_of_forall: a halting criterion both ways for orbits that stay in the table; orbit_kernel, 10,000 passes in the table.
- **Checked:** 2^18 passes native_decide (no halt, more than 10^45000 steps); c/orbit.c agrees with the outside repository's checkpoints. Outside report (not reproduced): orbit O2 halts at Bell 731,899,010,932.
- **Odds:** high: halting rate about 8.9e-13 per pass in the Markov model; the outside repository reports a halt near 10^12 passes.
- **Next step:** Run c/orbit.c to the reported halting pass with context counting, extend the table to those contexts, and evaluate a chunked (2-adic) check in Lean; or decode the general context rewrite (it looks like a counter with carries) to drop the table.

### [`1RB0RE_1RC---_0RD0RC_1LE1LF_1LD1RA_1RC0LF`](../../holdouts/1RB0RE_1RC---_0RD0RC_1LE1LF_1LD1RA_1RC0LF/README.md)

*reduced, outlook halts-late, table set T4*

- **Map:** Vampire family (bb6-vampire-family/README.md): E-events (c, n) = c E> 1^n with a context word c; the E-pass halves the block, then a context rewrite decided by (c, b = q mod 2) gives the next E-event, so n -> about 3n/2 with c -> c' (a counter-like rewriting of c). The rewrite is proved for the 99 contexts of the table; the rule for a general context is not decoded.
- **Halts when:** The orbit reaches a halting table entry (c, b); the machine halts iff it does, as long as the orbit stays in the table.
- **From blank tape:** first E-event at step 114, context 1, n = 17
- **Proved:** bb6-vampire-family/lean (kernel): Core.drain, Core.tbl_sound (99 contexts), nextE_sound, haltE_sound, and for this machine halts_of_check and not_halts_of_forall: a halting criterion both ways for orbits that stay in the table; orbit_kernel, 10,000 passes in the table.
- **Checked:** 2^18 passes native_decide (no halt, more than 10^45000 steps); c/orbit.c agrees with the outside repository's checkpoints. Outside report (not reproduced): orbit O2 halts at Bell 731,899,010,932.
- **Odds:** high: halting rate about 8.9e-13 per pass in the Markov model; the outside repository reports a halt near 10^12 passes.
- **Next step:** Run c/orbit.c to the reported halting pass with context counting, extend the table to those contexts, and evaluate a chunked (2-adic) check in Lean; or decode the general context rewrite (it looks like a counter with carries) to drop the table.


## Outside proof (2)

A busycoq pull request claims a decision. Compile it.

### [`1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA`](../../holdouts/1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA/README.md)

*external, outlook halts-late, table set T203*

- **Map:** Map F on four node kinds: S(X)=0^inf 1^X 1110 B> 0^inf, P(k,m)=0^inf F> 0 0 (10)^k 1^m 0 1 0^inf, Q(u,n), T(u,v). P(k,m) -> P(2k+3, m-2k-3) (k>=2, m>=2k+3); S(X) -> P(6*2^t-3, X+3t+12-12*2^t) while 12*2^t <= X+3t+12; overflow O(p,i,r) cases go to P/Q/T/S (e.g. O(0,i,0)->S(4i+7)). Reset orbit X: 13, 29, 45, 137, 185, 217, ...
- **Halts when:** Halts iff the orbit of S(13) (node s 7) under F reaches a doubling round P(k,0) with no 1s (halts_iff_H). Busycoq PR 60 reports this happens at a = 28*2^85 - 6 (~10^55 steps).
- **From blank tape:** S(13) at step 110
- **Proved:** halts_iff and halts_iff_H in lean/Map.lean (kernel, standard axioms only); external Rocq proof of halting in busycoq PR 60, not compiled here.
- **Checked:** 10^7 orbit nodes native_decide (~299,000 returns, S(34,793,745)); 10^5 nodes kernel; 10^8 returns in C (X up to 1.5x10^10); external map's first 2,000,000 steps match ours.
- **Odds:** reported to halt after ~10^55 steps (busycoq PR 60, 313 jobs, 275 core-hours)
- **Next step:** Compile/verify the busycoq PR 60 proof (or run our Lean map through the ~10^25 middle returns) to confirm the halt.

### [`1RB0RE_1LC0RA_1RF0RD_---1LE_0LB1LE_1LE1RC`](../../holdouts/1RB0RE_1LC0RA_1RF0RD_---1LE_0LB1LE_1LE1RC/README.md)

*external, outlook unclear, table set T97*

- **Map:** Nested bouncer. Top level: P(x,y)=0 1^x 0 (10)^y 1 B> sweeps P(x+2,y)->P(x,y+2); empty tank P(1,y+2)->D(1,2y+12); round D(m,c+2m+6)->D(2m+3,c+2) on D(m,c)=C> 0 (10)^m 1^c. Second level: explicit Lean innerMap on K(C,y)=(10)^C 0 (10)^y 1 B> (entry uses 2 outer pairs, rounds k->2k+6). Outer event and 3-ones case not covered, so no full two-level map.
- **Halts when:** Halts iff state D reaches blank tape at the right edge (halts_iff_edge); a top-level reset from tank y halts iff y = 2^j - j - 5, j >= 4 (reset_halts). Full condition on the two-level map unknown.
- **Proved:** halts_iff_edge in lean/Edge.lean (kernel, CTL certificate), reset_halts in lean/Top.lean, inner_reset in lean/Level2.lean; no full halts-iff map. busycoq PR 67 claims nonhalting (listed in holdouts/external.json only, not mentioned in status.json); DeepMind halts-iff map as cited axiom.
- **Checked:** rleaccel 3.50x10^154 steps trusted; 10^7 steps native_decide.
- **Odds:** not stated; next outer event ~2^250 steps away
- **Next step:** Check busycoq PR 67's nonhalting proof; internally, prove the outer event and the 3-ones inner round to complete the two-level map.


## Prove the map (8)

The map is explicit but not yet a Lean halts-iff. Proof engineering would make the question exactly a question about the map.

### [`1RB---_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA`](../../holdouts/1RB---_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA/README.md)

*map-partial, outlook halts-late, table set T11*

- **Map:** Phase starts P 1^n 0 C>0 (P a word of blocks ending in 0): n -> 8*(n div 3) + d, where d and the next word P' depend only on P and n mod 3 (word map measured by simulation). Proved case: residue 0, (L 0 1^(a+1) 0, 3m+3) -> (L 0, a+8m+11). Finer class map on events A U^m B (affine in m per class (A,U,B,m mod 3)), extrapolated.
- **Halts when:** Granted the class map: the orbit reaches a halting class; nearest needs 108 prescribed residues mod 3 in a row, ending at tail 01011011 with m = 1 (mod 3).
- **From blank tape:** first phase start at step 110, P = 1111110, n = 12 (class map from step 2,763: A=0, U=1, m=107, B empty)
- **Proved:** Rounds of a phase for all counts and words and the residue-0 phase end (first_X, drain_X, drain_iter, phase_zero in lean/Phase.lean, kernel); no halts_iff; plus step_none_iff and 10^7 steps (native) in lean/Blank.lean.
- **Checked:** 9.66e72809 steps rle accelerator and 1.71e299748 steps region-memo accelerator (trusted); 2,000 exact phases (n 2,835 bits, trusted); 161,449 class-map rounds (~10^137,548 steps, heuristic); 10^7 steps native_decide.
- **Odds:** one chance in 3^108 per try for the nearest halting class (fair-dice residues); README older note: probably nonhalting
- **Next step:** Prove the class/word map in Lean (halts-iff on the word dynamics) or find an invariant excluding the halting classes; computation cannot reach the 108-residue halt.

### [`1RB0LC_1RC1RE_1LA0LD_0RB0RA_1RB1RF_1RD---`](../../holdouts/1RB0LC_1RC1RE_1LA0LD_0RB0RA_1RB1RF_1RD---/README.md)

*map-partial, outlook halts-late, table set T11*

- **Map:** Phase starts P 1^n 0 B>0: n -> 8*(n div 3) + d, d and next word P' depend only on P and n mod 3 (measured). Proved: residue 0, (L 0 1^(a+1) 0, 3m+3) -> (L 0, a+8m+11). Same table as 1RB---_0RC0RE_... with relabelled states; class map on A U^m B (m mod 3) extrapolated.
- **Halts when:** Granted the class map: orbit reaches a halting class; nearest needs 107 prescribed residues mod 3, tail 01011011 with m = 2 (mod 3).
- **From blank tape:** first phase start at step 17, P empty, n = 6 (class map from step 4,187: A=0, U=1, m=126, B=0 1^6)
- **Proved:** Rounds of a phase and residue-0 phase end (first_X, drain_X, drain_iter, phase_zero in lean/Phase.lean, kernel); no halts_iff; 10^7 steps native in lean/Blank.lean.
- **Checked:** 1.94e301751 steps region-memo and 1.88e69794 rle accelerator (trusted); 2,000 exact phases (n 2,833 bits, trusted); 167,895 class-map rounds (~10^143,039 steps, heuristic); 10^7 steps native_decide.
- **Odds:** one chance in 3^107 per try for nearest halting class; README status still says probably nonhalting
- **Next step:** Prove the word/class map in Lean (shared with its relabelled twins) or find an invariant excluding the halting classes.

### [`1RB0LE_1LC0RD_0RA1LD_0LC1RA_1LF1LA_---1LA`](../../holdouts/1RB0LE_1LC0RD_0RA1LD_0LC1RA_1LF1LA_---1LA/README.md)

*map-partial, outlook probviously-nonhalting, table set T188*

- **Map:** EL(m,T) = E> 1 00 1^m T, T a short list of runs. One round m -> (4m + c)/3, T -> T', c and T' depending on m mod 3 and T. Drain law: tail first run a, r = 0 or 2: a' = 4a/3 + O(1), m' = (4m - a)/3 + O(1); r = 1: m' = (4m + 3a + 8)/3 and a is absorbed.
- **Halts when:** EL(m,[a,...]) halts when m != 1 mod 3 and a >= 4m + 14 (m = 0 mod 3) or a >= 4m (m = 2 mod 3), up to 12 less with more runs following (checked m < 30, a < 200).
- **From blank tape:** EL(11, 0 1^2) at step 213
- **Proved:** No Lean map or halts-iff; lean/ has only Blank.lean/Machine.lean (blank-tape runs).
- **Checked:** 100,000 rounds of round map Python (beyond 10^24990 steps); class map 376,892 rounds (~10^94,180 steps, heuristic); regaccel 1.13x10^113280 steps; 10^18 steps macro sim.
- **Odds:** below 2^-100,000
- **Next step:** Prove the round map with the tail runs in residue classes in Lean (no regular/pushdown certificate can work); the halting question is then number-theoretic.

### [`1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`](../../holdouts/1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---/README.md)

*map-partial, outlook probviously-nonhalting, table set T11*

- **Map:** Phase start PS(M, T) = 0^inf F> 0 1^M T, M -> ~8M/3 + c with tail stack T edited by M mod 3. Proved: PS(3j+5,[]) -> PS(8j+17,[]); PS(3j+6,[]) -> PS(8j+19,[]); PS(3j+7,[]) -> PS(8j+13,[6]); PS(3j+5,[6]) -> PS(8j+23,[]); PS(3j+6,[6]) -> PS(8j+35,[]); PS(3j+7,[6]) -> PS(8j+17,[1,1,3]). Other tails: push/pop rules extrapolated from simulation.
- **Halts when:** Halts exactly when the tail reaches one of a few shapes with two adjacent blocks 0 1 1, e.g. [2, 2] with M = 1 mod 3; nearest halting class (tail 01011011, m = 1 mod 3) needs 108 prescribed residues mod 3.
- **From blank tape:** PS(9, [])
- **Proved:** Phase rules for tails [] and [6] (phase_e0 ... phase_s2 in lean/Phase.lean, rounds in lean/Rules.lean, kernel); no halts-iff.
- **Checked:** 10^7 steps native_decide; 30,000 phases of the extrapolated map Python (M ~12,800 digits, >10^25000 steps); region-memo run to 1.88e299809 steps; 184,790 class-map rounds.
- **Odds:** one chance in 3^108 per try (fair-dice residues); 3e6 random-residue phases had no halt
- **Next step:** Prove the phase map for every tail (generic push/pop rules) in Lean to get a full halts-iff reduction.

### [`1RB0RF_0LC1RE_---1LD_1LE0LB_0RF0LD_1RD1RA`](../../holdouts/1RB0RF_0LC1RE_---1LD_1LE0LB_0RF0LD_1RD1RA/README.md)

*map-partial, outlook probviously-nonhalting, table set T240*

- **Map:** C(e) = 0^inf 1 E> 0 (01)^e: odd e -> (3e+7)/2 (proved); e = 0 mod 4 (e >= 8) -> (3e+6)/2; e = 6 mod 8 -> (3e+12)/2; e = 2 mod 8: recursive halving cascade, no single formula (e.g. 18 -> 41, 74 -> 101, 90 -> 167) (even cases tabulated e <= 300).
- **Halts when:** Halts from C(e) for e = 2^k - 6 (2, 10, 26, ..., 1018; tabulated), possibly other even-cascade values; machine halts only on 0 B> 0.
- **From blank tape:** C(4) at step 67
- **Proved:** Odd branch odd_step in lean/Macro.lean and the halving stage of the even branch (even_start, halving in lean/Even.lean), kernel; no halts-iff.
- **Checked:** Blank orbit to C(70796) at step 9,357,982,502 (C simulation); rleaccel 6.56x10^16 steps; 10^7 steps native_decide.
- **Odds:** not quantified; 'a random-looking orbit hits such a sparse set with small probability'
- **Next step:** Close the last row of the even branch: a 21 Nov simulation table (README) gives the second stage Y(i, j) for all i except i = 8m+3 (and 7); with that row in hand, prove the map in Lean and iterate the orbit far beyond C(70796).

### [`1RB1LB_1LC1LA_1RD0LB_1RA1RE_1RF0RD_---1RD`](../../holdouts/1RB1LB_1LC1LA_1RD0LB_1RA1RE_1RF0RD_---1RD/README.md)

*map-partial, outlook probviously-nonhalting, table set T248*

- **Map:** Epochs on a counter Y of a's (pairs 01) and a tail of digits: Y -> 5*floor(Y/2) + c, c in {0,5,10}; the parity of Y steers a carry rewriting the front digits of the tail (proved reset shapes: (2k+2,e+1)->(2k+3,e) c=0; (3,e+3)->(1,4)(1,e+1) c=5; (1,1)(1,e+3)->(2,2)(1,e+1); (1,1)(3,e+3)->(2,7)(1,e+1)). Full reset map F not proved; epoch map uses simulated reset.
- **Halts when:** A reset carry runs through the whole tail of digits and the sweep reads 1 0 0 in state D (F0).
- **From blank tape:** not stated explicitly (13 epoch starts checked from blank tape to 7.3e11 steps)
- **Proved:** round_a, round_b and reset families in lean/Rules.lean, epoch by induction in lean/Epoch.lean (kernel); no halts_iff.
- **Checked:** 4,000 epochs of the epoch map (Y 1,593 digits, tail 1,311 digits, trusted); 1.49e193089 steps region-memo and 2.91e78053 rle accelerator (trusted).
- **Odds:** astronomically small (carry depth has an exponential tail, tail of 1,311 digits grows linearly)
- **Next step:** Prove the full reset map F (finite list of parametric reset shapes plus merging e = 0 digits) and glue it to epoch to get halts_iff.

### [`1RB1RD_1LC0LE_1RA0LB_1RA1RF_0RA0RC_1RE---`](../../holdouts/1RB1RD_1LC0LE_1RA0LB_1RA1RF_0RA0RC_1RE---/README.md)

*map-partial, outlook probviously-nonhalting, table set T11*

- **Map:** Phase start Q 0 1^m (01)^5 1 D>0 with m = 3k + r -> Q' 0 1^(8k+c) (01)^5 1 D>0, Q' and c fixed by (Q, r) (prefix Q acts as a nested counter), step count 12k^2 + Bk + C; fitted case by case (py/phasemap.py), not proved.
- **Halts when:** Granted the class map: halts if the orbit reaches a halting class; nearest known is tail 01011011 with m = 1 mod 3, 107 prescribed residues mod 3 away.
- **From blank tape:** phase 1 at step 3,291
- **Proved:** The cycle inside a phase only (cycle, lean/Cycle.lean, kernel): L 1^(x+3) (01)^y 1 D>0 -> L 1^x (01)^(y+4) 1 D>0.
- **Checked:** 10^7 steps native_decide; fitted map 3,000 phases (~10^2557 steps, Python); 185,703 class-map rounds; region-memo run to 4.44e299820 steps.
- **Odds:** one chance in 3^107 per try (fair-dice residues)
- **Next step:** Prove the phase map for every prefix (Q, r) in Lean to obtain a halts-iff reduction.

### [`1RB1RE_1LC1RE_---1LD_1LE0LB_0RF0LD_1RD1RA`](../../holdouts/1RB1RE_1LC1RE_---1LD_1LE0LB_0RF0LD_1RD1RA/README.md)

*map-partial, outlook probviously-nonhalting, table set T323*

- **Map:** Left-end tape = list of blocks a^x0 110 a^x1 110 ... (a = 01). Round: [x] -> (3x+5)/2 (x odd) or [x/2-1, 0, x] (x even); [x0,...,xk] -> [x0/2+x1+2, x2, ..., xk+x0] (x0 even, k >= 2); odd first block x0 -> (x0-3)/2. Exact map for all lists computed (affine above 16), not proved.
- **Halts when:** A first block of 1 (with another block following) halts: iff a run of odd first blocks starts with x0+3 a power of two, or a single block [4] occurs.
- **From blank tape:** [0,0,2] at step 50
- **Proved:** Drain trips (drain1, drain2D, drainS, drainSD) and first-block-1 halts (halt1S, halt1D) in lean/Rules.lean (kernel); the round map is not proved.
- **Checked:** 10^6 rounds of computed round map (> 10^94,000 steps); 10^400 steps exact run-length sim with extrapolated linear cycles.
- **Odds:** ~2^-n for n-bit x0 (tens of thousands of bits)
- **Next step:** Prove the round map in Lean (the halving sweep with its carry and the small-block cases are missing) for a halts-iff.


## Decode (29)

The round or phase map is not closed yet and has to be read off the machine first.

### [`1RB0LA_0RC1RD_0LD1RE_1LA0RF_0RD0LD_1RD---`](../../holdouts/1RB0LA_0RC1RD_0LD1RE_1LA0RF_0RD0LD_1RD---/README.md)

*map-partial, outlook unclear, table set T64*

- **Map:** Block list at A-events: X(n)=A> 00 (10)^n 01, Y(a,b)=A> 00 1010 (010)^a (10)^b 01, Z(a,b). Rules: X(2k)->Y(k-1,3k); Y(2i+1,b)->X(b+3i+7); X(2k+1)->Z(k,3k-2); Z(2i+1,b), Z(2i,2j), Z(2i,2j+1) -> longer lists. So X(n), n=0 mod 4 -> X((9n+16)/4). Rules for a general leftmost segment (10)^x (010)^y not yet written.
- **Halts when:** unknown
- **From blank tape:** X(400) at step 227,603, then Y(199,600), X(904), Y(451,1356), X(2038)
- **Proved:** shift rules only: lean/Blank.lean has step_none_iff and blank-run checks; no map or halts-iff in Lean.
- **Checked:** regaccel 3.97x10^78595 steps trusted; macro sim 10^18 steps trusted; six rules checked for all parameters < 40 (Python).
- **Odds:** not stated
- **Next step:** Write down the rules for a general leftmost segment (10)^x (010)^y to close the block-list map and find the halting condition.

### [`1RB0LC_1LA1RE_1LD1RE_1RE0LA_0RA1RF_0RB---`](../../holdouts/1RB0LC_1LA1RE_1LD1RE_1RE0LA_0RA1RF_0RB---/README.md)

*map-partial, outlook unclear, table set T34*

- **Map:** At C-events X(n,t)=C> 000 (100)^n T, Y(n,t)=C> (100)^n T (T = 1 or 101): X(n) -> X((3n+5)/2) n odd, -> Y((3n+6)/2) n even; Y(n) n even -> X((3n+4)/2). Y(n) n odd opens a nested phase: n=4i+1 -> X(9i+9), n=8i+7 -> X(27i+36); n=8i+3 nests deeper (recursion on 2-adic digits, not closed).
- **Halts when:** unknown (hidden in the nested phases; no synthetic nested phase with n < 400 halts)
- **From blank tape:** X(5) at step 184
- **Proved:** shift rules only: lean/Blank.lean step_none_iff and blank-run checks; no map in Lean.
- **Checked:** regaccel 1.93x10^175825 steps trusted; rleaccel 4.47x10^48268 steps trusted; map matches blank run to 4x10^10 steps; 10^7 steps native_decide.
- **Odds:** not stated
- **Next step:** Close the n = 8i+3 nested case (general recursion on 2-adic digits) to obtain the full map and its halting condition.

### [`1RB0LD_0RC1RB_0RD0RA_1LE0RD_1LF---_0LA1LA`](../../holdouts/1RB0LD_0RC1RB_0RD0RA_1LE0RD_1LF---_0LA1LA/README.md)

*undecoded, outlook unclear, table set T171*

- **Map:** No map. At left-end switches the tape is 0 0 1^x 0 1^y 0 1 1, at right-end switches 1 1 1 1 0^u 1^v 0 0 1 1 1 0; the split point moves erratically; width grows like t^(1/3).
- **Halts when:** Halts exactly at 1 D>0 (D on a 0 with a 1 to its left; E1 halts and E is entered only from D0). Not expressed in a map.
- **Proved:** Only step_none_iff and the 10^7-step blank run (lean/Blank.lean); DeepMind's halts-iff map available only as a cited axiom (lean/DeepMindMap.lean).
- **Checked:** 10^7 steps native_decide; 10^9 steps C; 2.78e16 steps accelerated Python (rleaccel_rec.py).
- **Odds:** not stated
- **Next step:** Decode how the split point (x, y) moves between switches, e.g. starting from DeepMind's cited map, to get a closed map.

### [`1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---`](../../holdouts/1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---/README.md)

*map-partial, outlook no-halt-route, table set T172*

- **Map:** Round on DL(m,T) = D> 1 00 (10)^m T (tail word T): (m,T) -> ((4m + c(r,T))/3, tau(r,T)), r = m mod 3, computed exactly from small representatives (valid for m >= 30). Proved sub-map on P(n)=(101)^n 01 A>: P(3k)->P(4k+2), P(3k+1)->P(4k+3), P(3k+2)->Q(4k+4) with Q(n)=(101)^n 110101 A>.
- **Halts when:** Halts exactly when state D reads a 0 with another 0 to its left (only possible inside a tail rewrite); no halting (residue, tail) round is known.
- **From blank tape:** P(1) at step 14; Q(80) at step 27,264
- **Proved:** P-map for every n (p0, p1, p2 in lean/Macro.lean, kernel) and blank_Q80; the general round (right sweep through each tail) is not proved in Lean.
- **Checked:** 100,000 rounds of the round map (past 10^24990 steps, m ~10^12494) Python; 309,710 class-map rounds (~10^77,393 steps) heuristic; rleaccel 3.45x10^30862 steps trusted.
- **Odds:** no halting round known at all among 90,000 explored; 'probviously non-halting'
- **Next step:** Find and prove an invariant on the tail language that excludes the halting pattern (and prove the round with symbolic k in Lean).

### [`1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA`](../../holdouts/1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA/README.md)

*map-partial, outlook unclear, table set T186*

- **Map:** Two counters X(a,b) = (10)^a 1^b C> 0, Y(a,b) = (10)^a 1^b 0 C> 0: for large a, X(a,b) -> X(a-d(b), f(b)) (b even) or Y(a-d(b), f(b)) (b odd); Y(a,b) -> Y(a-d-2, f+4) (b even) or X(a-d, f+2) (b odd). f(b) ~3.4b irregular (table for b < 400, looks 3-regular in base 3); turnover when a cannot pay is not mapped. DeepMind's halts-iff map exists only as a cited axiom.
- **Halts when:** unknown (f, d and the turnover are not worked out); DeepMind's axiom: halts iff orbit of DM.next from start reaches none
- **Proved:** shift rules only in this repo (step_none_iff, lean/Blank.lean); DeepMind's halts-iff is a cited axiom deepmind_halts_iff in lean/DeepMindMap.lean, not proved here.
- **Checked:** rleaccel 2.23x10^147 steps trusted; macro sim 10^18 steps trusted; b-map table for b < 400 Python.
- **Odds:** not stated
- **Next step:** Find the closed (3-automatic) form of f(b) and map the turnover, or port DeepMind's map and iterate it.

### [`1RB0LE_1RC0RF_0RD0RB_1RE0RC_1LA0LA_1RA---`](../../holdouts/1RB0LE_1RC0RF_0RD0RB_1RE0RC_1LA0LA_1RA---/README.md)

*undecoded, outlook unclear, table set T193*

- **Map:** No closed map. Cycle n starts at P 1^3 0^K 1 E>0 with K ~ 3*2^n; fill sweeps (proved) eat the gap 4 zeros per sweep; two prefix passes then open K' = 2K - c (K = 9, 15, 27, 51, 99, 197, 389, 773, ...) while rewriting a prefix of smaller gaps growing ~1.36-1.5 per cycle with no visible closed form.
- **Halts when:** Halts only on B>1 1 (B1 -> F, F1 halts), which would have to happen in a pass over the prefix.
- **From blank tape:** fill record z = 95, m = 2 at step 3,224
- **Proved:** Fill sweep and k sweeps at once (lean/Gadgets.lean, lean/Macro.lean, kernel) and that the blank run reaches them; no halts-iff.
- **Checked:** 10^7 steps native_decide; 28 cycles (1.06e17 steps) C jumping simulator; 2.15e5835 steps rleaccel; 4.45e4173 steps region-memo.
- **Odds:** not stated
- **Next step:** Decode the prefix-rewriting passes as a hierarchy of counters (gap sizes per cycle) to get a cycle map.

### [`1RB0LF_0LC0RE_0RA1LD_1LB0LD_0RA1RC_1LA---`](../../holdouts/1RB0LF_0LC0RE_0RA1LD_1LB0LD_0RA1RC_1LA---/README.md)

*map-partial, outlook unclear, table set T92*

- **Map:** Binary counter on block lists 0^inf ell B> c (10)^D1 x1 (10)^D2 x2 ... (exact block macro machine, 387 crossing rules). At resets the countdown block follows X -> 3X/2 + 1 (X even) or (3X+5)/2 (X odd) (heuristic, observed at 28 resets: 142, 214, 322, 484, 727, 1093, ...); next block Y' ~ 3Y/2 + c.
- **Halts when:** Halts exactly on 1 A> 1 (F reading 1, entered only from A reading 1); in terms of the reset map: unknown. Random record-like block lists can halt (2 in 14,742).
- **From blank tape:** B>0 (10)^12 1 0 0 0 at step 2,438
- **Proved:** 387 crossing rules (lean/Rules.lean), carry_even sweep (lean/Sweep.lean), short sweep and reach2438/reach2522 (lean/Macro.lean), all kernel; composition of rules and halts-iff not proved.
- **Checked:** macro run 3.39x10^14 steps (16,409,053 records, 28 resets) trusted; direct 1.17x10^11 steps C.
- **Odds:** not stated; no invariant excluding the halt known
- **Next step:** Prove soundness of composing the macro rules in Lean and derive a halts_iff reduction to the reset map (or find an invariant of reachable block lists).

### [`1RB0LF_1LC0RB_0LD1LA_0RA1LE_0LA0RA_1LA---`](../../holdouts/1RB0LF_1LC0RB_0LD1LA_0RA1LE_0LA0RA_1LA---/README.md)

*map-partial, outlook no-halt-route, table set T64*

- **Map:** Round starts RS(N,T) = A> (10)^4 110 (10)^N 10010 T, Ts=(10)^11 1, Tl(m)=(10)^m 1 (10)^11 0101, TD(p)=1 (10)^p 1 (10)^9 0101101: RS(4j+5,Ts)->RS(6j+10,Tl(3j+6)); RS(4j+2,Tl(m))->RS(9j+m+27,Ts); RS(4j+4,Ts)->RS(9j+33,Ts); RS(4j+4,Tl(m))->RS(6j+11,TD(3j+m+5)). Other residues/tails end in new shapes: not closed.
- **Halts when:** unknown in terms of the map; machine halts exactly at 1 A> 1 (A reads 1 with 1 to its left), which never occurs in the proved rounds.
- **From blank tape:** RS(13, Ts) at step 1817; then N = 22, 84, 213, 322, 909, 1366, 3780, 8529, 12796, 19199
- **Proved:** Four round branches round_A..round_D and no_halt_1842640229 / reach_19199 in lean/Round.lean (kernel), conversions convA..convH in lean/Conv.lean; no halts_iff.
- **Checked:** 1,842,640,229 steps kernel (N = 19199); 3.05e90539 steps region-memo and 1.07e16 rle accelerator (trusted); macro sim to step 4,516,954,072.
- **Odds:** not stated
- **Next step:** Extend the conversions to the TD tail and the new tail at N = 28802 and look for a tail family closed under rounds (py/orbit.py).

### [`1RB0RA_0RC0LB_1LD1RF_1LE1RA_1RD1RB_1LA---`](../../holdouts/1RB0RA_0RC0LB_1LD1RF_1LE1RA_1RD1RB_1LA---/README.md)

*undecoded, outlook no-halt-route, table set T46*

- **Map:** Undecoded: rounds where a bouncer turns blocks b = 10000 into a = 11010 and back; each round appends a block about the sum of the others (total doubles: 3, 21, 61, 152, ...); one block-cycle step proved, the round structure only observed / class-map extrapolated.
- **Halts when:** unknown (halts only if F reads a 1; F always had 0101 to its left in the first 2x10^8 steps)
- **Proved:** One block cycle (sweep in lean/Rules.lean, kernel); rounds not proved.
- **Checked:** Class-round map 54 rounds past the direct run (largest block 90 bits, extrapolation); 10^12 steps cycle accelerator; rleaccel 2.81x10^33 steps.
- **Odds:** not stated
- **Next step:** Decode the left-end gadget and block merging to write an explicit round map, then find whether any round can make F read a 1.

### [`1RB0RA_0RC0LE_0LD1RA_1LB0RF_0LD1LC_1RD---`](../../holdouts/1RB0RA_0RC0LE_0LD1RA_1LB0RF_0LD1LC_1RD---/README.md)

*undecoded, outlook unclear, table set T92*

- **Map:** No closed map: a binary counter with one-cell digits between runs of 10, paid from a reservoir of 10s at the right; basic increments proved, carries into higher separators, reservoir refills and the 1100 region not yet rules.
- **Halts when:** unknown in terms of a map; machine halts exactly when C or E reads a 0 with a 1 on its left and (10)^k 1 1 on its right.
- **Proved:** Increments half_sweep, inc_d0, inc_d1 for all block lengths in lean/Rules.lean (kernel); no halts_iff.
- **Checked:** 3.14e134 steps region-memo and 7.04e12 rle accelerator (trusted); 2*10^11 steps C (trusted); 10^7 steps native_decide.
- **Odds:** not stated
- **Next step:** Turn carries through higher separators, reservoir refills and the 1100 region into proved rules, then seek an invariant excluding the halting pattern.

### [`1RB0RA_1LC0LE_1RA1LD_0LB1LF_1LD0RC_1LB---`](../../holdouts/1RB0RA_1LC0LE_1RA1LD_0LB1LF_1LD0RC_1LB---/README.md)

*map-partial, outlook unclear, table set T101*

- **Map:** Row of levels lv(u,v) = W^u 11100 V^v (runs of 110, separator, runs of 100); front (x, y): phase (x, 3k+y) -> (x+4k, y). On an empty front: y -> 4y/3 (y = 0 mod 3), y -> 4(y-2)/3 + 2 (y = 2 mod 3), counter p += 2, next level (z, w) -> (z+2, w-2). y = 1 mod 3 starts secondary bouncers that rebuild the left part (not closed).
- **Halts when:** Halts exactly when D reads a 1 with a 1 to its left (1 1 C>1 or 1 1 E>0); proved rules never do this, y = 1 regime and deep resets not closed.
- **From blank tape:** clean regime at step 58,429: front y = 72 (y: 72, 96, 128, 170, 226)
- **Proved:** sweep, phase, end0/end2/cleanA/cleanB in lean/Macro.lean and start/clean_chain in lean/Start.lean (kernel + native_decide for the start); no halts-iff.
- **Checked:** 10^7 steps native_decide; 10^1000 steps cycle accelerator (py/run_accel.py).
- **Odds:** not stated
- **Next step:** Close the y = 1 mod 3 phase end and the deeper-level resets as proved rules to get a full level map.

### [`1RB0RA_1LC1RA_0LD1LD_0LE0LC_1LA0LF_---1LC`](../../holdouts/1RB0RA_1LC1RA_0LD1LD_0LE0LC_1LA0LF_---1LC/README.md)

*undecoded, outlook unclear, table set T103*

- **Map:** Row of units (10)^x 00 (10)^y 110 0 1^w 0; unit moves proved (cycle P x (y+1) w -> P (x+3) y (w+2), phase, turn into wall, return). Main phases y: 4, 14, 46, 142, ... mostly y -> 3y+4 but not a law (exception at 17th phase); joints between units (387 classes) not written as rules.
- **Halts when:** Halts on F reading 0: a left sweep finding 0 1 0 just left of a cell C passed (e.g. C at right end of (10)^2 1^m, m odd); a parity question at unit joints, no map-level condition.
- **From blank tape:** P 1 4 2 at step 173
- **Proved:** Unit moves for all sizes (lean/Gap.lean, lean/Levels.lean, lean/Phase.lean, kernel); reach_173/1225/5625 (lean/Reach.lean, native); no halts-iff.
- **Checked:** exact run-length simulator with phase jumps 5.1x10^36 steps trusted; 10^7 steps native_decide.
- **Odds:** not stated
- **Next step:** Write the 387 joint classes as rules to get a macro machine and a halting condition.

### [`1RB0RC_1LC1RF_1RE0LD_1LC1LA_---1RD_0RB0RA`](../../holdouts/1RB0RC_1LC1RF_1RE0LD_1LC1LA_---1RD_0RB0RA/README.md)

*undecoded, outlook unclear, table set T105*

- **Map:** Big block alternates d^Y (d=010) and a^X (a=10): d^Y -> a^(2Y+2), a^X -> d-block of ~2X/3 with remainders in a right-end tail; Y grows ~4/3 per cycle (61, 83, 137, 195, ..., 23325). Exact cycle map (X mod 3 and tail) not written down.
- **Halts when:** Halts on E reading 0 (C moving right meets two 0s); map-level condition unknown.
- **Proved:** shift rules only (right_B_a, right_F_d, right_A_011, right_B_110 in lean/Rules.lean, kernel).
- **Checked:** rleaccel 5.21x10^4051 steps trusted; 10^10 steps C; 10^7 steps native_decide.
- **Odds:** not stated
- **Next step:** Decode the exact 4/3 cycle map including how X mod 3 and the tail combine.

### [`1RB0RE_1LC1RD_1LA0LC_0RA1RF_1RD0LB_1RA---`](../../holdouts/1RB0RE_1LC1RD_1LA0LC_0RA1RF_1RD0LB_1RA---/README.md)

*undecoded, outlook unclear, table set T101*

- **Map:** Undecoded: words 100 and 101 in nested regions, each counting off the one to its right; full sweeps at steps 25,912, 827,042, 1,021,956,316 (nested-counter shape).
- **Halts when:** unknown (machine halts when F reads a 1).
- **Proved:** Shift rules only (b_right, b_left, a_right in lean/Rules.lean, kernel) plus 10^7 steps native.
- **Checked:** 3.18e97153 steps region-memo and 1.75e25107 rle accelerator (trusted); 3*10^9 steps C.
- **Odds:** not stated
- **Next step:** Write down the region types and boundary-advance rules between full sweeps and fit the sweep gaps to a nested-counter formula.

### [`1RB0RE_1RC0RF_1LD1RA_1LB1LD_1RA1LB_---0LD`](../../holdouts/1RB0RE_1RC0RF_1LD1RA_1LB1LD_1RA1LB_---0LD/README.md)

*map-partial, outlook no-halt-route, table set T238*

- **Map:** Phase starts 0^inf B> 0 1 0^X T (gap X, tail word T): X -> (3X+d)/2 with d in {+6,-6} for X = 0 mod 4 and {+3,-3,-9} for X = 2 mod 4, d and the new tail T' set by (X mod 4, T); measured table map (not proved), tail rewrites partly read off as rules (e.g. 1^a 0^b -> 1^(a+12) 0^(b-6) when X = 2 mod 4).
- **Halts when:** Halts on F reading 0, only during a phase end while the head works through the tail; no halting entry of the table has been seen (0 of 6,000 alternative residues halt).
- **From blank tape:** X = 6, T = 1^8 (gaps 4, 12, 24, 42, 60, ... in the run)
- **Proved:** Rounds of a phase only (phase in lean/Phase.lean, kernel); the phase map and halts-iff are not in Lean.
- **Checked:** 2,009 phases of the table map (gap 1,179 bits) Python; macro sim 3.9x10^13 steps (35 phases); rleaccel 1.77x10^30400 steps trusted.
- **Odds:** not stated; no halting entry seen at all
- **Next step:** Close the set of tail-rewrite rules (a stack driven by X mod 4) and look for an invariant that excludes the F-on-0 transition.

### [`1RB1LA_1RC0RF_1RD---_0LE1RB_---0LA_1LD1RF`](../../holdouts/1RB1LA_1RC0RF_1RD---_0LE1RB_---0LA_1LD1RF/README.md)

*undecoded, outlook unclear, table set T245*

- **Map:** No map: the tape is 3 to 9 blocks of 1s separated by single 0s, block lengths roughly doubling left to right (97, 198, 397, 795, ...); sweeps merge and split blocks irregularly, no rule found (wiki: potential Cryptid).
- **Halts when:** Any halt (C reading 1 or E reading 0) happens with exactly 1 1 1 1 1 then blank tape left of the head (within six cells of the left end); map-level condition unknown.
- **Proved:** halt_left in lean/LeftEdge.lean (CTL closure by native_decide, rest kernel); no map.
- **Checked:** rleaccel 9.33x10^20 steps trusted; 10^7 steps native_decide.
- **Odds:** not stated
- **Next step:** Decode the merge/split block-list dynamics into explicit rules (a map on a short list of block lengths).

### [`1RB1LB_0RC0LD_1LD1RE_1RC0LA_1RD1RF_0RD---`](../../holdouts/1RB1LB_0RC0LD_1LD1RE_1RC0LA_1RD1RF_0RD---/README.md)

*undecoded, outlook unclear, table set T55*

- **Map:** Undecoded: two blocks of 1s trade cells (+4/-3 per round trip, e.g. cycle23: (111)^n1 +8 words, (111)^n3 -6), so regime lengths go ~4n/3 (3, 7, 12, 17, 25, ..., 44967) with an offset set by n mod 3 and a short left-end word; end-of-regime rule not worked out.
- **Halts when:** unknown (F reading 1 not reduced to a condition on the map)
- **Proved:** 35 one-cycle rules in lean/Cycles.lean (kernel); no map or halts-iff.
- **Checked:** bbtools.cycles to 10^40 steps (trusted, proved rules); region-memo accelerator 7.27x10^112352 steps.
- **Odds:** not stated
- **Next step:** Extract the end-of-regime rule (effect of n mod 3 on the left-end word) to get an explicit map; shared with its two related tables.

### [`1RB1LB_1RC1LD_1LA1RE_1RD0LA_0RB0RF_0RA---`](../../holdouts/1RB1LB_1RC1LD_1LA1RE_1RD0LA_0RB0RF_0RA---/README.md)

*undecoded, outlook unclear, table set T56*

- **Map:** No closed map: at left-end visits the tape is A>0 P (110)^N 1 with a short word P; N grows by ~3/2 per visit (1080, 2457, 3690, 8325, 12492, 28122), only observed.
- **Halts when:** F reading 1; not reduced to the map.
- **Proved:** Eleven shift rules only (lean/Rules.lean, kernel).
- **Checked:** 10^7 steps native_decide; 10^9 steps C; region-memo run to 4.60e202939 steps; 325,831 class-map rounds (heuristic).
- **Odds:** not stated
- **Next step:** Extract the exact map (N, P) -> (N', P') from the left-end samples and prove it.

### [`1RB1LC_1LA0RD_0LB1LF_1RE1LC_1LC0RB_0LA---`](../../holdouts/1RB1LC_1LA0RD_0LB1LF_1RE1LC_1LC0RB_0LA---/README.md)

*map-partial, outlook unclear, table set T34*

- **Map:** K(pre,N,S) = B> 0 0 pre 1^N S. With pre, S empty: N=4j -> (empty, 3N/2+4, empty); N=4j+2 -> (10, 3N/2+2, empty); N=4j+1 -> (10, (3N+1)/2, 011); N=4j+3 -> (empty, (3N+5)/2, 011). With pre=10 offsets 7, 5, 7/2, 11/2. Measured for N = 20..31; effect on the growing right word S (a counter) not worked out.
- **Halts when:** unknown (halting transition F reading 1 not located in terms of the map)
- **From blank tape:** run samples N = 175, 263, 395, 584, ...
- **Proved:** shift rules only (fourteen rules in lean/Rules.lean, kernel).
- **Checked:** rleaccel 9.07x10^41345 steps trusted; 448 class-map rounds (~10^108 steps) heuristic; 10^7 steps native_decide.
- **Odds:** not stated
- **Next step:** Work out how the right word S evolves under the odd N values and locate the F-reads-1 halt; it shares its table with 1RB0LC_1LA1RE_... whose nested-phase rules may transfer.

### [`1RB1LC_1LA0RD_1LB1LF_1LE1RE_0LA0RB_0LB---`](../../holdouts/1RB1LC_1LA0RD_1LB1LF_1LE1RE_0LA0RB_0LB---/README.md)

*undecoded, outlook unclear, table set T55*

- **Map:** Undecoded: two big blocks of 1s trade cells (8 three-cell words in, 6 out per cycle), regimes grow ~4/3 (3, 7, 10, 14, ..., 5667216) with a short tail of small blocks; same numbers as 1RB1LB_0RC0LD_..., suggesting the same map; end-of-regime rule not extracted.
- **Halts when:** unknown (F reading 1 not reduced to a condition on the map)
- **Proved:** 40 one-cycle rules in lean/Cycles.lean (kernel); no map or halts-iff.
- **Checked:** bbtools.cycles to 10^40 steps (trusted); region-memo accelerator 8.24x10^113165 steps.
- **Odds:** not stated
- **Next step:** Extract the end-of-regime rule (jointly with 1RB1LB_0RC0LD_1LD1RE_1RC0LA_1RD1RF_0RD---, same table) to write the 4n/3 map.

### [`1RB1LC_1LA1LD_1LD0LC_0LE0RD_1RA1LF_1RC---`](../../holdouts/1RB1LC_1LA1LD_1LD0LC_0LE0RD_1RA1LF_1RC---/README.md)

*undecoded, outlook unclear, table set T46*

- **Map:** Undecoded: epochs on a stack of q-blocks, D> 0 q 0 S p^3 S q^c0 r q^c1 r q^c2 ... (p=10110, q=10000, S=1011, r=1000); top block c0 = 3, 9, 25, 50, 102, 306, 414, 829, 1658, 4975, 6641, new top about 2x or 3x the old one or the stack sum; epoch map not extracted.
- **Halts when:** unknown; a halt needs E on a 1 with a 1 to its left, only possible at an epoch end.
- **Proved:** One round of an epoch (round in lean/Rules.lean, kernel) plus 10^7 steps native.
- **Checked:** 3.54e36 steps Quick_Sim (trusted); 3*10^9 steps C.
- **Odds:** not stated
- **Next step:** Extract the epoch-end rule (how the new top block is built from the stack) and prove it with symtm.

### [`1RB1LC_1LC0RF_0LF1LD_0LE---_1RF1LC_1LE0RA`](../../holdouts/1RB1LC_1LC0RF_0LF1LD_0LE---_1RF1LC_1LE0RA/README.md)

*map-partial, outlook unclear, table set T34*

- **Map:** Phase length l with tail: empty: l even -> 3l/2+4, empty; odd -> (3l+5)/2, [2]. [2]: even -> 3l/2+7, empty; odd -> (3l-1)/2, [8,2]. [8,2]: 3l/2+19 / (3l-19)/2, [26,2]. [26,2]: 3l/2+46 / (3l-625)/2, [359,2]. [359,2]: 3l/2+538 / (3l-1717)/2, [1232,2]. [1232,2]: 3l/2+1855 / (3l-3079)/2, [2780,2]. Tails [b,2] form an unbounded chain (measured, not proved).
- **Halts when:** Only D reading 1 halts; no halting tail found, phase ends for general tails not decoded.
- **From blank tape:** first phase l = 88
- **Proved:** One round and k rounds by induction (round, lean/Rules.lean; rounds, lean/Rounds.lean, kernel); no halts-iff.
- **Checked:** 10^7 steps native_decide; 47 phases exactly (3.4e18 steps, l = 2.39e9) C with Lean round jumps; 1.24e48365 steps rleaccel; 1.22e175810 steps region-memo.
- **Odds:** not stated
- **Next step:** Decode the phase end for a general tail [b,2] (the block 1^b processed like a small copy of the run) to close the tail system.

### [`1RB1LE_0RC1RC_0RD0RB_1RE0RF_1LA0LE_---1RB`](../../holdouts/1RB1LE_0RC1RC_0RD0RB_1RE0RF_1LA0LE_---1RB/README.md)

*undecoded, outlook unclear, table set T103*

- **Map:** Undecoded epoch map: right-end countdown L 0 1^2j 0 0 1 1 0 (10)^(a+1) 0 0 (10)^b 1 E> gives (j,a,b) -> (j+1,a-1,b+3) every two visits (proved); epochs a_0 = 3, 30, 75, 225, 677, 1783 (about x3), then nested counters; how the gap is refilled is not decoded.
- **Halts when:** unknown in terms of a map; machine halts exactly when C reads a 0 with 1 0 to its right (C> 0 1 0).
- **Proved:** Countdown and erase rules (visit_p, visit_q, exit1-3, erase, outer_step in lean/Rules.lean, kernel); no halts_iff.
- **Checked:** 2.98e30 steps rle accelerator (trusted); exact macro run to 1.09e19 steps (trusted); 10^12 steps blocks-of-16 C.
- **Odds:** not stated (CTL with windows of 6 allows 970 halting configurations)
- **Next step:** Decode the gap filling (inner loop at the gap's right edge with J symbolic) to get the epoch map, then try a CTL seeded with the rules.

### [`1RB1LE_1LC1RC_1LA1RD_1LD0RB_0LC0LF_0LB---`](../../holdouts/1RB1LE_1LC1RC_1LA1RD_1LD0RB_0LC0LF_0LB---/README.md)

*map-partial, outlook unclear, table set T56*

- **Map:** S-state B>0 0 0 1^X 0 T -> X' = (3X + c)/2, c and the new tail depending on X mod 6 and T (table on the explainer page, not in closed form; tail update not closed).
- **Halts when:** unknown (halts in state C on a 0 with three 1s to its left; no S-state tried halts)
- **Proved:** Two sub-rounds absorb and convert in lean/Rules.lean (kernel); cycle map not proved.
- **Checked:** 10^13 steps cycles accelerator; class map 100,179 rounds (~10^17,645 steps, heuristic); region-memo 6.59x10^203023 steps; Quick_Sim 2.23x10^24513 steps.
- **Odds:** not stated
- **Next step:** Put the tail update in closed form and determine which tails can reach the halting pattern.

### [`1RB1LF_1LC0RD_---1LD_1RB1RE_1LA0LB_0LA0LE`](../../holdouts/1RB1LF_1LC0RD_---1LD_1RB1RE_1LA0LB_0LA0LE/README.md)

*undecoded, outlook unclear, table set T105*

- **Map:** Undecoded: a list of counters a^x 1^(6k) (a = 10) on the left and one long block of 1s growing ~4/3 per round (8,750, 22,510, 29,966, 39,758, 52,630, 97,478, ...), re-encoded as ones, 100s, 10s; no round rule known.
- **Halts when:** unknown
- **Proved:** Shift rules only (six sweeps in lean/Rules.lean, kernel).
- **Checked:** rleaccel 8.81x10^4679 steps; region-memo 6.62x10^27877 steps; class map checked on 45 rounds to 3x10^9 steps.
- **Odds:** not stated
- **Next step:** Find the round rule (re-encoding of the long block and the counter list) to get an explicit map.

### [`1RB1LF_1RC1LD_1LB1LE_1LE0LD_0LA0RE_1RD---`](../../holdouts/1RB1LF_1RC1LD_1LB1LE_1LE0LD_0LA0RE_1RD---/README.md)

*undecoded, outlook unclear, table set T46*

- **Map:** No closed map: a stack of runs of d = 10010 separated by c = 1000 plus a short tail; each round pushes a new top about 6 or 4/3 times the old one, the old top gains one d, lower runs never change (observed in 17 right-end events).
- **Halts when:** F reading 1; not reduced to a map.
- **Proved:** Twenty-three shift rules only (lean/Rules.lean, kernel).
- **Checked:** 10^7 steps native_decide; 5e9 steps C; 1.12e37 steps Quick_Sim (outside program).
- **Odds:** not stated
- **Next step:** Determine the exact rule for the new top of the stack from right-end events and prove it.

### [`1RB1RA_1LC0RB_1LD0LB_1RA0LE_---1LF_1LB0LA`](../../holdouts/1RB1RA_1LC0RB_1LD0LB_1RA0LE_---1LF_1LB0LA/README.md)

*map-partial, outlook unclear, table set T296*

- **Map:** Phase starts P 0^z B> (prefix stack P): z = 4k+1 -> 6k+1, z = 4k+3 -> 6k+7 (z' = zmap(z) + c), while the stack P records z mod 4 and is rewritten near its right end; phases computed with a stand-in z of the same residue mod 4 (observed, not proved).
- **Halts when:** Halts on state C reading 0 with 0 1 to its left; would need a phase end walking unusually deep into the stack. Map-level condition unknown.
- **From blank tape:** first phase starts at steps 218, 546, 1220, ...
- **Proved:** sweep rule only (sweep in lean/Sweep.lean, kernel).
- **Checked:** 900 phases with stand-in block (~10^319 steps, z 160 digits) heuristic; 25 phases full simulation in C; 10^7 steps native_decide.
- **Odds:** not stated
- **Next step:** Prove that a phase depends on z only through z mod 4 and write the stack rewriting as explicit rules.

### [`1RB1RF_1LC1RD_1LA1LC_1RA0RE_1RD1LA_---0LE`](../../holdouts/1RB1RF_1LC1RD_1LA1LC_1RA0RE_1RD1LA_---0LE/README.md)

*map-partial, outlook no-halt-route, table set T331*

- **Map:** Epochs E(g,R) = 0^inf A> 0 1 0^g R -> E(3g/2 + c, R'), c in {-9,-6,-3,+6} and R' depending only on g mod 4 and the stack R (checked, not proved; R a growing stack of runs).
- **Halts when:** unknown in terms of the map; every halting R in a random search contains a lone 1, which the run never makes near the front of R.
- **From blank tape:** g = 4206 (epoch iteration start, step not stated)
- **Proved:** One sweep and many sweeps (xstep in lean/Rules.lean; sweep, sweeps in lean/Phase.lean), kernel; epoch map not proved.
- **Checked:** 300 epochs of the epoch map (~10^110 steps, g ~ 10^55); rleaccel 4.96x10^29100 steps; region-memo 8.72x10^110443 steps.
- **Odds:** not quantified; 'a halt would need the front to dig down through a stack that keeps getting deeper'
- **Next step:** Describe R exactly as a stack automaton and prove the class map in Lean for the R that occur.

### [`1RB1RF_1RC0LD_1LB1RA_1RE1LE_0RC0LB_0RB---`](../../holdouts/1RB1RF_1RC0LD_1LB1RA_1RE1LE_0RC0LB_0RB---/README.md)

*undecoded, outlook unclear, table set T55*

- **Map:** No exact pass map: a marker 0 zig-zags to the right end of a run of 1s; a pass from gap g widens the tape by about g/3, so width x about 4/3 per pass (706, 945, 1266, ..., 192218); next marker set by a left-end prefix and width mod 3. Zig-zag proved; pass ends and launches not.
- **Halts when:** unknown; F1 needs A to read 1 followed by another 1 (a rightward sweep meets triples out of phase).
- **Proved:** Shift rules and marker zig-zag (zig_d in lean/Rules.lean; z_pass, pass_c, pass_l0, pass_l2 in lean/Pass.lean, kernel); no halts_iff.
- **Checked:** 3.64e112456 steps region-memo and 1.23e35914 rle accelerator (trusted); 2*10^10 steps direct (21 passes).
- **Odds:** not stated
- **Next step:** Write and prove the exact pass map (pass end, left-end turn with prefix, launches at gap 0 or 2 mod 3) to get a 4/3 Collatz-like map with a halts-iff.


## Number theory (46)

Lean already reduces halting to the map. What is left is a Collatz-type question about one orbit, beyond current methods; only a lucky halt hunt could change that.

### [`1RB0LB_1LC0RE_1LA1LD_0LC---_0RB0RF_1RE1RB`](../../holdouts/1RB0LB_1LC0RE_1LA1LD_0LC---_0RB0RF_1RE1RB/README.md)

*reduced, outlook probviously-nonhalting, table set T70*

- **Map:** E(a,m) = 1 0 0 (10)^a 0^m E> 1. For a >= 1, m >= 2: m=3k -> E(a+6,4k+4); m=3k+1 -> E(a-1,4k+7); m=3k+2 -> E(a+4,4k+4).
- **Halts when:** Can only halt when the counter a runs out (a = 0 with m = 1 mod 3, and then only for some gaps; others become a translated cycler or restart the counter); the a = 0 case is not decoded as a map.
- **From blank tape:** E(4,124) at step 9,008
- **Proved:** emap_sound in lean/Map.lean and orbit_sound / not_halts_of_good in lean/Orbit.lean (kernel): if the counter never runs out the machine never halts; deepmind_halts_iff in lean/DMMap.lean (kernel): halts iff the orbit of DeepMind's map stops, every clause a rule of lean/DMRules.lean (written by tools/deepmind/dmproof.py).
- **Checked:** 20,000 map steps native_decide (>10^5000 steps, counter 60,462); 1,000 kernel; 10^6 map steps Python (counter never below 58); regaccel 1.64x10^177574 steps.
- **Odds:** ~10^-28,700 from where Lean leaves it (10^-27.6 from a = 58)
- **Next step:** none: pure number theory (random walk with drift +3).

### [`1RB0LF_1LC0LD_1RD1LB_---1RE_0RA1RE_1LA0LE`](../../holdouts/1RB0LF_1LC0LD_1RD1LB_---1RE_0RA1RE_1LA0LE/README.md)

*reduced, outlook probviously-nonhalting, table set T97*

- **Map:** Outer epochs O(N) = 1^N F>0 0 1^3 -> O(N'), N' about 2^(sqrt(N)/3) (depends on remainders of doubling passes; inner epochs X_j = 24*2^j - 3 heuristic, checked j < 400). Lean proves the block machine (mstep) exactly and that halting is exactly hitting H, but not a closed form for N -> N'.
- **Halts when:** Machine halts iff the run passes an outer configuration O(N) = 1^N F>0 0 1^3 with N = 2^(n+4) - 2n - 10 (Lean, both directions: outer_halts, halts_iff_outer).
- **From blank tape:** N = 10 at step 102
- **Proved:** halts_iff and halts_iff_four (block machine) in lean/Reduce.lean, outer_halts in lean/Outer.lean, halts_iff_outer (halts iff the outer orbit meets 2^(n+4) - 2n - 10) in lean/Epoch.lean, all kernel; the closed form of N -> N' is not proved.
- **Checked:** Outer orbit 10, 27, 60, 118, 254, 514, 1014, 2106, 17220, 8534636888060 (~6.5x10^25 steps) computed Python; 1.9x10^14 steps native_decide; rleaccel 1.92x10^1788 steps.
- **Odds:** negligible: halting set has ~1 element per doubling of N, orbit at 8.5x10^12 and growing doubly exponentially
- **Next step:** Prove the inner-epoch closed form (X_j = 24*2^j - 3 -> X_{j+1}, j + 4 units) so that N -> N' is an explicit function in Lean, then study it mod powers of two.

### [`1RB1LE_0LC0LB_1RD1LC_1RD1RA_1RF0LA_---1RE`](../../holdouts/1RB1LE_0LC0LB_1RD1LC_1RD1RA_1RF0LA_---1RE/README.md)

*reduced, outlook unclear, table set T273*

- **Map:** X(k,m) = A>0 0 (10)^k 1^m 0, k >= 1: m >= 4 (or m = 3, k even): k = 2j -> X(3j+3, m-2), k = 2j+1 -> X(3j+5, m-3); m = 3, k odd -> X(3j+4, 1); m = 2: k even -> X(2, 3k+5), k odd halts; m = 1: k odd -> X(2, 3k+3), k even runs right forever; m = 0: k even -> X(2, 3k), k odd runs right forever.
- **Halts when:** Countdown reaches m = 2 with k odd (halts); m = 1 with k even or m = 0 with k odd is a non-halting translated cycler.
- **From blank tape:** X(1,1) at step 24
- **Proved:** deepmind_halts_iff in lean/DMMap.lean (kernel): halts iff the orbit of DeepMind's map stops, every case a rule of lean/DMRules.lean; the passes are an induction (rounds). The macro rules above are checked by simulation (k < 40, m < 14).
- **Checked:** Three epochs computed exactly (m = 6, 41, 16,169; third epoch ends after 6,456 macro steps); rleaccel 1.02x10^41433 steps; region-memo 3.85x10^213008 steps.
- **Odds:** halts with probability 2/5 (runs away 3/5); 1/5 halt per epoch
- **Next step:** none: the fourth epoch (m with 1,139 digits) is out of reach; optionally a Lean link from DeepMind's map to the epoch game.

### [`1RB1LE_1LB1LC_1RD0LE_---0RB_1RF1LA_0RA0RD`](../../holdouts/1RB1LE_1LB1LC_1RD0LE_---0RB_1RF1LA_0RA0RD/README.md)

*reduced, outlook probviously-nonhalting, table set T278*

- **Map:** Y(n) = 0^inf 1^n 0 B>0: odd n -> 3n - 7 (Y(3) halts); even n: 2-adic piecewise linear, e.g. n = 4 mod 8 -> 3n/2 - 6, 16 mod 32 -> 9n/8 - 5, 22 mod 32 -> 15n/8 - 9/4, 2 mod 64 -> 27n/16 - 99/8, 14 mod 64 -> 45n/16 - 3/8, finer classes for the rest (infinitely many).
- **Halts when:** An even step halts on a sparse set: 10, 12, 34, 48, 122, 138, 178, 186, 192, 230, 294, ... including every 3*4^k (57 even n below 20,000).
- **From blank tape:** Y(2) (orbit 2, 5, 8, 14, 39, 110, 232, ...)
- **Proved:** deepmind_halts_iff in lean/DMMap.lean (kernel): halts iff the orbit of DeepMind's map on E(q,a,b,c), F_even(d,k,b,c) stops; 36 rules in lean/DMRules.lean. Also shift rules and r_halt in lean/Rules.lean.
- **Checked:** 10^7 steps native_decide; exact run-length C simulator to 1.748e20 steps (Y(7,858,625,690) at step 1.72e19); region-memo run to 7.89e703 steps.
- **Odds:** halting fraction of even n falls ~n^-0.5; chance of a halt after n = 1.4e9 of order 10^-4
- **Next step:** none: pure number theory; optionally a closed form of the even map (nested 2-adic structure) to iterate the orbit faster.

### [`1RB1LE_1LC0RA_0RF0LD_1LE1LA_1RC0LB_---1RC`](../../holdouts/1RB1LE_1LC0RA_0RF0LD_1LE1LA_1RC0LB_---1RC/README.md)

*reduced, outlook probviously-nonhalting, table set T280*

- **Map:** Marker lists at left-extension moments B> 0 0 a^k b a^m 1 / ... b a^n 1 (a=10, b=110): [k,m], m>=k+2 -> [2k+3, m-k-2]; [k,k+1] -> [1, 2k+3, 1]; [k,k] -> [2k+3] (no marker, halts); m < k: [k-m, 2m+3] if k-m odd, [1, k-m-1, 2m+3] if even; [k,m,n] n odd: [2k+3, m-k-2, n] if m>=k+2, [1, 2k+n+4] if m<=k, [1, 4k+n+10] if m=k+1. Fitted, not proved.
- **Halts when:** Halts iff the orbit of [1,1,1] meets two equal blocks [k,k] (assuming the fitted map); a block with no marker halts (proved).
- **From blank tape:** [1,1,1] at step 72
- **Proved:** deepmind_halts_iff in lean/DMMap.lean (kernel): halts iff the orbit of DeepMind's map on A(a,b), B(a,b,c) reaches some A(a,a); rounds and zloops by induction, 18 rules in lean/DMRules.lean. Also blank_to_P and single_halts in lean/Halt.lean.
- **Checked:** 3x10^8 map iterations exact Python (blocks ~1,000 bits); map matches run at 214 marker moments to 3.7x10^7 steps; rleaccel 2.21x10^88 steps trusted.
- **Odds:** 'a halt looks very unlikely' (chance of exact hit shrinks as blocks grow); no number given
- **Next step:** none: pure number theory (does the orbit of DeepMind's map from A(2,0) ever reach A(a,a)?).

### [`1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA0LB_---0LC`](../../holdouts/1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA0LB_---0LC/README.md)

*reduced, outlook halts-late, table set T295*

- **Map:** X(n, m) = 0^inf C>0 0^n 1^m 0 1, n even: m >= 2: n = 0 mod 4 -> X(3n/2+4, m-1), n = 2 mod 4 -> X((3n+10)/2, m-2); m = 1: n = 0 -> X(3n/2+4, 0), n = 2 -> new epoch X(4, 3n/2+6); m = 0: n = 0 -> X(4, 3n/2+5), n = 2 -> halt. Equivalently y = n/2+4, y -> ceil(3y/2), m -1 (y even) / -2 (y odd).
- **Halts when:** Halts at X(n, 0) with n = 2 mod 4.
- **From blank tape:** X(4, 5) at step 50; epochs start with m = 5, 57, 210,273,201, then m of 82,000,544 bits
- **Proved:** deepmind_halts_iff in lean/DMMap.lean (kernel): halts iff the orbit of DeepMind's map stops, every clause a rule of lean/DMRules.lean (written by tools/deepmind/dmproof.py). The macro map is checked by simulation (even n < 60, m < 12).
- **Checked:** Third epoch exactly (140,180,848 macro steps, divide-and-conquer parity iteration with GMP); 10^7 steps native_decide; 2.42e65295 steps rleaccel_rec.
- **Odds:** each epoch halts with probability 1/3, so halts with probability 1, but the fourth epoch lasts ~10^24,684,623 macro steps
- **Next step:** none: the halting question is out of computational reach; optionally a Lean link from DeepMind's map to the epoch game.

### [`1RB---_1LC0LD_0RF0LD_0LE0RA_0LC1RA_1RC1RD`](../../holdouts/1RB---_1LC0LD_0RF0LD_0LE0RA_0LC1RA_1RC1RD/README.md)

*reduced, outlook probviously-nonhalting, table set T134*

- **Map:** E-events Ev(n,T) = E> 0^6 (10)^n T, tail T in {1, X_k = 000(10)^k 1, Y_k = 11(01)^k, Z_k = 000(10)^k 0001}. n' = (3n+c)/2 for tails 1 and Z_k, n' = (9n+c)/8 for X_k, Y_k; new tail and c depend on tail and n mod 2 or n mod 8; k changes by -2..+1 or becomes 3k/2+3 or (3k+1)/2 (full table in py/emap.py / lean/Map.lean).
- **Halts when:** A halt can only come from tail Z_k with k = 0 or n < 12k+12 (the region the map does not cover); non-halting holds if the orbit never enters it.
- **From blank tape:** (tail 1, n = 0) at step 18
- **Proved:** next_sound in lean/Map.lean (kernel, 83 case theorems in lean/Cases.lean) proves the map for every tail and n except Z_k with k = 0 or n < 12k+12; not_halts_of_orbit in lean/Orbit.lean reduces non-halting to the orbit staying in the proved region (one direction: entering the region is not proved to halt).
- **Checked:** 3,000 passes kernel (10^450 steps); 10^5 passes native_decide (10^16000 steps); 10^5 passes Python with margin n/(12k+12) >= 55 (k never above 1,046).
- **Odds:** chance ~(n/12)^-1.2 per phase: ~10^-5 at end of direct simulation, far smaller after (n has thousands of digits)
- **Next step:** none: pure number theory (a bound k <= f(n) along the orbit is a Collatz-type statement); optionally prove the uncovered Z_k small-n cases.

### [`1RB---_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD`](../../holdouts/1RB---_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD/README.md)

*reduced, outlook probviously-nonhalting, table set T63*

- **Map:** K(x,m,s) = 1^4 0 (10)^x 1^m, head in C on s at right end. B: K(x+1,2n,s) -> K(x,2n+4,1-s); R: K(0,2n,0) -> K(n+3,1,0), K(0,2n,1) -> K(n+3,3,0); C: K(i+n+3,2n+1,0) -> K(i,4n+9,0), K(i+n+3,2n+1,1) -> K(i,4n+8,1); A: K(j+2,2(j+1+k)+1,s) -> K(2j+5,2k+3,1-s), K(j+2,2j+1,1) -> K(2j+5,1,0); A': K(j+2,2j+1,0) -> K(2j+7,1,0).
- **Halts when:** Case H: K(0,2n+1,s) halts. Equivalently a doubling (C, s=0) chain from (x,m,0) halts iff x+k+1 = (m+7)(2^(k+1)-1)/2 for some k >= 0 (algebra, not in Lean).
- **From blank tape:** (x,m,s) = (7,1,0) at step 216
- **Proved:** halts_iff (orbit of (7,1,0) under mstep reaches H) in lean/MapThm.lean, kernel; rules in lean/Rules.lean, lean/CRule.lean.
- **Checked:** 10,000 map rounds Python on the proved map (29,225,208 C steps, far beyond 10^100 steps); 4.84x10^772 steps rleaccel (trusted); 10^7 steps native_decide.
- **Odds:** summed chance 0.3187 almost all in first 20 rounds (checked); rounds 21-1000 add < 10^-4
- **Next step:** none: pure number theory

### [`1RB0LC_0LC0RF_1RD1LC_0RA1LE_---0LD_1LF1LA`](../../holdouts/1RB0LC_0LC0RF_1RD1LC_0RA1LE_---0LD_1LF1LA/README.md)

*reduced, outlook halts-late, table set T158*

- **Map:** X(a,b,c) = D> 0 0 1^a 0 1^b (01)^c: a>=3: (a-2,b+3,c); a=1,c>=1: (b+1,4,c-1); a=1,c=0: (b+1,3,0); a=2,c>=3: (b+6,4,c-3); a=2,c=2: (b+6,3,0); a=2,c=1: (b+5,3,0); a=2,c=0,b even: (1,1,b/2+1) refill.
- **Halts when:** Orbit reaches a = 2, c = 0, b odd (budget of 01 pairs runs out and the next even a is 2 mod 4).
- **From blank tape:** (a,b,c) = (1,1,4) at step 138
- **Proved:** halts_iff in lean/Map.lean (kernel): halts from blank iff the orbit of next from (1,1,4) reaches halt; ten rules in lean/Rules.lean.
- **Checked:** 4 budget refills computed exactly (cycles 3, 8, 25, 2,549; c = 9, 31, 4,966, a 1,479-bit number); 1.40e136781 steps region-memo accelerator, 8.91e32351 steps Quick_Sim (trusted); 10^7 steps native_decide.
- **Odds:** a fair coin per budget; next decision about 2^1478 rounds away
- **Next step:** none: pure number theory (the fifth budget, ~2^1478 rounds, cannot be computed).

### [`1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_---1RA`](../../holdouts/1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_---1RA/README.md)

*reduced, outlook probviously-nonhalting, table set T159*

- **Map:** U(a,b) = A> 011011 1^a 0 1^b, V(a,b) = A> 1110 1^a 0 1^b (o = other tag, s = same). a even: a=2 mod 4, b odd -> o((3a+10)/2, b); a=0 mod 4, b odd >=7 -> s((3a+16)/2 [U] or (3a+20)/2 [V], b-5); b=3,5 special; a,b even: b>=a+4 -> s(3a+6 [U]/3a+8 [V], b-a-3); b<=a-2 -> o(3b+4, a-b-1); b=a,a+2 -> V(4|2, 3a+c). Full table in py/emap.py.
- **Halts when:** Halts exactly at U(a,1) or V(a,1) with a = 0 mod 4.
- **From blank tape:** U(4, 3) at step 118
- **Proved:** next_sound and next_isSome in lean/Map.lean (kernel, 32 case theorems) prove the map for every even a (the run only meets even a); not_halts_of_orbit in lean/Orbit.lean reduces non-halting to the orbit; that the halting events halt is checked by simulation only.
- **Checked:** 3,000 passes kernel (10^500 steps); 10^5 passes native_decide (10^10000 steps); 10^6 passes Python (both numbers ~96,600 digits).
- **Odds:** P(halt) ~ 2/a; ~3e-5 from the last simulated event, ~10^-96600 after 10^6 passes
- **Next step:** none: pure number theory (whether subtraction steps ever leave b = 1 with a = 0 mod 4).

### [`1RB0LC_1LC0RD_1LF1LA_1LB1RE_1RB1LE_---0LE`](../../holdouts/1RB0LC_1LC0RD_1LF1LA_1LB1RE_1RB1LE_---0LE/README.md)

*reduced, outlook halts-late, table set T76*

- **Map:** Four-counter map next on (a,b,c,k), tape E>0 1^a 0 1 0 1^b (01)^c (11101)^k 1 (28 macro rules): a 3/2-type map on one counter paid for from a budget c of 01 pairs; exact formulas in lean/Map.lean (generated by py/gen_map.py), not restated in status.
- **Halts when:** Orbit reaches case halt: a = 1, c = 1, b even (a budget ends with a = 1 and b even).
- **From blank tape:** (15,7,7,1) at step 1,188
- **Proved:** halts_iff in lean/Map.lean (kernel), with 30 macro rules in lean/Rules.lean.
- **Checked:** Orbit computed exactly through 4 budget ends (phases 4, 34, 683,741, 683,742), ~700,000 phases Python; regaccel 9.20x10^130534 steps; Quick_Sim 5.62x10^27158 steps.
- **Odds:** ~1/4 per budget end; halts with probability 1 but only after ~2^399,946 more phases
- **Next step:** none: pure number theory (the 5th budget holds a 399,947-bit number of pairs).

### [`1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE`](../../holdouts/1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE/README.md)

*reduced, outlook probviously-nonhalting, table set T38*

- **Map:** P(n) = (10)^n A> 0: for h_k < n < h_{k+1}, n -> 3n - 10*2^k + 3k + 14 (i.e. 5*2^k - 1 + 3r with r = n - h_k - 1), h_k = 5*2^k - k - 6 (3, 12, 31, 70, 149, ...). Closed form checked for n <= 200,000, Lean proves the computable pstep.
- **Halts when:** P(h_k) halts: halts iff the orbit of 4 lands exactly on some h_k.
- **From blank tape:** n = 4 at step 31
- **Proved:** halts_iff in lean/Iff.lean (kernel): halts iff orbit k 4 = none for some k under pstep (pstep_sound in lean/Macro.lean); the closed form of pstep is not proved in Lean.
- **Checked:** 2,000 map steps native_decide (10^798 steps); 200 kernel (10^86); 10^5 map steps Python (n 66,605 bits, ~10^40,100 steps).
- **Odds:** ~10^-20,000
- **Next step:** none: pure number theory (optionally prove the closed form of pstep in Lean).

### [`1RB0LD_1RC1RA_1LD0RB_1LE1LA_1RF0RC_---1RE`](../../holdouts/1RB0LD_1RC1RA_1LD0RB_1LE1LA_1RF0RC_---1RE/README.md)

*reduced, outlook halts-late, table set T179*

- **Map:** g(K,j) = (j + 3*floor(K/2) + 1, 0) for K even, (j + 3*floor(K/2) + 3, 1) for K odd; seq A = A-th iterate of g from (0,1). Walls: A_1 = 3, A_{i+1} = 2(j + 3*floor(K/2)) + 7 where (K,j) = seq A_i, while K odd. Underlying phase config 1^a 0 0 (10)^K 1^(2j+1) C> 0.
- **Halts when:** Some epoch ends with (seq A_i).K even.
- **From blank tape:** mstep orbit from (a,K,j) = (3,0,1) at step 18; walls 3, 25, 227,097, then A_4 of 39,991 digits
- **Proved:** halts_iff in lean/Macro.lean (kernel): halts iff some (seq A_i).K even; epochs_small (kernel) and epoch3_odd/halts_late in lean/Epoch3.lean (native_decide): halt only at end of epoch 4 or later.
- **Checked:** 3 epochs survive (native_decide), more than 10^79,981 steps; 3.31e203569 steps region-memo accelerator (trusted).
- **Odds:** fair coin per epoch: 1/2 at end of epoch 4, after more than 10^(10^39989) steps
- **Next step:** none: pure number theory (epoch 4 needs the parity of seq at an index of 39,991 digits).

### [`1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RB---`](../../holdouts/1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RB---/README.md)

*reduced, outlook probviously-nonhalting, table set T70*

- **Map:** Wall C z y = A>0 0 10 0^z (10)^y 0 1: (3k, y) -> (4k+1, y+4); (3k+1, y) -> (4k+5, y+6); (3k+2, y) -> (4k+8, y-1) (last two need y >= 1).
- **Halts when:** The orbit can leave the rules only at y = 0 with z not divisible by 3; only some such exits halt (C 92 0 halts after 54,805 steps, C 8 0 does not in 10^6).
- **From blank tape:** (z, y) = (0, 0) at step 7
- **Proved:** next_sound and not_halts_of_orbit in lean/Reduce.lean (kernel): non-halting iff-style reduction to the orbit never exiting (exit only at y = 0, z != 0 mod 3).
- **Checked:** 10,000 macro steps native_decide (10^2400 steps); 10^6 macro steps Python (z 124,940 digits, y = 2,999,377, never below 4); region-memo run to 3.09e177252 steps.
- **Odds:** reach y = 0 from height y with probability ~0.335^y; y ~ 3e6
- **Next step:** none: pure number theory (Antihydra-like question on z in base 3).

### [`1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA`](../../holdouts/1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA/README.md)

*reduced, outlook probviously-nonhalting, table set T199*

- **Map:** Z(t) = 1^t A>. t even >= 6: F(t) = 3t/2+1 if 4|t else 3t/2+3. t odd >= 7: a = 1, d = (t+3)/2, loop: d = 0 halt; d < a: F = S(a-1-d, 2d+2) with S(x,y) = 2y+1+3x (x even), 2y+3+3x (x odd); d = a: F = 4a+4; d = a+1: restart a = 1, d = 2a+3; else a <- 2a+3, d <- d-a-2. Small: F(0)=F(1)=19, F(2)=6, F(4)=7, F(5)=20, Z(3) halts.
- **Halts when:** Halts iff the orbit of z 44 reaches H: z t with t = 2^(j+1) - 2j - 7 (3, 17, 47, 109, 235, ...) or a restart rs d with d + s + 4 = 2^(s+2).
- **From blank tape:** blank = z 0 -> z 19 -> z 44
- **Proved:** halts_iff, halts_iff_44, halts_iff_H in lean/Reset.lean (kernel, no native_decide).
- **Checked:** 300 resets kernel; 10,000 resets native_decide (t ~3,900 bits); region-memo run to 4.28e3287 steps.
- **Odds:** one halting odd value per doubling band, t grows ~1.3x per reset: expected number of future hits far below 1
- **Next step:** none: pure number theory.

### [`1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_---1LB`](../../holdouts/1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_---1LB/README.md)

*reduced, outlook probviously-nonhalting, table set T211*

- **Map:** S(p,r) = C on leftmost of 1^p 0 1^r: S(1,r) -> S(r+4,1); S(2,3m+1) -> S(3m+6,1); S(2,3m+2) -> S(3m+5,2); S(3k+3,r) -> S(4k+r+6,1); S(3k+4,r) -> S(4k+r+8,1); S(3k+5,r) -> S(k+1,2k+r+5). Doucette form: D = p+1 = 3^v(3a+rho), next start (D+a+v+r+rho+1, 1).
- **Halts when:** S(2,3m+3) halts: orbit reaches p = 2 with 3 | r; equivalently the sequence (4,1),(8,1),(14,1),(22,1),... reaches (3^v, r) with v + r = 1 mod 3.
- **From blank tape:** S(3,1) at step 11
- **Proved:** halts_iff in lean/Map.lean and halts_iff_doucette in lean/Doucette.lean (kernel).
- **Checked:** 30,000 samples kernel (>10^3747 steps, lean/Bound.lean); 10^9 Doucette terms (198,650,412 base-3 digits) by 2-adic algorithm, trusted.
- **Odds:** ~10^-4 (from N ~ 10^5; lower after the 10^9-term run)
- **Next step:** none: pure number theory

### [`1RB0RB_1LC1RE_1LF0LD_1RA1LD_1RC1RB_---1LC`](../../holdouts/1RB0RB_1LC1RE_1LF0LD_1RA1LD_1RC1RB_---1LC/README.md)

*reduced, outlook probviously-nonhalting, table set T50*

- **Map:** S(p,r) = D> on leftmost cell of 1^p 0 1^r: S(3,r) -> S(r+5,2) (r odd) / S(r+5,1) (r even); S(2k+2,r) -> S(3k+r+4,1); S(2m+1,r) -> S(m-1,m+r+3) (m>=2). Doucette form: D = p+3 = 2^v(2a+1), D -> D + a + v + 1 (r = 1), exception D = 3*2^v (run ends at p = 3).
- **Halts when:** Orbit reaches p = 1 (S(1,r) halts); equivalently the Doucette sequence (5,2), (9,1), (14,1), (19,1), ... reaches a power of two (tape length N = 2^j - 1).
- **From blank tape:** S(2,2) at step 11; Doucette sequence starts (5,2)
- **Proved:** halts_iff in lean/Map.lean and halts_iff_doucette in lean/Doucette.lean (kernel); no_halt_10_3669 in lean/Bound.lean (kernel); no_pow2_mod_twelve in lean/PowMod.lean.
- **Checked:** 10^9 Doucette terms by 2-adic algorithm (last term 401,522,426 bits, trusted); 30,000 map steps kernel (10^3669 steps); 10^10 steps C.
- **Odds:** ~3*10^-4 that it ever halts (heuristic)
- **Next step:** none: pure number theory.

### [`1RB0RD_0RC1RE_1RD0LA_1LE1LC_1RF0LD_---0RA`](../../holdouts/1RB0RD_0RC1RE_1RD0LA_1LE1LC_1RF0LD_---0RA/README.md)

*reduced, outlook halts-late, table set T226*

- **Map:** P m n = 0^inf (1011)^m 1^n (10)^3 A> 1, n = 3k+3+r: r=0: (m-1, 8k+19) if m>=1, (2k+4, 5) if m=0; r=1: (m-2, 8k+29) if m>=2, halt if m=1, (0, 8k+18) if m=0; r=2: (m-2, 8k+35) if m>=2, (2k+8, 5) if m=1, (0, 8k+18) if m=0.
- **Halts when:** Orbit reaches (m,n) = (1, n) with n = 1 mod 3.
- **From blank tape:** P 14 5 at step 1,098
- **Proved:** halts_iff in lean/Map.lean (kernel); runs_long in lean/Orbit.lean (native_decide).
- **Checked:** Two cycles, orbit to phase 6,819 native_decide: no halt in 10^2899 steps.
- **Odds:** 1/5 per cycle; halts with probability 1 after a tower of exponentials
- **Next step:** none: pure number theory (third cycle needs ~5x10^2901 phases).

### [`1RB0RE_1LC1LD_0RA0LD_1LB0LA_1RF1RA_---1LB`](../../holdouts/1RB0RE_1LC1LD_0RA0LD_1LB0LA_1RF1RA_---1LB/README.md)

*reduced, outlook halts-late, table set T235*

- **Map:** next(k,z): k even: (3(k/2)+1, z-1) if z>=1, (0, 3(k/2)+2) if z=0; k odd: (3(k/2)+4, z-2) if z>=2, (0, 3(k/2)+5) if z=1, none (halt) if z=0. k/2 floor; z = fuel. Equivalently u = k+2, u -> 3*ceil(u/2) from u = 2 each round.
- **Halts when:** Orbit reaches none (k odd, z = 0): a round with fuel z halts iff z equals the fuel spent before some odd u.
- **From blank tape:** (0,5) (D(0,0,5) after 136 steps)
- **Proved:** halts_iff in lean/Macro.lean (kernel), rules in lean/Rules.lean.
- **Checked:** Three rounds (fuel 5, 14, 185) survive, 138 applications of next (Python); rleaccel 3.45x10^41498 steps.
- **Odds:** ~1/3 per round; probably halts but after a number of steps with ~10^21 digits
- **Next step:** none: pure number theory (round 4 with fuel 22,205,951,667,644,132,025,548 needs parity of u_i for i near 1.5x10^22).

### [`1RB0RF_1RC1RF_1LD0LE_---1LC_1RA1LE_1LC1RB`](../../holdouts/1RB0RF_1RC1RF_1LD0LE_---1LC_1RA1LE_1LC1RB/README.md)

*reduced, outlook probviously-nonhalting, table set T50*

- **Map:** P(n) = 0^inf 1^n B> 0^inf. With n+2 = 2^j m, m odd: f(n) = 2^j m + (m+2j-1)/2, except m = 1 (halt) and m = 3 with j even >= 2: f(n) = 9*2^(j-1) + 3j/2 + 3. Doucette form: D = n+2 = 2^v(2a+1) -> D + a + v + 2, except D = 3*2^v, v even > 0: (3D+3v+10)/2.
- **Halts when:** Halts iff the orbit of 4 reaches n with n+2 a power of two (>= 4); equivalently the sequence D = 6, 10, 15, 24, 30, ... reaches a power of 2.
- **From blank tape:** n = 4 (P(4)) at step 9
- **Proved:** halts_iff and f_none_iff in lean/Macro.lean, halts_iff_doucette in lean/Doucette.lean (kernel); halting_exponent in lean/Preimage.lean.
- **Checked:** 10^9 Doucette terms trusted (fast 2-adic, last term 401,524,403 bits); 200,000 passes exact Python; 10,000 passes native_decide.
- **Odds:** ~2^-80,000 (expected halts left from 80,223 bits on)
- **Next step:** none: pure number theory

### [`1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE`](../../holdouts/1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE/README.md)

*reduced, outlook probviously-nonhalting, table set T50*

- **Map:** K(p,q) = A>0 1^p 0 1^q: odd p: (p,q) -> ((p-3)/2, q+(p+5)/2); even p >= 2: (p,q) -> (3p/2+q, 1); (0,q) -> (2,q-1); p = 1 halts. Doucette form at K(p,1): D = p+3 = 2^v(2a+1), D' = D + a + v (D' = D + v + 3 when D = 3*2^v).
- **Halts when:** Orbit reaches p = 1; iff some K(p,1) has p + 3 a power of two; iff the sequence 5, 7, 10, 13, 19, 28, ... reaches a power of two.
- **From blank tape:** K(0,2) at step 7
- **Proved:** halts_iff and halts_iff_pow2 in lean/Reduction.lean, halts_iff_doucette in lean/Doucette.lean (kernel); halt_time_native: any halt takes > 2^80181 steps.
- **Checked:** 200,000 samples native_decide (halt > 2^80181 steps); 5,000 kernel (> 2^2073); 10^9 Doucette terms by 2-adic algorithm (401,523,017 bits), trusted.
- **Odds:** expected number of future hits 'far below one' (chance ~1/X per chain start)
- **Next step:** none: pure number theory

### [`1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_---0LD`](../../holdouts/1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_---0LD/README.md)

*reduced, outlook probviously-nonhalting, table set T244*

- **Map:** Doucette's sequence: D_0 = 6, D -> D + v + 3a for D = 2^v(2a+1) (6, 10, 17, 41, 101, 251, 626, ...). Underlying mxdys map on X(b,c) = 0^inf A>0 1^b 0 0 1^c: (0,c)->(c+2,1); (2k+2,c)->(5k+c+7,1); (2k+3,c)->(k,k+c+4); (1,c) halts.
- **Halts when:** Some D_k is a power of two (equivalently the X orbit from (3,1) reaches b = 1).
- **From blank tape:** X(3,1) at step 45; D_0 = 6
- **Proved:** halts_iff in lean/Macro.lean and halts_iff_pow2 in lean/Collatz.lean (kernel); Fit_kernel/Fit_native in lean/Bound.lean (20,000 terms kernel, 300,000 native_decide).
- **Checked:** 10^10 terms by 2-adic algorithm (last term 9,411,461,282 bits, trusted); 3*10^6 terms C; 300,000 terms native_decide; 20,000 kernel.
- **Odds:** far below 10^-10000
- **Next step:** none: pure number theory.

### [`1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_---0LA`](../../holdouts/1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_---0LA/README.md)

*reduced, outlook halts-late, table set T76*

- **Map:** S_t(x, c) = A> on 1^x (01)^2 1^6 (01)^c 1^t 0 1^2, t in {3, 6}: step (x, c+2) -> (floor(3x/2)+7, c). When c hits 0 or 1, B = 3*floor(x/2)+7 (+t if c = 0) and by parity of B either halt or reset to S_3(4,(B-5)/2), S_3(6,(B-8)/2), S_3(5,(B-5)/2) (c=0), S_6(4,(B-3)/2), S_6(6,(B-6)/2), S_6(5,(B-3)/2) (c=1, t=3), or a short phase to S_3(floor(3y/2)+4, 1) (c=1, t=6).
- **Halts when:** Halts iff the orbit of (4, 4, 3) under next reaches a halt: one residue class in four at each reset, e.g. from S_3(x,2) for x = 1, 6 mod 8; from S_3(x,1) for x = 2 mod 4; from S_6(x,1) for x = 0, 9, 11, 14 mod 16.
- **From blank tape:** S_3(4, 4) at step 388
- **Proved:** halts_iff and next_spec in lean/Reset.lean, step_rule in lean/Step.lean (kernel); orbit_585 (native_decide) rules out a halt before phase 3.
- **Checked:** 585 map terms (phases 0-2, ~10^203 steps) native_decide; region-memo run to 3.70e130329 steps.
- **Odds:** each phase from phase 3 on halts with chance ~1/4; probably halts within a few phases, but after a tower of exponentials of steps
- **Next step:** none: pure number theory (phase 3 halts iff the ((c-1)/2)-th iterate of x -> floor(3x/2)+7 from 6, c ~2.3e101, is 2 mod 4; no shortcut known).

### [`1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_---0RE`](../../holdouts/1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_---0RE/README.md)

*reduced, outlook probviously-nonhalting, table set T38*

- **Map:** D> 10 1^N: N -> 3N + 24 + 6j - 20*2^j, j = least j >= 1 with 20*2^j > N + 12 + 2j (closed form checked for even N 8..3000; Lean proves the computable phase map).
- **Halts when:** Remainder m_j = N + 10 - 10*2^j + 2j equals 0 (halting N = 10*2^j - 2j - 10: 8, 26, 64, 142, ...).
- **From blank tape:** N = 22 at step 208
- **Proved:** halts_iff in lean/Orbit.lean (kernel): halts iff orbit of 22 under next = phase 1 reaches none; closed form not proved in Lean.
- **Checked:** 10^6 map rounds Python exact (N 666,845 bits); rleaccel 4.65x10^1516 steps; region-memo 1.55x10^3084 steps.
- **Odds:** below 10^-200000
- **Next step:** none: pure number theory (optionally prove the closed form in Lean).

### [`1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LF---_0RA1LA`](../../holdouts/1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LF---_0RA1LA/README.md)

*reduced, outlook unclear, table set T259*

- **Map:** Phase ends B> 0 0 1 (1100)^n (10110110)^r 10 (1110)^t 1; period (n,m+5) -> (n+31,m) proved; reset table by r (measured): r=0 new phase m' = ceil((n+4)/2), t-4; r=1 (n+12,0), t-1; r=2 (n+32,0), t-4; r=3 m' = floor((n+25)/2), t-3; r=4 m' = floor((n+26)/2), t-2; new phase (10,m') ends at n = 10+31*floor(m'/5), r = m' mod 5. Also DeepMind's cited halts-iff map on states R1,R2,Q,S4,S6(n) from S6(1).
- **Halts when:** DeepMind map reaches none. In the repo's terms: second-level resets with a nearly empty tail, e.g. tail 10 (1110)^2 1001101011001 with r = 2 halts; reached from 6 words left, r = 0, n = 0 or 9 (mod 10).
- **From blank tape:** first-level tail 10 (1110)^6805 1 from (n,r,t) = (17,0,6805) at step 374,475,636; DeepMind start S6(1)
- **Proved:** Repo Lean: left-end turns and period in lean/Rules.lean, periods in lean/Periods.lean (kernel), no halts_iff; deepmind_halts_iff in lean/DeepMindMap.lean is a cited axiom (DeepMind's compiled theorem).
- **Checked:** Exact accelerated run to 4.5e17 steps (trusted); 7.07e19058 steps Quick_Sim (trusted); reset table iterated 2,176 more phases to ~10^1541 steps (heuristic).
- **Odds:** not stated; outcome decided after ~10^770 second-level phases by n mod 10 and r (halt, loop or third level)
- **Next step:** Prove the reset rows in Lean (making the first level a theorem) and prove one halting and one looping second-level class with n symbolic.

### [`1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RB1RF_---1RD`](../../holdouts/1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RB1RF_---1RD/README.md)

*reduced, outlook probviously-nonhalting, table set T269*

- **Map:** Shapes at left turns into D: X(a,b,c) = 1^a 0 (10)^b 1 D> 0 1^c, Y(a,b,c) = same with 00, Z(a,c) = 1^a 0 D> 0 1^c; 20 counter rules, e.g. X(a+4,b,c+2) -> X(a+1,b+2,c+1) (4b+13 steps), Y(a,b+1,c+2) -> Y(a+3,b,c+1) (4b+13 steps); full list in lean/Rules.lean / lean/Model.lean.
- **Halts when:** Halts iff the orbit of X(2,0,3) reaches some Z(a,2), i.e. a Y run whose middle block empties exactly when the right block holds 3 ones (c - b = 3 at the start of a Y run).
- **From blank tape:** X(2,0,3) at step 29
- **Proved:** halts_iff and not_halts_of_orbit in lean/Model.lean (kernel only), 20 rules in lean/Rules.lean.
- **Checked:** 2,000 rounds Python (N ~10^756, ~10^1511 steps); 9,500 rounds GMP c/xyz.c (~10^7170 steps); no Lean orbit evaluation stated; region-memo run to 1.98e2708 steps.
- **Odds:** ~1/N per Y run outside the doubling stage (impossible by parity inside it); closest approach after round 3 |c-b-3| ~ 10^-5.5 N
- **Next step:** none: pure number theory (a closed form for the endgame of a round would help analysis but the reduction is complete).

### [`1RB1LD_1RC1RE_0LA1LB_0LD1LC_1RF0RA_---0RC`](../../holdouts/1RB1LD_1RC1RE_0LA1LB_0LD1LC_1RF0RA_---0RC/README.md)

*reduced, outlook probviously-nonhalting, table set T272*

- **Map:** E(m,k) = 0^inf D> 110 (10)^m (110)^k 0^inf: (3t, k) -> (4t+4, k-1) (k = 0 stays 0); (3t+1, k) -> (4t+4, k+1); (3t+2, k) -> (4t+5, k+1).
- **Halts when:** Halts iff the orbit of (8, 1) reaches a pair (3t+2, 0), i.e. m = 2 mod 3 with k = 0.
- **From blank tape:** (m,k) = (8,1), E(8,1) at step 280
- **Proved:** halts_iff in lean/Round.lean (kernel only), with round_some/round_none and blank_to_E.
- **Checked:** 1,000,000 map rounds Python big integers (k = 331,763 at the end, never below 7 after round 10); rleaccel 2.23x10^20543 steps trusted; 10^7 steps native_decide.
- **Odds:** return to k = 0 has probability ~2^-k with k ~331,763 (Antihydra-type argument)
- **Next step:** none: pure number theory

### [`1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_---0RE`](../../holdouts/1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_---0RE/README.md)

*reduced, outlook probviously-nonhalting, table set T57*

- **Map:** Phases E(x,z) = E>0 (10)^x 1^z, R(x,y) = (10)^x 1^y C>0, Q(m,k,t) = (10)^m 1 A>0 0 (10)^k 1^t; 18-case map next, main moves E(x,z) -> E(2x+4, z-2x-6) (z >= 2x+7), R(x,y) -> R(x - floor(y/2) - 2, 2y+5), Q bounces (m,k,t) -> (m-b, k+2b, t-2b), R(0,y) -> E(0,y+1) (all ones).
- **Halts when:** Orbit reaches E(x,0) or E(x,1); only possible right after an all-ones tape 1^n C>0 with n fatal: for n < 10^5 exactly n = 0, 6 or 32*2^k - 2k - 12 (20, 50, 112, 238, ...).
- **From blank tape:** R(0,2) at step 2
- **Proved:** halts_iff and next_sound in lean/Phases.lean (kernel); no_halt_phases (10^8 phases) and fatal_list for n < 10^5 by native_decide; even_next/even_safe (kernel).
- **Checked:** 10^11 phases in C (~4.1e30 steps, 30 all-ones tapes, none fatal, trusted); 10^8 phases native_decide (~4.1e21 steps).
- **Odds:** not quantified; needs an all-ones length to land exactly in a sparse list (about one value per doubling)
- **Next step:** Prove the fatal-length list for every n (beyond 10^5); then only the number-theoretic question of all-ones lengths remains.

### [`1RB1LF_0RC1RD_1LA1LD_1LE0RA_---1LC_0LA1LA`](../../holdouts/1RB1LF_0RC1RD_1LA1LD_1LE0RA_---1LC_0LA1LA/README.md)

*reduced, outlook probviously-nonhalting, table set T287*

- **Map:** Round start A>0 1^a 0 1^c (a even, a >= 4, c >= 6). c even: (a-c+12, 3c-6) if c <= a+8; halt if c = a+10, a+12; (c-a-10, 3a+27) if c >= a+14. c odd: (a-c-1, 3c+6) if c <= a-5; halt if c = a-1, a-3; (c-a+3, 3a) if c > a.
- **Halts when:** Halts iff the orbit from (74, 30) hits c - a = 10 or 12 (c even) or a - c = 1 or 3 (c odd).
- **From blank tape:** (a, c) = (74, 30) at step 6,998
- **Proved:** halts_iff, orbit_dom, round_ok/round_halt in lean/Map.lean (kernel, no extra assumption).
- **Checked:** 10^6 rounds Python; 2e7 rounds GMP tools/c/redmaps.c (numbers ~6.1e6 bits); no Lean orbit evaluation stated; region-memo run to 9.15e96987 steps.
- **Odds:** sum of 4/c_k over the orbit: astronomically small
- **Next step:** none: pure number theory.

### [`1RB1LF_1LC0RD_---1LA_0LA0RE_1LA1RA_1LB0LD`](../../holdouts/1RB1LF_1LC0RD_---1LA_0LA0RE_1LA1RA_1LB0LD/README.md)

*reduced, outlook halts-late, table set T288*

- **Map:** Round start D> 0 0 111 0 1^n T (tail word T): n -> n' = 4*floor((n-1)/3) + d, with (d, T') computed from T and c = (n-1) mod 3 alone by a Lean simulator roundMap (e.g. T empty or 011: d = 11 (T kept) or 7 (next tail, c=1); T = 010111, c != 1: d = 19, T' empty).
- **Halts when:** Halts iff the orbit of roundMap from (11, empty tail) reaches a halting (tail, c) round (given it never answers stuck); shortest halting tail has blocks 2,1,1,1,2, 36 rounds (29 pushes) from empty.
- **From blank tape:** n = 3, empty tail at step 51; orbit starts at (11, empty)
- **Proved:** halts_iff in lean/Reduction.lean (kernel; hypothesis: orbit never stuck), round_next/round_halt, arun_sound in lean/Zone.lean, halting_round in lean/Round.lean.
- **Checked:** 500 rounds kernel; 2x10^6 rounds Python (n has 249,880 digits, never stuck); rleaccel 1.13x10^46615 steps trusted.
- **Odds:** ~10^-18 to 10^-13 per excursion; expected halt after ~10^13-10^18 rounds (~10^-15 per round)
- **Next step:** Prove the never-stuck hypothesis in general (or along the orbit) so the halts-iff is unconditional; the rest is a Collatz-type question.

### [`1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC`](../../holdouts/1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC/README.md)

*reduced, outlook no-halt-route, table set T56*

- **Map:** Step starts W A> 0 b^N 1 (b = 110, W a wall word): (W,N) -> (W', (3N + c)/2), W' and c depending only on W and N mod 2; computed by a Lean-verified zone simulator (stepMap), not by closed formulas. Observed: wall = stack of counters K(k) = b^k 1^3 b 1 (open), K'(k) = b^k 1^6 (closed), each ~3k/2 per odd parity.
- **Halts when:** Orbit reaches a halting step (needs A> 0 111); no halting wall is known.
- **From blank tape:** 11101101111101 A> 0 b^48 1 at step 10,206; after 5 steps wall 1, N = 468 (step 1,133,743)
- **Proved:** halts_iff in lean/Reduction.lean (kernel), under the hypothesis that stepMap never answers stuck along the orbit; halts_of_orbit/not_halts_of_orbit unconditional; first_steps: 40 orbit steps by kernel.
- **Checked:** 40,000 steps of the Lean step map (N 23,405 bits, never stuck) and 300,000 of the plain map (N ~175,000 bits), trusted; 6.38e43391 steps rle and 1.15e203321 region-memo accelerator (trusted); 40 steps kernel.
- **Odds:** not stated; no halting mechanism known
- **Next step:** Remove the never-stuck hypothesis of halts_iff and prove the stack-of-counters description, then look for a closed wall language without A> 0 111.

### [`1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_---1LC`](../../holdouts/1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_---1LC/README.md)

*reduced, outlook probviously-nonhalting, table set T292*

- **Map:** Doubling map op on (c,u,v) (u = b+1, v = a/2+b+2 for S(c,a,b) = (10)^c 1^a 0 (10)^b 1 B>0): 2u < v: (c, 2u, v+1); else if c >= 1: 2u = v -> (c-1, 1, v+2), else (c-1, 2u-v, v+1); if c = 0 (reset): (2(v-u-1), 2u-v, 2u-v+3), halt if 2u = v.
- **Halts when:** A reset (c = 0) with 2u = v exactly (b = a/2): opIter n (0,2,5) = none.
- **From blank tape:** (c,u,v) = (0,2,5); visit S(0,4,1) at step 43
- **Proved:** halts_iff_op in lean/Doubling.lean and halts_iff in lean/Map.lean (kernel).
- **Checked:** 10^7 operations native_decide (10^4 kernel); 10^11 operations in C (54 resets, far beyond 10^30 steps); rleaccel 1.89x10^22 steps.
- **Odds:** ~10^-10 for a later halt
- **Next step:** none: pure number theory (resets are logarithmically rare: reset k needs ~1.47^k operations).

### [`1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA`](../../holdouts/1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA/README.md)

*reduced, outlook probviously-nonhalting, table set T293*

- **Map:** Antihydra walk on (p,a), Q(p,a,b) = 0^inf 1^p 0 1^a 0 1^b B> 0^inf: (p, 2k+1) -> (p+2, 3k+4); (p, 2k) -> (p-1, 3k+2) for p >= 1. With x = a+5: x -> floor(3x/2), p +2 for x even, -1 for x odd.
- **Halts when:** Orbit meets an even a with p = 0 (counter would drop below 0).
- **From blank tape:** (p,a) = (2,7), Q(2,7,2) at step 62
- **Proved:** halts_iff in lean/Macro.lean (kernel), with nxt_sound and nxt_halt; sweep rules in lean/Rules.lean.
- **Checked:** 10^6 walk steps Python (p ends at 498,505, a 584,967 bits, trusted); 1.60e203416 steps region-memo and 2.05e41681 rle accelerator (trusted).
- **Odds:** about 0.618^500000 (phi^-(p+1) with p ~ 500,000)
- **Next step:** none: pure number theory (Mahler-type 3/2 parity question).

### [`1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE`](../../holdouts/1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE/README.md)

*reduced, outlook probviously-nonhalting, table set T127*

- **Map:** next(i,j,J) on two blocks of 1s (R1: J=false, R2: J=true): j+2 <= i: (i-j-1, 3j+2 [J false] or 3j+3 [J true], J); i = j+1: J false -> (3i-3, 3, true), J true -> (3i, 1, false); i+2 = j: J false -> (3i+3, 1, false), J true -> (3i+3, 3, true); otherwise (j > i+2): (j-i-2, 3i+3 [false] or 3i+5 [true], !J).
- **Halts when:** Orbit reaches i = j or i + 1 = j.
- **From blank tape:** (3,1,R1) from blank tape
- **Proved:** halts_iff in lean/Round.lean (kernel), every round by round_ok (lean/Round.lean, pieces in lean/Pieces.lean).
- **Checked:** 2x10^7 rounds GMP in C (numbers ~6.1x10^6 bits); 10^6 rounds Python; Quick_Sim 1.12x10^2004 steps; region-memo 1.86x10^100539 steps.
- **Odds:** ~2^-n per round with n-bit numbers; expected future hits negligible
- **Next step:** none: pure number theory

### [`1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD`](../../holdouts/1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD/README.md)

*reduced, outlook probviously-nonhalting, table set T127*

- **Map:** Round starts P(u,v) = C> 0 11 0 (11)^u 0 (11)^v and Q(u,v) (one more 11 0): P(u,v) -> P(3u+2, v-u-1) if u < v, Q(3v+3, u-v-2) if u >= v+2; Q(u,v) -> Q(3u+3, v-u-1) if u < v, P(3v+5, u-v-2) if u >= v+2 (subtract the smaller, triple it).
- **Halts when:** Orbit reaches u = v or u = v + 1.
- **From blank tape:** P(3,0) at step 42
- **Proved:** halts_iff and halts_iff' in lean/Reduction.lean (kernel), rounds in lean/Macro.lean; first_rounds: 10,000 rounds by kernel.
- **Checked:** 2*10^7 rounds GMP C (numbers ~6.1*10^6 bits, trusted); 3*10^6 rounds Python; 10,000 rounds kernel.
- **Odds:** ~2^-300000 (one claim says ~2^-900000 after the computed rounds)
- **Next step:** none: pure number theory.

### [`1RB1RC_1LC1LE_1RA1RD_0RF0RE_1LA0LB_---1RA`](../../holdouts/1RB1RC_1LC1LE_1RA1RD_0RF0RE_1LA0LB_---1RA/README.md)

*reduced, outlook probviously-nonhalting, table set T309*

- **Map:** R(n, m) = A> 0 11 (01)^n 0 11 (01)^m: even n -> R(3n/2+2, m+2); odd n, m >= 1 -> R((3n+7)/2, m-1); odd n, m = 0 -> Z((3n+9)/2); Z(k) = A> 0 11 (01)^k: odd k -> R((3k+1)/2, 1), even k halts.
- **Halts when:** Halts iff the orbit from Z 1 reaches Z k with k even (the counter falls below zero).
- **From blank tape:** Z 1 at step 10
- **Proved:** halts_iff and halts_iff' in lean/Reduction.lean, round and round_halt in lean/Macro.lean (kernel).
- **Checked:** 10,000 rounds kernel (first_rounds, n ~5,800 bits); 10^5 rounds Python (counter 50,008, never below 1); 4.62e179118 steps region-memo.
- **Odds:** ~10^-11 (random walk +2/-1 falls from m with chance phi^-(m+2))
- **Next step:** none: pure number theory (Antihydra-like).

### [`1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_---0RE`](../../holdouts/1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_---0RE/README.md)

*reduced, outlook probviously-nonhalting, table set T57*

- **Map:** E(x,z) = E> 0 (10)^x 1^z, A(x,y) = (10)^x 1^y A> 0, bounce frame Q(m,j,t): left phase E(x,z) -> E(2x+4, z-2x-6) (z >= 2x+7); right phase A(x,y) -> A(x-y/2, 2y+2) (y even, 2x >= y+2); 21 cases in Lean's next. Halts only right after an all-ones tape 1^n A> 0.
- **Halts when:** Halts iff next from A(0,0) reaches E(x,0) or E(x,1); this happens only from an all-ones tape A(0,n) with n = 1 or n = 12*2^k - 2k - 9 (3, 13, 35, 81, 175, ...).
- **From blank tape:** A(0,0) = blank tape
- **Proved:** halts_iff, next_sound, even_next in lean/Phases.lean (kernel); ones_fatal_all / ones_safe_all in lean/Fatal.lean (kernel).
- **Checked:** 10^8 phases native_decide (~4.1x10^21 steps); 10^11 phases in C (~4.1x10^30 steps), all-ones lengths up to 44,891,446 (+5 later), none fatal.
- **Odds:** 'very probably never halts': all-ones moments get rarer (~1/w) and must hit a doubling list; no number given
- **Next step:** none: pure number theory

### [`1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE`](../../holdouts/1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE/README.md)

*reduced, outlook probviously-nonhalting, table set T57*

- **Map:** 25-case phase map next on E(x,z) = E>0 (10)^x 1^z, A(x,y) = (10)^x 1^y A>0, Q(m,j,t) = (10)^m 1 D>0 0 (1010)^j 1^t; main cases E(x,z) -> E(2x+4, z-2x-6) (z >= 2x+7), A(x,y) -> A(x-y/2-2, 2y+6) (y even, 2x >= y+4). Coarse: all-ones tape 1^n A>0 -> E(3, n-2), x -> 2x+4 until the ones run out.
- **Halts when:** Iterate reaches E(x,0) or E(x,1); in practice an all-ones tape 1^n with n = 3 or 28*2^k - 2k - 13 (15, 41, 95, 205, ...) (native-checked n < 10^5; README probes also list 29).
- **From blank tape:** A(0,0) (blank tape)
- **Proved:** halts_iff and next_sound in lean/Phases.lean (kernel); even_next/even_safe parity classes (kernel); fatal_list for n < 10^5 (native_decide).
- **Checked:** 10^8 phases native_decide (~4.1x10^21 steps); 10^11 phases in C (~4.1x10^30 steps); all-ones moments up to n = 23880729, none fatal.
- **Odds:** 'very probably never halts' (not quantified)
- **Next step:** Prove the fatal all-ones list for all n in Lean (reducing to a 1-variable map on all-ones lengths), then iterate that map far.

### [`1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_---0RE`](../../holdouts/1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_---0RE/README.md)

*reduced, outlook probviously-nonhalting, table set T311*

- **Map:** Phases E(x,z) = E>0 (10)^x 1^z, R(x,y) = (10)^x 1^y 0 B>0, Q(m,k,t) = (10)^m 1 D>0 0 (10)^k 1^t; 24-case map next, main moves E(x,z) -> E(2x+4, z-2x-6) (z >= 2x+7), R(x,y) -> R(x - (y+3)/2, 2y+5) (y odd), all-ones 1^n 0 B>0 -> E(1, n+1).
- **Halts when:** Orbit reaches E(x,0) or E(x,1); only right after an all-ones tape 1^n 0 B>0 with n fatal: for n < 10^5 exactly n = 0 or 20*2^k - 2k - 12 (8, 26, 64, 142, 300, ...).
- **From blank tape:** R(0,2) at step 6
- **Proved:** halts_iff and next_sound in lean/Phases.lean (kernel); no_halt_phases (10^8 phases) and fatal_list for n < 10^5 by native_decide; even_next/even_safe (kernel).
- **Checked:** 10^11 phases in C (~4.1e30 steps, 8 more all-ones tapes after the Lean bound, none fatal, trusted); 10^8 phases native_decide (~4.1e21 steps).
- **Odds:** not quantified; needs an all-ones length to land exactly in a sparse list (about one value per doubling)
- **Next step:** Prove the fatal-length list for every n (beyond 10^5); then only the number-theoretic question of all-ones lengths remains.

### [`1RB1RD_1LC0RD_1RF1RB_1LE0RA_0LB0LE_---0RC`](../../holdouts/1RB1RD_1LC0RD_1RF1RB_1LE0RA_0LB0LE_---0RC/README.md)

*reduced, outlook probviously-nonhalting, table set T314*

- **Map:** C(k,a,b) = 0^inf (10101)^k C> 0 1 0 1^a 0 1^b 0^inf under DeepMind's map next. Rounds on E n = B> 0 0 1^n or (a,b): even n: E(2p+4) -> E(5p+11) (n -> 5n/2 + 1); odd blocks divided by 6 digit by digit. One block, n = 6^j m + (6^j - 1)/5: m = 0 (repunit) halts; m even -> n + 3m/2 + 1 + j; m = 3 mod 6 -> n + 3 + j; m = 6q+5 -> (n - q + 1 + j, q + 1).
- **Halts when:** Halts iff the orbit of next from C(0,2,0) reaches none: a round halts only at top level with remainder 1 and nothing after (base-6 repunit-like block), or nested with remainder 5 and nothing after.
- **From blank tape:** C(0,2,0) at step 10; rounds 2, 6, 16, 41, (36,7), 106, ...
- **Proved:** halts_iff and step_state in lean/DMMap.lean (kernel, standard axioms, independent of DeepMind's proof); even_round and reaches_26041 in lean/Macro.lean.
- **Checked:** 1,000,000 rounds of the round map Python (block ~205,000 digits); direct sim to E 326796 (3.4x10^10 steps); rleaccel 1.12x10^14319 steps trusted.
- **Odds:** ~6^-D per round for D-digit blocks; summed 'astronomically small'
- **Next step:** none: pure number theory

### [`1RB1RE_1LC0RA_0RD1LB_---1RC_1LF1RE_0LB0LE`](../../holdouts/1RB1RE_1LC0RA_0RD1LB_---1RC_1LF1RE_0LB0LE/README.md)

*reduced, outlook probviously-nonhalting, table set T318*

- **Map:** Samples W p 0 r = 0 (10)^p 0 1^r E> 0 (r >= 1): r >= p+2: (p,r) -> (2p+2, r-p-1); r = p: -> (2, 4p+1); r < p: -> (p-r, 4r+2); r = p+1 halts.
- **Halts when:** Orbit reaches r = p + 1.
- **From blank tape:** (p,r) = (2,1) (W 2 0 1 at step 27)
- **Proved:** halts_iff_orbit in lean/Map.lean (kernel, no native_decide), map_step there.
- **Checked:** 3x10^7 map steps GMP in C (~6.5x10^6 bits); 3x10^6 Python (> 2^600000 steps); Quick_Sim 1.41x10^14109 steps.
- **Odds:** far below 2^-100000
- **Next step:** none: pure number theory

### [`1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_---0LE`](../../holdouts/1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_---0LE/README.md)

*reduced, outlook probviously-nonhalting, table set T38*

- **Map:** Samples S(n) at the left end: n -> 3n - 2c_i + i + 3 for c_i < n < c_{i+1}, c_i = 10*2^i - i - 7 (thresholds 3, 12, 31, 70, 149, ...). Lean defines next n = ph (n-1) 0 0 (recursive); the closed form is checked for n < 10,000 and derived level by level, not proved in Lean.
- **Halts when:** Orbit lands exactly on a threshold n = c_{i+1}.
- **From blank tape:** n = 1 (S 1 at step 4); orbit 1, 7, 18, 34, 45, 78, 100, 166, ...
- **Proved:** halts_iff_orbit in lean/Phase1.lean (kernel, no native_decide), with ph_spec and round rules in lean/Rules.lean, lean/Phase2.lean.
- **Checked:** 8*10^6 map steps GMP C (n 5,332,435 bits, trusted); 1.25*10^6 Python; 1.12e3085 steps region-memo accelerator.
- **Odds:** about 1/(10*2^i) per step; expected future hits far below 2^-100000
- **Next step:** none: pure number theory (optionally prove the closed form equals ph in Lean).

### [`1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_---1RA`](../../holdouts/1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_---1RA/README.md)

*reduced, outlook probviously-nonhalting, table set T320*

- **Map:** Tape as list of runs of 1s (u = run of length 1); visit map on lists between left-end visits: sweep [X, 4, u^(n+2), R] -> [X+6, 4, u^n, R]; conversion [2x+8, u^(k+2), R] -> [6, 4, u^x, 4, u^k, R]; plus 8 visit shift rules. Effectively a unit counter m' = 3m/2 + d (d in {-2,+1,+4} m even, {-1/2,+5/2} m odd) whose parities drive a stack of slower counters.
- **Halts when:** Halts iff the orbit of [12, 1^9] reaches a list in which every run is even (the first after adding 2); requires the whole stack to be used up.
- **From blank tape:** [12, 1^9] at step 423
- **Proved:** halts_iff, visit_step, scan_none_iff in lean/Visit.lean (kernel); halts_iff_edge in lean/Edge.lean.
- **Checked:** 10^7 steps native_decide; 260,000 epochs exact run-list simulator Python (~10^91568 steps).
- **Odds:** stack emptying chance negligible: head passes >= 5 stack entries in 0.04% of epochs while the stack gains 0.28 entries per epoch
- **Next step:** none: pure number theory (an invariant keeping some run odd would decide it; none known beyond the parity of the count of even runs).

### [`1RB1RE_1LC1LD_---1LA_1LB1LE_0RF0RA_1LD1RF`](../../holdouts/1RB1RE_1LC1LD_---1LA_1LB1LE_0RF0RA_1LD1RF/README.md)

*reduced, outlook halts-late, table set T321*

- **Map:** P c u x = 0^inf 1^c (01)^u 0 0 (10)^x F> (u = 2 or 3): phase P(c+4) u x -> P c u' x' with X = x+u+4, u' = 2 + X mod 2, x' = 3*floor(X/2) - 1. Epoch end at r = c mod 4: r = 3 -> P(2x+4+2u) 3 5; r = 0, u = 3 or r = 1, u = 2 -> P(2x+5) 3 5; else halt. Epochs start at P c 3 5.
- **Halts when:** Halts iff epochs k = none for some k: an epoch ends with r = 2, or r = 0 with u = 2, or r = 1 with u = 3.
- **From blank tape:** P 3 3 5 at step 139 (epoch 0: c = 3); epochs c = 3, 20, 297, 459271258863231
- **Proved:** halts_iff, epochs_first, epochs_4 in lean/Phase.lean (kernel).
- **Checked:** Epochs 0-3 evaluated by the kernel (no halt before end of epoch 4); simulator agreement to ~10^114 steps; rleaccel 2.61x10^49522 steps trusted.
- **Odds:** halts at end of epoch 4 with probability 3/4, eventually with probability 1
- **Next step:** none feasible: the epoch-4 end needs parities after 1.1x10^14 steps of X -> floor(3X/2)+5 on ~10^13-digit numbers (~10^27 bit operations).

### [`1RB1RF_1LC---_1LE1RD_1RA0RC_0LF0LA_0LD0RB`](../../holdouts/1RB1RF_1LC---_1LE1RD_1RA0RC_0LF0LA_0LD0RB/README.md)

*reduced, outlook probviously-nonhalting, table set T63*

- **Map:** A(n,k), D(n,k) at 1^n (01)^k 111: n even: s(n,k) -> other(n+4,k-1) (k=1: other(n+7,0); k=0: other(n+3,0)). n odd: A(n,0) -> D(1,(n+1)/2), D(n,0) -> D(3,(n+1)/2); k >= 2: 2k > n+5: D -> D(2n+7, k-(n+5)/2), A -> A(2n+6, k-(n+5)/2); 2k = n+5: all ones of length 2n+10 (D) / 2n+9 (A); 2k < n+5: other(n-2k+6, 2k); k = 1 halts.
- **Halts when:** Halts iff the orbit of D(3,0) reaches A(n,1) or D(n,1) with n odd; along the orbit equivalently D(n, (n+7)/2) with n odd one step earlier (the latter read off the map, not in Lean).
- **From blank tape:** D(3, 0) at step 11
- **Proved:** halts_iff, halts_iff_state, map_step in lean/Map.lean, rows in lean/MapRules.lean (kernel).
- **Checked:** 8,598 epochs Python (>10^3100 steps); 40,000 epochs GMP c/emap.c (N 47,748 bits); no Lean orbit evaluation stated.
- **Odds:** ~2/n per doubling stage; around 2^-10000 past the epochs followed
- **Next step:** none: pure number theory.

### [`1RB1RF_1LC1LF_0RE1LD_0LB1LD_---1RC_1RA0RD`](../../holdouts/1RB1RF_1LC1LF_0RE1LD_0LB1LD_---1RC_1RA0RD/README.md)

*reduced, outlook probviously-nonhalting, table set T125*

- **Map:** Pass starts PS a c = 0^inf B> 0 0 (10)^a 1^c and frames Q R m c; plain pass (a,b) -> (2a+2, b-2a-2) for a >= 2, b >= 2a+3, with rebound cases off the right end (e.g. Q 0 (m+2) (c+5) -> PS (m+4) (c+1), PS 0 (c+3) -> PS 2 (c+1)); Lean's next covers all cases.
- **Halts when:** Halts iff some iterate of next from PS 0 2 is PS a c with c <= 1 (a pass ending with b = 0).
- **From blank tape:** PS 0 2 at step 4
- **Proved:** halts_iff, next_sound in lean/Phases.lean (kernel); pass_plain in lean/Pass.lean.
- **Checked:** 10^8 phases native_decide (2x10^7 passes); 10^8 passes Python; 10^11 phases in C (2x10^10 pass starts), closest c = 2.
- **Odds:** each even-b stretch hits 0 with chance of order 1/width; gets rarer as the tape grows (no number given)
- **Next step:** none: pure number theory
