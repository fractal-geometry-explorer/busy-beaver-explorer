# NGramCPS on the holdout

The n-gram Closed Position Set decider (NGramCPS) is the workhorse of the Coq-BB5 proof (*Determination of the fifth
Busy Beaver value*, arXiv 2509.12337, Section 4.4): it decides 99.89% of the nonhalting five-state machines that are
not loops. This folder runs it on `1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LD1RE` from blank tape at every practical
window width, with and without the paper's two tape augmentations, and explains why it fails.

**In short.** Every run fails, at every width, the same way: the decider's abstract run reaches the machine's only
halting move, a packet carried left meeting a block (`0 1 1 A>1 1`, then A1 E1 B0 C1 D1 and D reads 1). The real run
never does this, because blocks are always to the right of the packet. That ordering holds across stripes `1010…`
hundreds or millions of cells long, and a window of n cells sees nothing beyond the stripe it sits in. The failure
is not an accident of the order in which the decider explores: for every width up to at least 1,000, a
**twin tape** proves that NGramCPS must fail. The twin is a configuration that halts (a theorem in `../lean/thm`), and
every one of its windows of that width occurs in the machine's own run from blank tape, so the decider cannot tell
the twin from the run. The twins are round starts whose marks sit at distances the machine never produces. Whether
the machine halts depends on those distances modulo high powers of 2, the 2-adic residues of the wall positions
(`../lean/END_TO_END.md`, "Deeper trees", and `../integ/INTEGRALITY.md`), and no window can see them.

## The decider

`../../tools/c/ngramcps.c` is Algorithm 2 of the paper for any two-symbol machine, with separate left and right window
widths (`NL`, `NR`) and the two augmentations of Section 4.4.2: a fixed-length history (`-H LEN`: each cell also holds
the last `LEN` (state, bit) pairs read on it) and Least Recent Usage (`-U`: every pair read on it, most recent first).
The paper's loop that revisits every configuration until nothing changes is replaced by an equivalent worklist: a
step that needs an n-gram with given known cells waits on that key, and is completed by every n-gram with that key,
now and whenever a new one is recorded. The closure is the same set. Configurations are processed in breadth-first
order and the decider stops at the first halting one, as the paper's does.

The C program is tested against `../../tools/py/bbtools/ngramcps.py`, a line-by-line transcription of the paper's
pseudo-code, on random machines in all three modes: same result, and the same closed set whenever the answer is
NONHALT. It is also tested on the paper's examples: the translated cycler of Figure 7 is decided, and the machine of
Figure 8 is decided by LRU but not by the plain or fixed-history decider, as the paper says (`TestNGramCPS` in
`../../tools/tests/test_tools.py`).

```sh
gcc -O2 -o ngramcps ../../tools/c/ngramcps.c
./ngramcps 1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LD1RE 12 -w deriv.txt -s 20000000   # widths 12/12, plain
./ngramcps 1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LD1RE 8 -H 2                         # fixed history of 2
python3 run.py OUT plain        # the sweeps below (plain | history | lru | asym | all) -> OUT/results.tsv, OUT/deriv/
python3 analyze.py OUT          # how each derivation reaches the halt
python3 twin.py OUT2            # the twin certificates
```

On a halt, `-w` writes the **derivation**: the chain of local configurations from the blank one to the halting one,
one machine step apart. For each step it gives the n-gram glued in at the far end of a window and the configuration
that first recorded that n-gram. With `-s STEPS` the machine is also run directly from blank tape, and each
configuration of the chain is marked `real` (it occurs in that run) or `UNREAL`.

## The runs from blank tape

All runs were on a 4-core container with 15 GB of memory, with the limit of 60 million local configurations
(25 million for the augmented runs). Time and memory are for the decider alone, without the direct run used for the
real/unreal marks.

**Plain, equal widths** (`results/plain.tsv`): every width from 1 to 38 reaches a halting local configuration (UNKNOWN).
Width 39 passed 60 million configurations (5.3 GB, 74 s) without reaching one, so that is where "practical" ends with
this memory. The cost does not grow smoothly with the width, because the decider stops at the first halt it finds:

| n | result | configurations | left/right n-grams | seconds | peak MB | derivation (steps) | first unreal step |
|---|---|---|---|---|---|---|---|
| 1 | UNKNOWN | 20 | 2/2 | 0.00 | 13 | 3 | 2 |
| 2 | UNKNOWN | 103 | 4/4 | 0.00 | 13 | 14 | 10 |
| 3 | UNKNOWN | 265 | 8/8 | 0.00 | 13 | 30 | 15 |
| 4 | UNKNOWN | 335 | 16/10 | 0.00 | 13 | 22 | 16 |
| 5 | UNKNOWN | 2,724 | 31/32 | 0.00 | 13 | 52 | 23 |
| 6 | UNKNOWN | 9,320 | 61/64 | 0.00 | 13 | 131 | 36 |
| 7 | UNKNOWN | 26,978 | 104/128 | 0.01 | 13 | 93 | 41 |
| 8 | UNKNOWN | 67,081 | 177/243 | 0.02 | 13 | 170 | 73 |
| 9 | UNKNOWN | 147,960 | 279/445 | 0.04 | 18 | 301 | 69 |
| 10 | UNKNOWN | 107,610 | 335/508 | 0.03 | 13 | 216 | 36 |
| 11 | UNKNOWN | 210,883 | 477/793 | 0.06 | 25 | 479 | 338 |
| 12 | UNKNOWN | 138,523 | 524/820 | 0.04 | 19 | 508 | 327 |
| 13 | UNKNOWN | 126,223 | 571/752 | 0.05 | 13 | 319 | 167 |
| 14 | UNKNOWN | 304,611 | 838/1264 | 0.13 | 36 | 571 | 347 |
| 15 | UNKNOWN | 565,150 | 1156/1746 | 0.22 | 72 | 662 | 356 |
| 16 | UNKNOWN | 425,112 | 1098/1505 | 0.17 | 48 | 564 | 355 |
| 17 | UNKNOWN | 469,207 | 1229/1654 | 0.18 | 48 | 845 | 477 |
| 18 | UNKNOWN | 1,058,486 | 1823/2729 | 0.53 | 140 | 805 | 468 |
| 19 | UNKNOWN | 606,041 | 1578/1954 | 0.27 | 73 | 923 | 579 |
| 20 | UNKNOWN | 643,931 | 1678/2009 | 0.29 | 73 | 976 | 746 |
| 21 | UNKNOWN | 674,918 | 1834/2207 | 0.33 | 89 | 1275 | 733 |
| 22 | UNKNOWN | 2,141,237 | 2708/4055 | 1.20 | 280 | 1725 | 857 |
| 23 | UNKNOWN | 2,432,189 | 3089/4652 | 1.97 | 289 | 1098 | 563 |
| 24 | UNKNOWN | 2,679,742 | 3293/4905 | 2.07 | 347 | 1774 | 856 |
| 25 | UNKNOWN | 3,161,457 | 3752/5372 | 3.09 | 355 | 1297 | 857 |
| 26 | UNKNOWN | 9,195,195 | 5770/10323 | 7.13 | 1,073 | 2122 | 856 |
| 27 | UNKNOWN | 10,472,690 | 6548/11341 | 9.25 | 1,105 | 1430 | 857 |
| 28 | UNKNOWN | 9,653,014 | 6767/9591 | 7.07 | 1,107 | 1825 | 983 |
| 29 | UNKNOWN | 19,135,143 | 9821/14843 | 21.20 | 2,189 | 2258 | 857 |
| 30 | UNKNOWN | 19,671,277 | 10161/15152 | 20.46 | 2,148 | 2537 | 856 |
| 31 | UNKNOWN | 10,672,374 | 8119/9709 | 9.90 | 1,376 | 2316 | 1053 |
| 32 | UNKNOWN | 9,655,635 | 7991/8644 | 7.97 | 1,111 | 2052 | 1025 |
| 33 | UNKNOWN | 10,758,223 | 8757/9283 | 9.27 | 1,373 | 3023 | 961 |
| 34 | UNKNOWN | 26,426,682 | 13104/17012 | 29.13 | 2,684 | 4080 | 2830 |
| 35 | UNKNOWN | 31,775,414 | 13914/19904 | 35.32 | 2,708 | 4518 | 2829 |
| 36 | UNKNOWN | 32,410,445 | 14379/19889 | 34.23 | 2,734 | 4489 | 2830 |
| 37 | UNKNOWN | 37,483,330 | 15494/22005 | 48.53 | 4,305 | 3828 | 2829 |
| 38 | UNKNOWN | 49,411,305 | 17704/26599 | 70.78 | 5,308 | 3880 | 2920 |

**Unequal widths** (`results/asym.tsv`): all 240 pairs NL ≠ NR with 1 ≤ NL, NR ≤ 16 are UNKNOWN.

**Fixed-length history** (`results/history.tsv`), history lengths 1 to 8, widths from 1 up to the configuration
limit: every run that finished is UNKNOWN. Length 1 at widths 1 to 29, length 2 at
1 to 36, length 3 at 1 to 38 (the next width passed 25 million configurations each time, 2.7 GB), length 4 at 1 to 20,
lengths 5 to 8 at 1 to 16.

**LRU history** (`results/lru.tsv`): UNKNOWN at widths 1 to 11, the costliest at width 8 (75.7 million
configurations, 90 s, 8.3 GB); width 12 passed 90 million (8.5 GB, 106 s). LRU symbols multiply fast: 605,223 distinct
left n-grams at width 12, against 19,703 for the plain decider at width 39.

So no variant of the decider in the paper proves this machine nonhalting at any width that can be run here.

## How each run reaches the halt

`analyze.py` reads the derivations (`results/analysis.md`). Three things hold at every width.

1. **The halt is always the packet meeting a block.** From width 4 on (width 3 with a history), the last five local
   configurations are A1 E1 B0 C1 D1, with left window `…011` and head symbol 1: the packet `11`, carried left in
   state A, finds a block `111` directly on its left (`0 1 1 A>1 1`). In the mark rules (`../notes/LAB_NOTES.md`, "The
   rules") this is PACKET→block, the only rule that halts. At widths 1 to 3 the windows are too short to show the
   whole block, and the derivation ends with the same last moves (B0 C1 D1). All 477 derivations of the sweeps end
   this way.
2. **In the real run that never happens.** A block appears only where a shift ends, and the packet then starts from
   there going left. A pass or shift that reaches a block removes it. So blocks are always to the right of the
   packet ("Halting has exactly one route" in the notes), and the run from blank tape, followed with the proved
   rules to 1.6 × 10¹⁹ steps, never meets a contact that could change this. The fact is about the order of marks
   along the tape, and the marks are separated by stripes.
3. **The derivation leaves the real run by forgetting how long a stripe is.** The first configuration of the chain
   that the direct run never shows is a step into a window full of stripe: the decider glues in an n-gram in which
   the stripe stops (two equal cells) just beyond what the window can see. Width 29 at steps 847 to 857 shows how:

   ```
      847  00101010101010101010101010101 B1 10000000…   real   (the stripe being written at the right end, 27 cells, "00" before it)
      …
      856  01010101010101010101010101010 C1 10000000…   real   (the same stripe, now longer than the window)
      857  00101010101010101010101010101 D0 11000000…   UNREAL glued L 00101…01, recorded at #847
   ```

   At step 857 the head steps left out of a window that is all stripe, and the left n-gram it needs is any recorded
   one that continues the stripe. The one recorded at #847, ten steps earlier, when the same stripe was still short
   and began with `00`, fits. From then on the abstract tape is a stripe shorter than the real one, and the remaining
   1,400 steps of the derivation splice more such pieces until a block lies left of the packet. Over all 477
   derivations (`results/analysis.md`), the first departure is a window that is all stripe on the glued side in 200
   of them (126 where the glued cell ends the stripe, as here; 74 where it continues it); in the rest the window
   already holds a mark and the glued cell misplaces the next one. Either way it is the same thing: a recorded window
   reused where the real tape differs only beyond the window's reach.

## Why no width works: twin tapes

Write C, L and R for the closed sets the decider builds (local configurations, recorded left n-grams, recorded right
n-grams). By induction on the run from blank tape, they contain:

- every local configuration of that run;
- every left window the run has when it steps right (that is when Algorithm 2 records it);
- every right window the run has when it steps left;
- the blank n-gram.

Call a configuration X *covered* if three things hold: its local configuration is in C, its left window at every
position left of the head is in L, and its right window at every position right of the head is in R.

**A machine step keeps X covered.** Take a step to the right. The old left window goes into L. The new right window
is X's right window one cell further on, which is in R and agrees with the cells already known, so the new local
configuration is one of those the decider adds. A step to the left is the mirror image. So if a covered X halts,
C contains a halting local configuration, and the decider cannot answer NONHALT. This holds whatever the order of
exploration and whatever limits are used.

`../../tools/c/ngramtwin.c` checks that X is covered using only the run from blank tape. It collects the windows X
needs, as exact strings, and marks each one found when the run shows it at the right kind of step. Rolling hashes
find candidates, which are then compared cell by cell. Then it runs X to its halt. `twin.py` builds round starts from
the Lean examples (cells from 0: `1 0 0 E>0`, then stripes and walls `00` at the given positions, as `roundStart` in
`../lean/BB6/Marks.lean`) and bisects for the largest certified width. Covered at width n implies covered at every
smaller width, since a window's occurrence carries those of its sub-windows. The blank-tape run was 3 × 10⁹ steps
(tape width 5,129 cells):

| twin (Lean theorem) | walls, width | gaps (stripe to first wall, between walls, R) | halts after | certified for every n ≤ |
|---|---|---|---|---|
| `pass_r6_halt_example` (R = 6) | 743, 1,802, 3,319; 3,326 | 742, 1,059, 1,517, 7 | 11,362,210 | 8 |
| `pass_class_halt_example` (R = 48) | 731, 1,886, 5,603; 5,652 | 730, 1,155, 3,717, 49 | 72,326,042 | 108 |
| `family_open_halt` (R = 178) | 1,523, 2,010, 2,477; 2,656 | 1,522, 487, 467, 179 | 23,574,957 | 180 |
| `lane769_far` (δ, R = 998) | 449, 2,462, 15,193; 16,192 | 448, 2,013, 12,731, 999 | 974,052,281 | 1,000 |

So **NGramCPS fails on this machine at every width up to 1,000**, which is far beyond any width it can be run at.
A twin certifies a width only while no window of that width straddles a short gap. The R = 6 twin stops at 8, where a
right window holds both the last wall and the end of the tape, which the machine never writes that close together.
The δ twin of `lane769_far` has every gap at least 448, and its windows all occur in the run up to width 1,000, just past its right end R = 998. Larger twins exist in
the same families: `lane769_open_halt` takes any odd first wall a ≥ 448 and shifts b and W by any multiple of 2¹⁸ to
2⁴⁴ (`delta998`, one family per scale up to W − b = 2³⁰ − 2,654). The routes near R = 5,000 and γ's lane
(R = 55,918,886, `lane769_far_wide`) have right ends larger still. A twin built from them would need a longer
blank-tape run to show its windows, and a much longer run to reach its own halt.

**What this says about the machine.** The decider's sets are a finite description of which marks can sit next to
which, up to distance n. The twins have exactly the same neighbourhoods as the run (walls in long stripes, the gap
at the left end, the end marker after a long stripe). They differ only in how far apart the walls are. The machine's
fate depends on those distances. Whether a pass start closes is decided by b and W modulo 2^k, with k from 14 for the
R = 178 family to 44 at δ's largest scale (`lean/thm/PassOpenHalt.lean`, `LaneHalt.lean`), and the open clean-tape
classes each hold a 2-adic value of W/2 that no finite depth settles (`../lean/END_TO_END.md`). The research log had
already found this at the level of marks: "Every window language I tried still let in configurations that the run
never reaches, and some of those lead to a contact. They differ from real configurations only in distances between
marks that are far apart, which a fixed window does not see" (`../notes/LAB_NOTES.md`, "What is not proved").
`../../tools/py/bbtools/ctl.py`, which closes windows of K cells with a blank-tail letter, is the same kind of
invariant and fails for the same reason.

**The augmentations.** A history records which (state, bit) pairs last visited a cell. Inside a long stripe every
cell has seen the same sweeps, so the augmented stripe is again periodic, and a window inside it still cannot tell
its length. History cells do remember where marks used to be ("scars"). But the scars are local too, and the twin argument applies to augmented tapes as long as
the stripes between scars are longer than the window. The twin check here is for the plain decider only; for the
augmented ones the evidence is the runs above.

## Why the paper's other deciders do not apply

- **Loops** (Section 4.3) detects cyclers and translated cyclers: a run that repeats a configuration, or repeats one
  shifted at the edge of the tape, within L steps. This run does neither. Its clean tapes grow in width by an
  irregular recurrence (`../notes/LAB_NOTES.md`, "How the rules give the round recurrence"), the exhaustive check
  reaches widths 2⁶⁵ with ever-changing gaps, and a translated cycle would make the record-setting behaviour at the
  edge periodic forever.
- **RepWL** (Section 4.5) replaces a word repeated at least T times by `(w)^{T+}`. On this machine that is the stripe
  `(10…)^{T+}`: the same abstraction as a window, which keeps the marks and forgets the stripe lengths above a
  threshold, modulo the block length l. Its closed graph would contain the twins whose gaps differ from real ones by
  multiples of l. The halting families come in residue classes of b and W modulo 2^k at every width, so we expect the
  same failure. That is an argument, not a run.
- **FAR** (Section 4.6) looks for any regular language of configurations, closed backwards from the halts and
  rejecting the blank tape. A finite automaton reading a long stripe is eventually periodic, so it sees the stripe's
  length only above a threshold and modulo some period p. Separating the run from the twins would need p to carry
  ever higher powers of 2, since the halting families need b and W modulo 2^k for k up to 44 and beyond, at every
  scale. A regular certificate would amount to settling the open clean-tape classes with finitely many 2-adic
  digits, and the tree computations show that no fixed number of digits settles them (`../lean/END_TO_END.md`,
  "Deeper trees": the number of open classes at b digits stays put at every depth). This too is an expectation, not
  a run of FAR.
- **WFAR** (Section 4.7) adds integer weights to the automaton: a linear quantity that a step can change and whose
  sign rules out the halt. The quantity that matters here is arithmetic, a divisibility of distances by powers of 2.
  The lock study (`../lock/LOCK_NOTES.md`) found never-zero countdowns for the pure Q loop and for periodic words, but
  showed that mixtures have none, and that no such lock can settle the open cases.
- So the machine is what the paper calls a **sporadic machine**, one needing an individual proof, and the rest of
  this folder (`../README.md`) is the start of one.

## Files

| file | what |
|---|---|
| `../../tools/c/ngramcps.c` | the decider (plain, `-H`, `-U`; unequal widths; derivations; real/unreal marks) |
| `../../tools/py/bbtools/ngramcps.py` | the paper's pseudo-code transcribed, the reference for the tests |
| `../../tools/c/ngramtwin.c` | the twin certificate check |
| `run.py` | the sweeps over widths and augmentations |
| `analyze.py` | the halting move and the first departure from the real run, per derivation |
| `twin.py` | the twin round starts and the bisection for the largest certified width |
| `results/*.tsv` | the sweeps (`plain`, `asym`, `history`, `lru`) and the twin certificates (`twins.tsv`) |
| `results/analysis.md` | `analyze.py` on every derivation |
| `results/deriv/` | the derivations at widths 4, 12 and 29, plain |
