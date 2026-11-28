# 1RB0LF_0LC0RE_0RA1LD_1LB0LD_0RA1RC_1LA---

bbchallenge id 129771, a six-state holdout of group G05. **Open.** The tape is a binary counter on blocks
`(10)^D x`. Its phases grow by a Collatz-like 3/2 map. An exact block-level macro machine reproduces direct
simulation record for record. Every crossing rule it used in the first 300,000 records is proved in Lean (kernel), for
all block sizes and all surrounding tapes. The macro run finds no halt in 338,536,834,271,065 (3.39·10^14) steps, and a record-skipping version of it (`py/run_accel.py`) none in 8.86·10^40 steps (phase 106 of the reset map; the twin: phase 101, 2.59·10^39 steps). The reset map
X' = floor(3X/2) + 1 or + 3 is proved in Lean for the head part of the tape (`lean/ResetMap.lean`), so both this
machine and its twin halt only if a carry into the tail fails to come back. Every carry of the first 130 phases of both runs
is now checked in Lean (`lean/TailHashLong.lean`, `native_decide`, by Hashlife over the carries): this machine's run reaches the reset with
X ≈ 3.3·10^24 (about 6·10^49 steps), with no hypothesis. No invariant that excludes the halt in later phases is known.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LF |
| B | 0LC | 0RE |
| C | 0RA | 1LD |
| D | 1LB | 0LD |
| E | 0RA | 1RC |
| F | 1LA | --- |

## The tape at a left record

A *left record* is a moment when state B stands strictly left of every cell visited so far. Write
`P = 10`. At every left record the tape is

    0^inf  ell  B>c  P^D1 x1  P^D2 x2  P^D3 x3 ...  0^inf          x = i (1) or o (0)

Here `ell` is empty or a single 1, and `c` is 0 or 1 (`ell = 1, c = 1` occurs only right after a reset). The blank
right end is the same as an endless list of blocks `(0, o)`. The previous worker's separators fit this as follows:
`1^2 0` is `... P^D i  P^0 ...`, and `1 0^2` is an o-block.

In the first 10^5 records (a one-off scan of the macro run; heuristic):
- no block `(0, i)` appears after the first;
- the block after an o-block has D + x even;
- the first block has D + x odd, or `ell = 1, c = 1`, first block `(0, o)` and the second has D + x odd.

## One sweep

From the record, the head goes right. For blocks with D ≥ 8 it carries a phase bit, α (state A) or β (state B/E).
Crossing a block `P^D x` flips the phase when D + x is even. The sweep turns at the first o-block with D + phase
odd: α turns at an odd o-block, β at an even one. On the way out it re-encodes `1010` as `1100`. On the way back,
state B (or D) restores the blocks and changes the ones the counter changes. It then reaches the left end one cell
further out, which is the next record.

Most sweeps are of this kind (99.99% of macro steps: right crossings, one turn, left crossings). The rest bounce
several times on short blocks. The macro machine handles every pattern of bounces the same way; nothing is
special-cased.

The long sweep, for the common even case, is the theorem `carry_even` (`lean/Sweep.lean`, kernel, for all a, b, the
list ts and the tape R):

    0^inf B> 0 (1010)^(a+2) 1 10 1 [ (1010)^(t+4) 1 ]^ts 10 (1010)^(b+4) 0 R
      ->  0^inf B> 0 1 0 1 (0101)^a 0 1 0 0 0 1 0 1 0 1 [ (0101)^(t+3) 0 1 0 0 1 ]^ts 0 1 0 1 (0101)^(b+3) 0 1 1 0 R

In blocks this is one increment. The head pair `P^(2a+4) i P i` becomes `P^(2a+3) o o`. The even i-blocks of the
list become o-blocks, with +2 on the first. The odd o-block `P^(2b+9) o` becomes an i-block, and the block after it
gets +1. The short sweep that follows (`short`, `lean/Macro.lean`) restores the head pair.

## The block macro machine (`py/blockmm.py`)

`macro_step(ell, c, blocks)` maps a record to the next record exactly, or reports a halt.
- **Words.** The tape between the two records is a left stack and a right stack of *words*. A word is a token list
  with its own parameter t. A block with D < 8 is a literal word. Larger blocks are `(1010)^(t+4) x` (D even) or
  `10 (1010)^(t+4) x` (D odd).
- **Crossings.** The head is in a *situation*: moving right with the last 8 cells known, moving right on the blank
  side, or moving left with up to 1000 cells known on its right. Crossing a word of a given kind from a given
  situation is one `bbtools.symtm` run, valid for every t, and it is cached. The run either passes the word, turns
  inside it, reaches the record, or halts.
- **Normal form.** Between crossings, `normalize` rewrites words so every repeat count is at least 2, or writes the
  word out in full. At the record, `reparse` reads the cells back into P-blocks.
- **Rules.** The first 300,000 records use 111 right-crossing and 276 left-crossing rules. `py/gen_rules.py` writes
  each one as a Lean theorem (`lean/Rules.lean`, `right0` ... `right110`, `left0` ... `left275`). Each theorem is
  `steps n <start> = some <end>` for every t and every tape outside the known context.

What is **not** proved in Lean is the composition: that the Python bookkeeping (stacks, `normalize`, `reparse`)
glues the rules together correctly. That part is trusted Python. It is cross-checked against direct simulation:
`py/check_macro.py` compares steps, head cell and blocks at each of the first 15,144 records (3·10^8 steps). All
agree. It also reproduces the previous worker's C run exactly: record 300,000 at step 116,666,829,938.

## Phases and the reset map

The first block counts down by 2 per increment. When it runs out, the next blocks move down. Resets found by the
macro run (record, step, first two blocks after the reset):

| record | step | X | Y |
|---|---|---|---|
| 280 | 100,433 | 142 i | 53 o |
| 1,454 | 2,651,707 | 727 o | 337 i |
| 7,392 | 68,628,877 | 3,697 o | 1,810 o |
| 37,459 | 1,757,615,063 | 18,733 o | 9,314 o |
| 189,692 | 45,293,767,053 | 94,849 o | 47,362 o |
| 960,369 | 1,157,584,303,737 | 480,190 i | 240,019 o |
| 4,861,933 | 29,630,629,246,279 | 2,430,970 i | 1,215,401 o |
| 7,292,906 | 66,659,636,161,183 | 3,646,456 i | 1,823,142 i |
| 10,939,365 | 150,649,541,815,643 | 5,469,685 o | 2,734,754 o |
| 16,409,053 | 338,536,834,271,065 | 8,204,530 i | 4,102,173 o |

**Heuristic.** At every reset so far (27 of 27 transitions), X maps to X' = 3X/2 + 1 for even X and to
X' = (3X + 5)/2 for odd X. For example, 142 → 214 → 322 → 484 → 727 → 1093. Y follows Y' ≈ 3Y/2 + c, where c grows
slowly (8 ... 40). Each phase takes about 2.25 times as many steps as the one before. The parities of the blocks
decide the corrections, so the long-run behaviour is a Collatz-like question.

## The twin, and what the tail sees (21 Nov)

**One counter, two starts.** [`1RB0RA_0RC0LE_0LD1RA_1LB0RF_0LD1LC_1RD---`](../1RB0RA_0RC0LE_0LD1RA_1LB0RF_0LD1LC_1RD---/README.md)
is this table in a mirror, its states A to F renamed D, B, C, A, E, F. So its run is the run of this table started in
state D (`twin_halts_iff`, `lean/Twin29537.lean`, kernel). After 157 steps that run is at a left record
`0^inf B> 0 (10)^3 0 0 (10) 1 (10) 1 (10) 1 (10)`, blocks `(3, o) (0, o) (1, i) (1, i) (1, i) (1, ·)`
(`twin_reach157`, `twin_halts_iff_record`). From there the block macro machine of this folder reproduces it:
`py/twin.py` compares steps, head cell and blocks with a direct run at all 15,228 records up to step 299,972,981, and
all agree. The macro run of the twin finds no halt in 300,000 records (1.20·10^11 steps). It uses 56 right and 175
left crossing rules that this machine's own first 300,000 records do not use; they are proved for all t and all
tapes in `lean/RulesTwin1.lean` and `lean/RulesTwin2.lean` (kernel, written by `py/gen_rules_twin.py`). Everything in
this section holds for both machines.

**The countdown map, exactly.** Call X the long block after the first block `(0, o)` at a reset. The next reset has

    X' = floor(3X/2) + 1   (X even)        X' = floor(3X/2) + 3   (X odd)

`py/reset_map.py` checks this at every reset of a run. It holds at all of them: 13 transitions in this machine's
direct run to 3·10^7 steps, 19 in the twin's direct run to 3·10^9 steps, 34 in this machine's macro run to 3.4·10^14 steps and 33 in the twin's macro run (2·10^7 records, 2.5·10^14 steps, no halt). The map involves X only, and
the two machines are two orbits of it: 142, 214, 322, 484, 727, 1093, 1642, ... here, and 52, 79, 121, 184, 277,
418, 628, 943, ... for the twin. The reason is visible in the records: in a phase the countdown starts at X + 1 and
loses one per record, while the block after it starts again near 0 and gains 3 per increment (two records); so it
has about 3X/2 when the countdown runs out, and becomes the next countdown.

**What the tail sees.** At the `o o` records of a phase the tape is `0^inf B> 0 (D0, o) (0, o) (Y, x) T`. Call T the
tail. From one such record to the next (one increment), T changes in a way that depends only on Y mod 2 and x, not
on D0 or on the size of Y. So there are four operators on tails:

| operator | the block before T | what it does to the cells of T |
|---|---|---|
| E0 | Y even, x = o | lengthens the first block by one `10`, nothing else |
| E1 | Y odd, x = i | a carry: changes a few cells, sometimes hundreds of cells deep |
| O0, O1 | Y odd, x = o / Y even, x = i | another carry (the two give the same cells, parsed differently) |

`py/tail_ops.py` computes each one by a direct run of the machine on a constructed tape (D0 = 61, Y = 20 or 21) and
checks, on a direct run:
- the operators come out the same with D0 = 41, 61, 81 and Y = 20/21 or 30/31 (every tail probed, both machines);
- inside every phase Y + x is even, so the tail goes through E0, E1, E0, E1, ...: 1,467 of 1,467 increments in this
  machine's first 3·10^7 steps, 2,965 of 2,965 in the twin's first 6,000 records;
- a reset applies E1 O0 O1 when X is even and E1 when X is odd: 13 of 13 resets here, 13 of 14 in the twin (the
  exception is its first, at X = 7, which applies E1 O0).

So, read this way, whether either machine halts is a question about one fixed word of operators acting on one tail:
`w = (E0 E1)^m1 r(X1) (E0 E1)^m2 r(X2) ...`, where the phase lengths m_k and the reset words r(X_k) are read off the
orbit of the 3/2 map. The operators do not commute (E1 E0 E1 and E1 E1 differ on the three tails tried, at records 278, 1,502 and 3,000, even though E0
only lengthens the first block), so the tail is not a function of the number of increments, and the halting
question is about the parity sequence of a 3/2 map driving a carry through an irregular tail. All of this is
**heuristic**: checked on the runs named, not proved.

**Why compression stalls.** The tail is where the counter's carries leave their marks, and they are not regular: the
records have 29 blocks at 10^5 steps, 90 at 3·10^7 and 156 at 3·10^9 steps (190 in the twin), most of them short and of different
lengths (`... 2 o o 1 i 10 o o 1 i 188 o o 1 i 24 o o 2 o 11 i ...`). A run-length code of the tape therefore has
thousands of distinct runs beyond the first few blocks, which is what made the region-memo engine recurse that deep.
The method that works here is the one of this folder: keep the countdown and the long blocks symbolic (the macro
machine), and treat the tail as data acted on by the operators above.

## The reset map in Lean (22 Nov)

**The head part follows the 3/2 map exactly, whatever the tail holds.** `lean/ResetMap.lean` (kernel) proves, for
both machines at once:

- `reset_map`: from a reset `Reset X T = 0^inf 1 B> 1 0 (10)^X T` with X ≥ 36, if the phase's tail excursions are
  as in `Good X T K`, the run reaches `Reset (f X) T'`, where f X = floor(3X/2) + 1 (X even) or + 3 (X odd).
  Nothing about the tail T is assumed beyond `Good`.
- `orbit`: k phases in a row (`GoodN k X T`) take the run to `Reset (f^k X) T'`, in at least k steps.
- `reach_own`, `reach_twin`: from blank tape this machine is at `Reset 40 T0own` after 8,577 steps, and this table
  started in state D (the twin, `Twin29537.lean`) is at `Reset 52 T0twin` after 14,638 steps.
- `never_halts_own`, `never_halts_twin`: if `GoodN k` holds for every k, the machine never halts (the twin via
  `twin_halts_iff`).

**What `Good` says.** The tail is used only by *excursions*: the head reads the first cell of the tail in a state q
with four known cells u on its left, and later leaves to the left of those four cells in a state q', with four known
cells v written where u was. `Exc u q q' v T T'` says this happens for every tape on the left; T' is what is left of
the tail. A phase makes these excursions, in this order (cells left to right):

| piece | where | excursions |
|---|---|---|
| `re` | reset, X even | `0100` A→B `1001`, `0010` E→C `0101` twice, `1100` A→D `0101` twice |
| `ro` | reset, X odd | `1001` B→D `1011`, `0101` C→A `1010`, `1001` B→D `1011`, `1100` A→D `0101` twice |
| `g` | each two increments of the phase | `1100` A→D `0010` (the carry, one per two increments) |
| `e0`, `e1` | end of the phase, countdown 5 or 7 | `1100` A→D `0010`, and for `e1` then `0100` A→B `1010` |

Everything between excursions is a proved run (`lean/ResetMapRuns.lean`, 19 theorems for all values of the
parameters and every tail, written by `py/gen_resetmap.py` with `bbtools.symtm.prove`). So the countdown, the
growing block, the arithmetic of f and the parities that pick `e0` or `e1` are all in Lean, and **whether either
machine halts is now exactly the question whether some tail excursion fails to come back with the signature
above** (a halt can only happen inside an excursion, because everything outside them is a proved run without a
halt).

**Checked, not proved**: that the excursions do come back. `py/gen_resetmap.py` runs the symbolic head part next
to a direct simulation and reads each excursion's signature off the real run: all 1,888 phase double-steps of both
machines in their first 4,000 records, and 11 resets and 12 phase ends (X from 40 to 727, both machines), have the
signatures of the table. The signatures do not depend on X or on the tail in any instance seen.

## The carries checked in Lean, phase by phase (22 Nov)

**For the first 36 phases the reset map holds without hypotheses**, for this machine and for the twin.
`reset_map` (previous section) assumes `Good`: that every tail excursion of a phase comes back with the listed
signature. Those assumptions are now discharged, one phase after the other, by running the excursions themselves on
the actual tail inside Lean:

- `lean/ExcSim.lean` is the run-length simulator of `tools/lean/TM/RLE.lean`, rebuilt for excursions. Its left side
  ends in an **arbitrary** tape `L` instead of blank tape. No move ever reads past the end of the left side, and a
  left step off that end is the excursion's exit. Every move (a crossing of a run of `1010`-like words on the right
  or on the left, by `cross_r`/`cross_l`, or one ordinary step) is proved for every `L`, in a number of steps that
  does not depend on `L` (`xmove_spec`). So a successful run proves `Exc u q q' v T T'` exactly as `ResetMap.lean`
  states it (`exc_spec`).
- `lean/ResetExc.lean` runs the excursions of a phase in the order `Good` lists them (reset piece, the X/4 or so
  carries, phase end), with the tail kept as runs (`Side`), and proves `cOrbit k X T = true → GoodN k X T`
  (`cOrbit_spec`). Together with `orbit` this is `reach_of_check`: k checked phases take the run from the reset of
  `X` to the reset of `f^k X`.
- `native_decide` evaluates `cOrbit` on the two runs' first resets (`Reset 40 T0own` after 8,577 steps here,
  `Reset 52 T0twin` after 14,638 steps for this table started in D):

| file | machine | phases | reset reached (X) | approx. steps | check time |
|---|---|---|---|---|---|
| `lean/ResetExcRuns.lean` (in CI) | this one | 26 | 1,620,646 | 1.3·10^13 | ~1 min |
| | twin 1RB0RA_0RC0LE_0LD1RA_1LB0RF_0LD1LC_1RD--- | 26 | 2,099,734 | | ~1.5 min |
| `lean/ResetExcLong.lean` (by hand) | this one | 36 | 93,454,756 | 4·10^16 | 59 min |
| | twin | 36 | 121,081,390 | | 76 min |

`reach_own_phases36` says that this machine's run from blank tape reaches `Reset 93454756 T` for some tail `T`, so
it does not halt before; `reach_twin_phases36` says the same for the twin (through `twin_halts_iff`). The step
counts in the table are not part of the Lean statements (they come from the macro run's reset table above and the
2.25 growth per phase); the old Lean bound was `blank_runs_native`, 10^7 steps.

**How it is run.** The checker is ordinary Lean code. Interpreted, 22 phases take 170 s; `lean/check_native.sh`
compiles it and the modules it uses to C, links one shared library and loads it with `lean --load-dynlib` (what
Lake's `precompileModules` does), which is about 12 times faster. The trust is that of `native_decide`, the Lean
compiler. A wrong claim fails: `cOrbit 22 41 ...` and a tail with one extra cell are evaluated to `false`.

**Why this is not the whole answer.** Each phase has about X/4 carries and X grows by 3/2, so the check costs about
1.5 times more per phase (36 phases: about an hour per machine). The halting question is whether every phase passes.
That cannot follow from any property of the tail alone: the steered runs of the next section halt. A proof for all
phases needs a property of the tails that the true 3/2 orbit produces, which is still open.

**Further compute.** The lead asked for the halt hunt to go past phase 106. That had already happened: the
region-memo accelerator (`tools/py/bbtools/regaccel.py`, see the status page) reached about 10^135 steps for both
machines in 10 minutes, about phase 370 of the reset map at 2.25 per phase.

## The carries by Hashlife: 130 phases without hypotheses (24 Nov)

**Every carry of the first 130 phases of both runs is now checked in Lean**, so the reset map holds there with no
hypothesis: this machine's run reaches the reset with X = 3,335,644,625,007,427,579,461,373 (about 3.3·10^24), and the
twin's (this table started in D) the reset with X = 4,321,711,362,379,564,880,782,897 (`reachF_own130`,
`reachF_twin130`, `lean/TailHashLong.lean`, `native_decide`). By the 2.25 growth of steps per phase, that is about
6·10^49 steps for this machine and 9·10^49 for the twin; these step counts are an estimate, not part of the Lean
statements. The previous Lean bound was 36 phases (X = 93,454,756, about 4·10^16 steps), and the trusted
record-skipping run of `py/run_accel.py` stopped at X ≈ 1.3·10^20 (phase 105 in the numbering used here, where
X = 40 is phase 0).

**How.** The old checker (`lean/ResetExc.lean`) runs every carry of a phase on the actual tail, about X/4 of them, so
phase 36 already took an hour. Within a phase the tail only ever sees one operation, the carry `cc Eg wg` (the
excursion `Exc [0,0,1,1] A D [0,0,1,0]`, then `1010` in front), applied about X/4 times; it does not depend on X. So
the carries can be skipped in blocks of 2^j, in the manner of Hashlife:

- `lean/SymSim.lean` is the excursion simulator of `ExcSim.lean` with **symbolic counts**: a count is a linear form
  in variables, and the simulator, run at one concrete tail, records the linear conditions its decisions used. Each
  move is proved for every valuation that satisfies them, every tape on the left and every tape beyond the side
  (`exc_spec`).
- `lean/TailHash.lean` defines a *transform*: for every tail whose first runs have given words and counts (small
  counts exact, counts of at least 4 free), n carries give a tail whose first runs are linear in those counts, the rest
  of the tape untouched, under recorded conditions. `Sound t` is exactly `Gen n` of `ResetMap.lean` for the whole
  family. One carry is a transform by the symbolic simulator (`baseAt`); two transforms in a row compose by
  substituting the first one's output counts for the second one's variables (`compose_sound`). The memo keeps
  transforms together with their proofs, keyed by a hash of the runs they read; which transform is tried when is
  unverified search, and a lookup is always checked against the tail (`matchT`, `applyT_spec`).
- `cOrbitF_spec`: if `cOrbitF k X T` evaluates to `true`, then `GoodN k X T`, the hypothesis of `orbit` and
  `never_halts_own`. The pieces at the resets and phase ends are run as before, one excursion each.

Two things made it fast. A carry is cut down to the runs it actually read (the common suffix of its input and output),
so a transform's key does not include the deep, never-repeating digits of the counter; and adjacent single cells are
packed into one literal run of up to 32 cells, which makes the tails about five times shorter (6,770 runs at phase 130).

| file | phases | this machine: reset reached (X) | twin: reset reached (X) | check time |
|---|---|---|---|---|
| `lean/TailHashRuns.lean` (in CI) | 40 | 473,114,716 | 612,974,545 | 6 s |
| `lean/TailHashLong.lean` (by hand) | 130 | 3.34·10^24 | 4.32·10^24 | about 12 min each |

`lean/TailHashProgress.lean` prints the run phase by phase. Time per 10 phases grows slowly (30 s around phase 60,
about 2 minutes around phase 120, where the memo of 400,000 transforms is emptied and refilled). The Python model
of the algorithm (without the packing) is `py/tailhash.py`; it agrees with the carry-by-carry check on 17 phases of both machines.

**What this does and does not settle.** The open part of the problem has not moved: whether **every** phase passes,
`∀ k, GoodN k`. The checker proves each phase separately, and the cost per phase still grows. What is new is that
the tail's dynamics under the carries is now a finite symbolic object per phase (a few thousand transforms, each a
linear map on block lengths valid on a polyhedron of tails), rather than X/4 concrete runs. A proof for all phases would
need an invariant on the tails that the 3/2 orbit produces; the transforms are where such an invariant would have to be
read off.

## Is the tail safe on its own? (22 Nov, heuristic)

`reset_map` leaves one question: does every carry into the tail come back. Two C programs test whether the tail is
safe **by itself**, or only for the phase lengths the 3/2 orbit actually produces. Both run the real machine; they
change only the countdown X at a reset record `0^inf 1 B> 1 0 (10)^X T` and keep the tail T as it is.

- `c/branch.c` follows the true run and, at each of its resets, branches with X + δ for δ = -3 ... 8 and runs each branch for two more
  unchanged phases. It covered the first 17 resets here (X = 40 to 28,102) and the first 16 of the twin (X = 52 to
  24,271), plus 4 branches at the twin's 17th. **None of the 400 branches halts.**
- `c/perturb.c` changes X at every reset:

| X at each reset | runs | halted |
|---|---|---|
| fixed X, each of 37 ... 48, 50, 52, 60, 61, 80, 81 (200 resets each) | 18 | 0 |
| fixed X = 41, 50, 61, twin (200 resets) | 3 | 0 |
| growth ratio 1.25, 1.75 or 2 per phase instead of 1.5 | 7 + 24 + 24 | 0 |
| true X + δ, δ uniform in [-3, 3] (10 resets) | 40 | 4 |
| true X + one of -δ, 0, δ, for δ = 1, 2, 3, 4, 6 (10 resets) | 50 each | 0, 0, 2, 4, 0 |
| uniform in [36, 400] (30 resets) | 200 | 21 |
| uniform in [36, 400], twin (30 resets) | 100 | 20 |
| uniform in [2000, 4000] (20 resets) | 100 | 25 |

So **the tail is not safe by itself**: a run of the real machine whose phase lengths are chosen differently can
halt. Every halt seen is deep in the tail (hundreds to thousands of cells from the head), during an ordinary carry
of a phase, often only a few dozen records after a reset. Phase lengths that follow a regular rule (constant, or a
fixed growth ratio) never halted, and neither did a single change in the true orbit. Halts came when the lengths
jump around irregularly from phase to phase. So whatever keeps the true run alive has to come from how the 3/2
orbit's phase lengths shape the tail. It is not a property of every tape the head part can leave behind.

The random runs halt at about 0.3% to 1% per reset. If the true orbit's tail had a constant hazard of that size,
surviving its 28 known resets would not be surprising (about 75% to 90%). It would also mean the machine
eventually halts with probability 1. Nothing here says whether the true orbit has such a hazard, or why the regular
schedules avoid it. That is the open question, now stated sharply: which property of the phase-length sequence
keeps every carry inside the tail returning.

**Where the carries die, and how often the true run goes there.** Each sweep from a left record turns at some
block, the rightmost one it reaches. `CTX=1 ./perturb ...` prints that turning block with its neighbours (D capped
at 9) at every record. In the true run (the first 2·10^10 steps, 126,293 records here, 123,155 in the twin)
99.3% of the turns are at four contexts: the head's `(0, o)` or a long o-block, followed by a long block. The other
0.7% (892 here, 972 in the twin) turn further out, in the **rough part of the tail**, where short blocks follow
each other. In the steered runs with X uniform in [36, 400], 14.4% of all turns are rough (180,471 of 1,252,308).
That is 20 times more often.

Every halt of a steered run happens at a rough turn: a short block followed by small blocks such as `1i 1i 1o 1i`,
`1i 1o 1i` or `1o 2o`. Most of these contexts never occur as a turn of the true run. Per rough turn, the steered
runs halt about once in 8,600 (21 of 180,471). At that rate the true run's 1,864 rough turns (both machines)
would give about 0.2 halts, so its survival so far fits the same hazard per rough turn. **What keeps the true run
safe so far is mainly that its carries rarely reach the rough tail.**

In the true run the rough turns of a phase come in two groups. The first group is the first 8 or so records after
each reset. The second is a regular train of turns later in the phase, at records 4, 8, 12, ... or 16, 32, 48, ...
into it, like the carries of a binary counter reaching a fixed depth. Their number per phase grows slowly: about
20 to 40 in phases 1 to 6, and 45 to 85 in phases 14 to 18, much slower than the phase lengths (×1.5 each). If the
hazard per rough turn stayed near 1 in 10^4 and the count kept growing like this, the expected number of halts
would grow without bound, but only over a hundred or more phases. Nothing here rules that out, and nothing proves
it. A proof would have to show that the rough tail the carries reach never contains a fatal context.

**The tail is a binary counter of blocks.** Within a phase, compare the tail at consecutive `o o` records
(the first 3·10^9 steps, 23,785 increments with a change). One increment in two (E0) changes only the first block.
The others (E1, the carries) change the first d blocks with frequency halving in d: 5,939 / 2,975 / 1,480 / 739
/ 372 / 187 / 93 / 46 for d = 2 ... 9, and 56 blocks once. Write a block's *shape* as its x and D (D capped at
8 + D mod 2). After a transient following each reset, the shapes of the first w blocks repeat with period
**exactly 2^w carries**. In the eight phases of more than 500 records in the first 3·10^9 steps, this holds for w ≤ 4 in all of them. It
holds up to w = 7 (128 carries) in the five longest, and for w = 8 in the last one. It is not seen for w = 5 in
the second phase, and the phases are too short to test larger w (`py/tail_counter.py`). So block w is a digit touched once per 2^w carries, and the rough tail is reached only by the
rare deep carries and by the transient after a reset.

This suggests how a halt hunt could go much further than the 28 phases of `py/run_macro.py`, which steps through
every record. A carry-skipping simulator would keep the tail as blocks with big-integer D. It would advance block w
by its number of touches in a phase (about m / 2^w for m carries), using the per-touch rule of its regular shape.
It would step the macro machine only through the post-reset transient and through carries that reach a rough or
irregular block. The cost per phase would then be about (tail blocks) × (transient length) instead of X, which
makes phase 100 a matter of bookkeeping. This is not built yet. The per-touch rules for regular blocks are the
crossing rules of `py/blockmm.py`.

**The carry-skipping halt hunt (`py/accel.py`, `py/run_accel.py`).** This is the simulator outlined above, built
as Hashlife over time on the block macro machine. A *transform* records what 2^j records do to a tape whose first
L blocks have given shapes (D exactly when D < 64, else the parity of D, and x). The new first blocks are linear
expressions in the old D's, the steps are a linear expression, and linear conditions say when the intermediate
shapes are the ones assumed. One record comes from `blockmm.macro_step` on a generic tape (each long block a distinct
huge number, decoded afterwards) and is checked against the concrete step. Level j is two level-(j-1) transforms
composed, memoized by shapes. Checks: from blank tape it reaches record 16,409,053 at exactly step
338,536,834,271,065 with X = 8,204,530, as the old run did (8 s instead of the old run's long compute). For the
twin it agrees with the plain macro run, state and steps, over 300,000 records.

| run (100 minutes, about 3 GB) | phases (X from 40, resp. 52) | records | steps | halt |
|---|---|---|---|---|
| this machine | 106 (X ≈ 1.3·10^20) | 2.65·10^20 | 8.86·10^40 | none |
| the twin | 101 (X ≈ 2.3·10^19) | 4.5·10^19 | 2.59·10^39 | none (stopped by memory) |

The previous reach was phase 31 (3.39·10^14 steps). By the estimate above (about one halt per 8,600 rough turns), and if the number of rough turns per phase kept
growing as it did in phases 1 to 18, a halt before phase 106 would have had a probability of very roughly one half.
None came. That makes the estimate doubtful, and it says the true orbit's rough tail is safer than the steered
runs' rough tail. This is still a computation, not a proof. It is exact if `blockmm`'s crossing rules (symbolic
runs, not in Lean beyond the first 300,000 records) and the shape threshold 64 are right. The threshold was checked
by the two comparisons above. Each phase now costs about 150 s and grows slowly. `python3 run_accel.py FILE
SECONDS` resumes from the STATE line a run prints at its end.

Reproduce: `gcc -O2 -o perturb c/perturb.c && ./perturb 5 36 400 30 1e10` (seed 5 halts after 23 resets);
`gcc -O2 -o branch c/branch.c && ./branch 16 2 A 0 1 2 3 4 5 6 7 8 -1 -2 -3`.

## Where it could halt

F is entered only by A reading 1 (A1 = 0LF), and F1 halts. So the machine halts exactly on `1 A>1`. Neither the
macro run nor the direct simulation has reached it. The record patterns above are **not** an invariant.
`py/random_check.py` builds 20,000 random block lists and runs one macro step on each. 2 of 14,742 lists that obey
the three patterns halt, and 2 of 5,258 that do not. Excluding the halt therefore needs finer information about
which lists the run can reach.

## Status and evidence

**Lean, kernel**:
- `right0` ... `right110`, `left0` ... `left275` (`lean/Rules.lean`, from `py/gen_rules.py`): every crossing rule of
  the macro machine used in the first 300,000 records, for all t and all tapes;
- `carry_even` (`lean/Sweep.lean`, from `py/gen_sweep.py` with `bbtools.seqtm`): the even long sweep over an
  arbitrary list of blocks; `lean/Seq.lean` is the sequence library, copied from bb6-1RB1RF_1LC0LB;
- `short_raw` / `short` (`lean/Gadgets.lean`, `lean/Macro.lean`): the short sweep for every x and tape;
- `reach2438`, `reach2522`: the run from blank tape reaches the first counter configuration;
- `step_none_iff`, `blank_runs_kernel` (`lean/Blank.lean`): halting configurations; no halt in 10^4 steps;
- `twin_halts_iff`, `twin_reach157`, `twin_halts_iff_record` (`lean/Twin29537.lean`): the twin
  1RB0RA_0RC0LE_0LD1RA_1LB0RF_0LD1LC_1RD--- halts from blank tape iff this table halts from blank tape started in D,
  iff it halts from the twin's record at step 157;
- `twin_right0` ... `twin_right55`, `twin_left0` ... `twin_left174` (`lean/RulesTwin1.lean`, `lean/RulesTwin2.lean`, from
  `py/gen_rules_twin.py`): the further crossing rules used in the twin's first 300,000 records.
- `reset_map`, `orbit`, `reach_own`, `reach_twin`, `never_halts_own`, `never_halts_twin` (`lean/ResetMap.lean`, with
  the runs of `lean/ResetMapRuns.lean` from `py/gen_resetmap.py`): the reset map X' = f X for the head part of the
  tape, for both machines, given the tail excursions (`Good`).

**Lean, native_decide**: `blank_runs_native`, no halt in 10^7 steps.
- `ExcSim.lean`, `ResetExc.lean` (kernel): a run-length simulator for excursions, proved for every tape on the left
  (`exc_spec`), and the phase checker: a successful check of k phases proves `GoodN k` (`cOrbit_spec`, `reach_of_check`).
- `reach_own_phases`, `reach_twin_phases` (`lean/ResetExcRuns.lean`, in CI): every carry of the first 26 phases is checked;
  the runs reach the resets with X = 1,620,646 (this machine) and X = 2,099,734 (the twin) without a halt.
- `reach_own_phases36`, `reach_twin_phases36` (`lean/ResetExcLong.lean`, by hand): the same for 36 phases, X = 93,454,756
  and X = 121,081,390. Both files run with the checker compiled to native code (`lean/check_native.sh`).
- `SymSim.lean`, `TailHash.lean` (kernel): the excursion simulator with symbolic counts (`exc_spec`), transforms of
  many carries and their composition (`compose_sound`), and the Hashlife phase checker (`cOrbitF_spec`).
- `reachF_own40`, `reachF_twin40` (`lean/TailHashRuns.lean`, in CI, 6 s) and `reachF_own130`, `reachF_twin130`
  (`lean/TailHashLong.lean`, by hand): every carry of the first 40 / 130 phases is checked; the runs reach the resets
  with X = 3,335,644,625,007,427,579,461,373 (this machine) and X = 4,321,711,362,379,564,880,782,897 (the twin) at phase 130.

**Computed (trusted)**:
- `py/run_accel.py` (record skipping, checked against `py/run_macro.py`): no halt through phase 106, 8.86·10^40
  steps, here, and through phase 101, 2.59·10^39 steps, in the twin.
- `py/check_macro.py`: the macro machine agrees with `c/recp.c` (direct simulation) at all 15,144 records up to
  step 299,979,488.
- `py/run_macro.py`: no halt through 16,409,053 left records, 338,536,834,271,065 (3.39·10^14) steps and
  28 resets. This rests on the composition in `py/blockmm.py`; each rule it applies is a symtm run, and the
  rules of the first 300,000 records are the ones in Lean.
- `c/rec18.c` (previous pass): no halt in 1.17·10^11 steps, by direct simulation.

- `py/twin.py`: the macro machine agrees with a direct run of the twin at all records up to step 299,972,981; its
  macro run finds no halt in 300,000 records (1.20·10^11 steps).

**Heuristic**: that the tail excursions come back as `Good` asks (`py/gen_resetmap.py`); that the tail is not safe by itself, so steered runs with irregular phase lengths halt (`c/perturb.c`, `c/branch.c`); the tail operators (`py/tail_ops.py`), the three record
patterns, and the 99.99% share of simple sweeps.

**Open**: whether it halts. `GoodN 130` is proved for both runs; the Lean theorem `¬ Halts` is proved only under `∀ k, GoodN k` (`never_halts_own`), that is, if
every tail excursion comes back the observed way.

## Reproduce

```sh
holdouts/1RB0LF_0LC0RE_0RA1LD_1LB0LD_0RA1RC_1LA---/lean/check.sh
holdouts/1RB0LF_0LC0RE_0RA1LD_1LB0LD_0RA1RC_1LA---/lean/check_native.sh ResetExcLong.lean   # 36 phases, about an hour per machine
holdouts/1RB0LF_0LC0RE_0RA1LD_1LB0LD_0RA1RC_1LA---/lean/check_native.sh TailHashLong.lean   # 130 phases by Hashlife, about 12 minutes per machine, 4 GB
python3 holdouts/1RB0LF_0LC0RE_0RA1LD_1LB0LD_0RA1RC_1LA---/py/tailhash.py own 40   # the Python model of the Hashlife checker
D=holdouts/1RB0LF_0LC0RE_0RA1LD_1LB0LD_0RA1RC_1LA---
python3 $D/py/gen_rules.py 3e5              # rewrites lean/Rules.lean (a few minutes)
python3 $D/py/gen_sweep.py                  # rewrites lean/Sweep.lean
gcc -O2 -o recp $D/c/recp.c && ./recp 4000000 3e8 1 100000 > r3e8.txt && python3 $D/py/check_macro.py r3e8.txt
python3 $D/py/run_macro.py 2e7 1e6          # the long macro run, about 40 minutes
python3 $D/py/random_check.py SEED 20000     # random block lists, one macro step each
python3 $D/py/gen_resetmap.py               # rewrites lean/ResetMapRuns.lean and the generated parts of lean/ResetMap.lean (a minute)
python3 $D/py/gen_rules_twin.py 3e5          # rewrites lean/RulesTwin1.lean, lean/RulesTwin2.lean (a few minutes)
./recp 4000000 3e8 1 100000 D > twin3e8.txt && python3 $D/py/twin.py twin3e8.txt   # the twin, record by record
python3 $D/py/reset_map.py twin3e8.txt       # the countdown map at every reset (also: reset_map.py own|twin N)
./recp 4000000 3e7 1 100000 > r3e7.txt && python3 $D/py/tail_ops.py r3e7.txt 400   # the tail operators (minutes)
```

## Layout

| path | what it is |
|---|---|
| `lean/Machine.lean`, `lean/Blank.lean` | the machine and bounded runs (generated) |
| `lean/Gadgets.lean`, `lean/Macro.lean` | the short sweep and the reach from blank tape |
| `lean/Rules.lean` | the 387 crossing rules of the macro machine (generated) |
| `lean/Seq.lean`, `lean/Sweep.lean` | sequence library; `carry_even` (generated) |
| `py/blockmm.py` | the block macro machine |
| `py/run_macro.py`, `py/check_macro.py` | long macro run; comparison with direct simulation |
| `py/gen_rules.py`, `py/gen_sweep.py`, `py/gen_gadgets.py` | Lean generators |
| `py/random_check.py`, `py/check_counter.py` | random-list test; the previous pass's counter check |
| `lean/Twin29537.lean` | the twin is this table, mirrored, started in D (kernel) |
| `lean/RulesTwin1.lean`, `lean/RulesTwin2.lean`, `py/gen_rules_twin.py`, `py/gen_rules_lib.py` | crossing rules of the twin's run (generated) |
| `py/twin.py`, `py/reset_map.py`, `py/tail_ops.py` | the twin against direct simulation; the countdown map; the tail operators |
| `lean/ResetMap.lean`, `lean/ResetMapRuns.lean`, `py/gen_resetmap.py` | the reset map in Lean: the head part of a phase and its composition |
| `lean/ExcSim.lean`, `lean/ResetExc.lean` | the excursion simulator (any tape on the left) and the phase checker |
| `lean/ResetExcRuns.lean`, `lean/ResetExcLong.lean`, `lean/check_native.sh` | the checks of 26 (CI) and 36 (by hand) phases, run as native code |
| `lean/SymSim.lean`, `lean/TailHash.lean` | the excursion simulator with symbolic counts; Hashlife over the carries of a phase |
| `lean/TailHashRuns.lean`, `lean/TailHashLong.lean`, `lean/TailHashProgress.lean` | 40 (CI) and 130 (by hand) phases by Hashlife; a phase-by-phase timing run |
| `py/tailhash.py` | the Python model of the Hashlife checker |
| `c/recp.c`, `c/rec18.c` | direct simulators printing records in P-notation (any start state) / the old notation |
| `py/accel.py`, `py/run_accel.py` | the carry-skipping run (Hashlife over records on the block macro machine) |
| `py/tail_counter.py` | the tail as a binary counter of blocks: depth of each carry, periods of the first w blocks |
| `c/perturb.c`, `c/branch.c` | the real machine with the countdown replaced at resets: steered runs, and branches off the true run |

## For later

- **Soundness of composition in Lean.** Define the block lists and `reparse` in Lean, and prove that a macro step
  built from the `Rules.lean` lemmas yields `steps n` between consecutive records. Then the macro bound is
  kernel-level.
- **Invariant search at block level.** Find a property of reachable block lists, finer than the three patterns,
  that random halting lists violate and the macro step preserves. If the parities are the issue, a `halts_iff` to a
  Collatz-like statement on (X, Y, digits) may be the realistic target.
- **Speed.** A C port of `blockmm`, or an increment-at-a-time or phase-at-a-time acceleration via `carry_even`,
  would push the bound by many more phases.

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0RA_0RC0LE_0LD1RA_1LB0RF_0LD1LC_1RD---`](../1RB0RA_0RC0LE_0LD1RA_1LB0RF_0LD1LC_1RD---/README.md): rename A→D, B→B, C→C, D→A, E→E, F→F and exchange left and right; it is this table started in state D, in a mirror

<!-- end of related machines -->
