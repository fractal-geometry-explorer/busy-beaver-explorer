# 1RB---_1RC0RD_1RD1RA_1LE1RB_0LF0LE_1RF0RD

bbchallenge id 140108. One of the six-state holdouts whose halting from blank tape is open (group G11, family
*separator counter*, shared with `1RB---_1LC1RE_0LD0LC_1RD0RB_1RF0RB_0LF1RA`).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | --- |
| B | 1RC | 0RD |
| C | 1RD | 1RA |
| D | 1LE | 1RB |
| E | 0LF | 0LE |
| F | 1RF | 0RD |

## What it does

**Events.** Every so often B reaches the right end of the tape on blank. At every such event the tape is blocks of
1s separated by single 0s, `1^x1 0 1^x2 0 ... 0 1^xr 0 1^N B>0`, with x1 >= 2 and a long last block N.

**Two binary counters (proved).** Right after an event the head, in state B, is at the left end of a binary
counter written in groups of three cells (`0 0 0` = digit 0, `0 0 1` = digit 1, lowest digit first), which reads
`0^d 1`. Left of the head is the bit string in pairs `1 b` (after the first two 1s), ending with the pair `0 1`
(the old separator and the first 1 of the old block). Call this configuration `P(d, bs)` (`P` in `lean/Count.lean`).
One *count*: B runs right over the trailing 1-digits (`0 0 1` -> `1 1 1`), writes `1 1 1` on the first 0-digit
and turns; E erases back to the pair `0 1`; then the carry of the left string is a leftward walk through a block of
1s (each cell shifted right, 3 steps a cell) up to the first 0, and D runs back rewriting `1 1` pairs as `1 0`. The
count adds 1 to the right counter and 4 to the left string (its two lowest pairs are scratch and come back unchanged).
2^d counts take the counter from `0^d 1` to `1^d 1`, and the next one carries into blank tape: the next event, one
digit more. So, with j = d + 1 = (N+2)/3,

> **event rule:** bits b (M of them), N  →  b + 2^j, N + 3, as long as the addition does not carry out of the top bit.

`lean/Count.lean` proves this for every size, every bit string and every left context (kernel): `count` (one count,
by cases on the lowest bit and the two carry lengths), `iter` (2^d counts, induction on d), `event_rule`
(`P d (b1 :: lo ++ h)` reaches `P (d+1) (b1 :: lo ++ inc h)` when `lo` has d bits and `h` contains a 0),
`event_to_P` (the event `bits 0 1^(3d+4) B>0` reaches `P (d+1) (bits + 2)`), `blank_to_P` (step 69 from blank is
`P 0 [0,1]`). Since these are runs, **the machine cannot halt between overflows** (a deduction from `blank_to_P` and `event_rule`, not itself a Lean theorem): it can halt only in a phase
whose addition carries out of the top bit. (Note: the bits at a P configuration are the bits of the event just
before it plus 2, because the first count of a phase finishes after the event.)

Example (steps 1,262,008 to 12,075,404): N = 43, 46, 49, 52, 55 and bit strings `0000110000010000101`,
`0001110000010000101`, `0011110000010000101`, `0111110000010000101`, `1111110000010000101` (2^15, 2^16, ... added).
`py/pchain.py` lists the P configurations of a run: to 2·10^7 steps, 22 phases follow `event_rule` and 6 are
overflows.

**Overflow.** When the addition carries out of the top bit, let R = X + 2^j - 2^M (X the bit string as a number).

- R even: the next event has X = R + 1 with M + 1 bits, N + 3 (the string grows by one bit).
- R odd: read R in pairs from the lowest bit; k = number of pairs at the bottom whose low bit is 1, r = R mod 4^k.
  The next event has X = C(r) + floor(R / 4^k), M + 3k + 1 bits, N - 3(2k - 1) (if that is -2: X halved, one bit
  fewer, N = 1). C(01) = 43, C(11) = 104, and for k >= 2, with t the number of trailing `11` pairs of r,
  C(r) = C(r >> 2) + c_t 8^(k-1), c_0 = 42, c_t = 248·4^(t-1) - 21 (2 c_(k-1) + 21 if all k pairs are `11`).

This map was first read off runs of the machine (it is now proved in another form, below). It agrees with every overflow of the run to 4·10^11 steps, with all
1,950 overflows of strings of at most 9 bits (run directly), and the recursion for C with all 126 patterns of k <= 6
and 12 random ones of k = 7, 8 (`py/macro.py`). The overflows of the run (bits, then M and j):

| step | before (M, j) | after (M, j) |
|---|---|---|
| 7,049 | `11100101` (8, 8) | `000000110001001` (15, 5) |
| 721,358 | `100000101101001` (15, 14) | `0000000000010000101` (19, 13) |
| 12,962,688 | `1111110000010000101` (19, 19) | `00000000000111111110000011` (26, 16) |
| 1,857,557,486 | `11111111110111111110000011` (26, 26) | `000000111111111110000001001000` (30, 25) |
| 48,364,000,185 | `111110111111111110000001001000` (30, 30) | `0111110111111111110000001001001` (31, 31), R even |
| 78,168,858,449 | `0111110111111111110000001001001` (31, 31) | `00000001111101111111111100000111101` (35, 30) |

**Halting.** The map covers every overflow except those whose odd pairs reach the top bit. Among those, for every
string of at most 9 bits, the machine halts only for the all-ones string with j = M: `1^(2M+2) 0 1^(3M-2) B>0`
(after 686, 1,390, 2,798 steps for M = 4, 5, 6; Lean, kernel); the other 67 such cases do not halt. So the machine
halts if and only if the map reaches a string whose odd pairs fill it (and then the all-ones one). This is now proved
for every size, in the form of the phase map below (`halts_iff_family`).

**The map iterated.** From the first event (step 39), 100,000 phases in 38 s: the odd pairs never reach the top; M
grows to 508,578 bits, about 10^153,000 machine steps. k at an overflow: 1 (35,315 phases), 2 (14,810), 3 (8,264),
4 (4,218), 5 (2,226), 6 (959), 7-10 (819), 11-20 (318), 21-92 (56); R even in 33,015. A halt needs k >= M/2.

**The map iterated to 10^10 phases (`c/phasefast.c`, item 15 of the 24 Nov list).** `phasefast` keeps the string as a
packed bit array whose low end moves: the shift by 2k only moves a pointer, the events of a phase only set the 5k bits
between j0 and M (the string is shorter than 2^j0 after an overflow), and C(r) is added in place level by level, so
a phase costs O(k) and not O(M). It prints the same (M, j) as `py/macro.py` at each of the first 100,000 overflows and
the same string at every 500th (`phasefast dump 100000 500`, compared in Python). After every overflow it tests the
two halting conditions directly: the stuck case (odd pairs reach the top) and the landing condition of
`halts_iff_lands`, X = 2^j - 1 with j + 1 <= M. **Neither occurs in 10^10 overflows** (1,300 s, about 7 GB;
`evidence/phasefast-1e10.txt`): M grows to 51,003,339,348 bits, so the run covers about 10^(1.5·10^10) machine
steps. k at an overflow: 1 (3,542,223,542), 2 (1,475,065,025), 3 (822,448,196), 4 (424,871,306), 5 (223,654,003),
6 (102,207,606), 7-10 (83,924,169), 11-20 (31,864,176), 21-62 (5,877,814), 63 and more (67,897); R even in
3,287,796,266. The largest k is 776 (overflow 3,938,587,432), where a halt needs k >= M/2, about 2.5·10^10; after
overflow 100, 2k/M never exceeds 0.0234. The longest run of ones at the bottom of an output string is 699, where
landing needs j (about M) ones and nothing above. At the end 3,255,286,356 of the 25,501,669,674 pairs of the string
(13%) have low bit 0 (blockers). Only 7 event additions in the whole run carry (the 3rd and 5th overflows' phases):
everywhere else the string is shorter than 2^j0. This is still evidence, not a proof.

On the other option of the item, a residue search: `py/congruence.py` (below) already shows that no invariant on
residues of (X mod q, j, M) can exclude the family for q <= 1,500 or q = 2^a, a <= 31, because orbit outputs meet
every residue class of the family. So the halting question stays where it was: does the orbit of `phase` ever land?

**The shape of the string at an overflow (worker 2, round 2 of G11; computed with the trusted map).** In a phase
that starts with j = j0 the events add 2^j0, 2^(j0+1), ..., so the phase ends when the sum 2^j - 2^j0 passes 2^M.
After an overflow the new string is shorter than 2^j0, so the phase runs to j = M and the remainder is
R = X + 2^M - 2^j0: **the top M - j0 bits of R are all 1 and the low j0 bits are those of X**. This holds at 2,998
of the first 3,000 overflows (all but the 3rd and 5th). Call a pair of R (from the lowest bit) a *blocker* when its
low bit is 0: k is the place of the lowest blocker, and the halting case needs a string with no blocker. The shift
by 2k keeps pairs aligned, so blockers above the lowest one move down unchanged until the addition of C(r) (about
3k bits) reaches them. In 20,000 overflows of the map the number of blockers in R grows about linearly: 17 at
overflow 39 (M = 155), 639 at overflow 2,000 (M = 10,075), 3,302 at 10,000 (M = 50,724), 5,901 at 18,000
(M = 91,490), about one blocker gained per three overflows, and only 56 of the 20,000 overflows (all among the first
ones) have fewer than 20. So under the map a halt would need thousands of blockers to disappear at once; this is
evidence, not a proof: no invariant that keeps one blocker is proved. The
recursive visit law that settled the corresponding point for the two-word sweepers
(`holdouts/1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RA_0LB---/lean/Stream.lean`) was not found here: in this machine every turn
of the head erases back into the left string, so a visit of the right side is not a function of the right side
alone.

**The overflow, proved (`lean/Overflow.lean`, `lean/Junction.lean`, `lean/Phase.lean`, `lean/Orbit.lean`,
kernel).** Write a post-event configuration with numbers, `PN d M Y` = `P d (bitsOf M Y)` (Y = X + 2 the string as
an M-bit number, lowest bit nearest the head). In an overflowing phase, i0 counts bring the string to `b1 1^(M-1)`;
the next count carries into the blank left of the string, F writes two new 1s there and D comes back over the
shifted block (`overflow_true`, `overflow_false`). The string is reset (to `0^M`, or to `1 0^M` when b1 = 0) and the
head comes back one cell out of phase with the counter: the right side is `ctr(low) J`, where the *junction* J is
`h ctr(H)` (a K junction, after b1 = 1) or `0 h ctr(H)` (a J junction, after b1 = 0) and H is the rest of the
incremented counter. From there the machine is a small *junction machine* with one proved rule per step
(`Junction.lean`):

- a count adds 1 to `low` (and 2 to the string), as before;
- `low` full, next digit 0 (`carry0`): `low` becomes `0^l 1`, one digit longer;
- `low` full, J junction, next digit 1 (`carryJ1`): the head crosses the ones `1^s 0` that follow and `low` becomes
  `0^(l+s+1) 1`;
- `low` full, K junction, next digit 1 (`absorb_even`, `absorb_odd`): `low` is absorbed into the string: l = 2n
  gives the new low bits `0^(3n) 1` and a J junction, l = 2n + 1 gives `1 0^(3n+1) 1` and a K junction;
- H used up: the counter is `0^d 1` again, a post-event configuration.

`astep` and `arun` (`Phase.lean`) are this machine on numbers and lists, with side conditions where the left string
could overflow (`stuck`); `astep_next`, `arun_done` prove every step. `phase d M Y` (`Orbit.lean`) is one whole
phase: the event rule, or i0 counts, the overflowing count and `arun` (fuel 2d + 12). `phase_sound`: whenever
`phase` returns `(d', M', Y')` the machine goes from `PN d M Y` to `PN d' M' Y'`. With `blank_to_P` (step 69 is
`PN 0 2 2`), `orbit_reach` and

> **`not_halts_of_orbit`: if the orbit of `phase` from (0, 2, 2) never gets stuck, the machine never halts**

(axioms propext, Classical.choice, Quot.sound; no `sorry`). `lean/OrbitCheck.lean` checks with `#guard` that the
first 9 overflows of `orbit` are those of the table above. `py/phasemap.py` is a line-for-line transcription: it
agrees with the machine at all 2,000 overflows of strings of at most 9 bits (and is stuck at the 8 that halt), with
`py/macro.py` (the old trusted map, C(r)) at the first 1,000 overflows of the orbit (M up to 4,788), and Lean's
`#eval` of `phase` agrees with it at the first 300.

**Halting is exactly the map getting stuck (`lean/Invariant.lean`, `lean/Start.lean`, `lean/Family.lean`,
`lean/Converse.lean`, kernel).**

> **`halts_iff_stuck`: the machine halts from blank tape if and only if the orbit of `phase` from (0, 2, 2) gets
> stuck;** `halts_iff_family`: if and only if the orbit meets (d, M, Y) = (m, m + 2, 2^(m+1) + 1) for some m

(axioms propext, Classical.choice, Quot.sound). The pieces:

- `Inv` (`Invariant.lean`) is an invariant of the junction machine that bounds the left string by what the counts
  still to come will add: with a J junction the right side is one counter that runs on to `2^l tl(H)` and the string
  has room for twice the difference (`JInv`); with a K junction there is room for the counts up to the next
  absorption, and right after it plenty of room (`KInv`, `SInv`). `step_inv`: from a state with `Inv`, `astep` never
  gets stuck, keeps `Inv` and lowers a measure; `arun_inv`: with fuel above the measure `arun` ends in a post-event
  configuration with `2 <= Y < 2^M` and `d < M`. `arun_mono`: the counter never shrinks, so the guard of `phase`
  never fires.
- `phase_some` (`Start.lean`): every overflow start with `2 <= Y < 2^M`, `d < M` satisfies `Inv`, except the family
  (d, M, Y) = (M - 2, M, 2^(M-1) + 1), where the first 1 of the counter (`lz`) is too high. So outside the family
  `phase` returns a configuration, again of that kind.
- `fam_halts` (`Family.lean`): the family halts for every m. After the overflowing count the junction machine carries
  through the m + 1 zeros of the counter until the left string is `0 1^(m+1)`; the next carry overflows it again
  (`overflow_walk`, the walk of `overflow_false` for any tape on the right), leaving the counter `0^(m+1)` followed by
  `0 1 1`; `2^(m+1) - 1` counts fill it and the carry reads B0, C1, A1: halt.
- `halts_iff_stuck` (`Converse.lean`): the orbit stays in the good region until it meets the family, so it gets stuck
  only right after the family, from which the machine halts; the other direction is `not_halts_of_orbit`.

**Where the family can be entered, and no congruence blocks it (`lean/Landing.lean`, kernel; `py/congruence.py`).**
The event branch of `phase` adds 2^(d+1) to Y and 1 to d, so it keeps Y - 2^(d+1) fixed: a family point is preceded,
back to the last overflow, by points (d, M, 2^(d+1) + 1) with d + 2 <= M. So

> **`halts_iff_lands`: the machine halts from blank tape if and only if some overflow phase of the orbit returns
> (d, M, 2^(d+1) + 1) with d + 2 <= M**

(axioms propext, Classical.choice, Quot.sound). In event terms (X = Y - 2, j = d + 1) the overflow must leave the
string X = 2^j - 1, j ones under a counter of length j. Lead 27 asked for a congruence that excludes this. A residue
invariant on (X mod q, j, M), with any moduli for j and M, can exclude it only if no overflow output has
X = 2^j - 1 (mod q), because every family point shares its residues with such an output. `py/congruence.py 20000 1500 24`
(18 s) counts them over overflows 6 to 20,000: every q <= 1,500 is hit (the fewest relative to 1/q is q = 1,237,
4 hits), mod 3 the six classes of (X mod 3, j mod 2) each hold about a sixth of the outputs, and outputs whose low a
bits are all ones occur for every a <= 31, with frequency close to 2^-a (13,371, 6,856, 3,264, 1,538, ... for
a = 1, 2, 3, 4). **So there is no congruence invariant mod 3, mod any q <= 1,500, or mod 2^a with a <= 31.** The
reason is the shift: an overflow divides R by 4^k, so the low bits of the new string come from higher bits of the
old one and no fixed modulus closes up (the blockers above carry the information down). Every one of these outputs
has X < 2^j (the string is shorter than the counter; the family is the largest string allowed by this), but that
bound is not closed under the map by residues either: from an overflow start (M - 1, M, Y) whose top bits are ones
(Y = Y0 + 2^M - 2^(d0+1), Y0 < 2^(d0+1), d0 < M - 1) the output breaks it exactly when Y0 mod 32 is 1, 9, 17, 23,
25 or 31 (all 16,320 such starts with M = 14, by `phase`).

So the whole halting question is now a question about the integer map `phase`: does its orbit from (0, 2, 2) ever
reach (m, m + 2, 2^(m+1) + 1)? In the README's event terms that is the all-ones string with j = M, the pattern of
`Shapes.lean`. The map behaves like a random process on growing strings; a halt needs k >= M/2 and the k seen thin
out geometrically (above). No invariant excluding the family is known; this looks like a Collatz-type question,
not something a finite certificate will settle.

## Status

Open, and reduced in Lean to a question about an integer map. Lean: `lean/Blank.lean` (halting configurations; no
halt in 10^7 steps), `lean/Rules.lean` (shift rules `erase`, `fill`, `pairs`, `shift`, kernel), `lean/Shapes.lean`
(`allones_4/5/6`: the halting pattern halts, kernel), `lean/Count.lean` (the event rule for every size, kernel),
`lean/Bits.lean` (bit strings as numbers), `lean/Junction.lean`, `lean/Overflow.lean`, `lean/Phase.lean`,
`lean/Orbit.lean` (the overflow phase for every size and `not_halts_of_orbit`, kernel), `lean/OrbitCheck.lean` (the
first 9 overflows, `#guard`), `lean/Invariant.lean`, `lean/Start.lean`, `lean/Family.lean`, `lean/Converse.lean`
(**`halts_iff_stuck`, `halts_iff_family`**, kernel). Not proved: that the orbit never meets the family.
Computed: no halt in 4·10^11 steps (`tools/c/tmrun.c`); 10^10 phases of the map (`c/phasefast.c`, which agrees with
`py/macro.py`, which agrees with `phase`) without meeting it or getting stuck, about 10^(1.5·10^10) steps.

## Scripts

- `py/bitmodel.py events 1RB---_1RC0RD_1RD1RA_1LE1RB_0LF0LE_1RF0RD B LOG` checks every event of `tmrun 1RB---_1RC0RD_1RD1RA_1LE1RB_0LF0LE_1RF0RD T at B R 400 > LOG` against the rule;
  `py/bitmodel.py exhaust 1RB---_1RC0RD_1RD1RA_1LE1RB_0LF0LE_1RF0RD B 6` runs every 6-bit string and every j.
- `py/pchain.py MACHINE B 2e7` lists the post-event configurations `P d bs` of a run and checks each phase against
  `event_rule` (state E for the sibling).
- `py/accel.py MACHINE B N --c=PATH` (PATH: `gcc -O2 -o PATH c/transient.c`): the exact run, phase by phase with the
  proved rules (jumps whose endpoints are proved; step counts checked, not proved: steps of a count: 30 + 6t + 8r, summed in closed form; equal to the direct run at every P
  configuration to 2·10^7 steps) and the overflows simulated cell by cell. For this machine it reproduces the
  overflows of the table above (the seventh, P at step 1,857,557,588, after 3.7·10^8 simulated steps); the
  simulated stretch grows fast with k.
- `py/overflows.py MACHINE B MMAX`: every overflowing phase with at most MMAX bits, run to the next P configuration.
- `py/macro.py 100000` iterates the map; `py/macro.py 9 check LOG` compares it with the overflows of a log;
  `py/macro.py 0 checkO 9` runs every overflow of at most 9 bits; `py/macro.py 0 checkC 6` checks C.
- `py/phasemap.py machine 9 | macro 300 | stuck 12 | orbit K`: the proved phase map (`lean/Orbit.lean`) in
  Python, against the machine, against `py/macro.py`, where it is stuck, and iterated.
- `c/phasefast.c` (`gcc -O2 -o phasefast c/phasefast.c`): `phasefast run 10000000000 100000000` iterates the map
  10^10 phases with the halting tests (22 minutes, about 7 GB); `phasefast dump 100000 500` prints (M, j) at each
  overflow and the string at every 500th, to compare with `py/macro.py`.
- `py/blockers.py 20000`: the blockers at the overflows of the map (see above).
- `py/congruence.py 20000 1500 24`: the congruence search of lead 27 (see above).
- `py/leanfiles.py` writes `lean/Rules.lean` and `lean/Shapes.lean` (shared by the batch; spec as JSON, see its
  docstring).

## Pages

- [`pages/holdouts/1RB---_1RC0RD_1RD1RA_1LE1RB_0LF0LE_1RF0RD/explainer.html`](../../pages/holdouts/1RB---_1RC0RD_1RD1RA_1LE1RB_0LF0LE_1RF0RD/explainer.html)
- [`pages/holdouts/1RB---_1RC0RD_1RD1RA_1LE1RB_0LF0LE_1RF0RD/proof-status.html`](../../pages/holdouts/1RB---_1RC0RD_1RD1RA_1LE1RB_0LF0LE_1RF0RD/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB---_1RC0RD_1RD1RA_1LE1RB_0LF0LE_1RF0RD/lean/check.sh
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB1RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_1RE---`](../1RB1RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_1RE---/README.md): rename A→F, B→E, C→A, D→B, E→C, F→D; it is this table started in state C

<!-- end of related machines -->
