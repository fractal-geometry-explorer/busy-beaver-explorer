# 1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---

bbchallenge id 4320, group G12. Whether it halts from blank tape is **open**. Family: two-level block counter (fast tail, walker in a list of 2s, rebuilds).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RE |
| B | 0RC | 0RF |
| C | 1LD | 1RA |
| D | 1RE | 0LD |
| E | 0LB | 1RC |
| F | 1LE | --- |


## The picture

At the moments the head is in C on a 0 just right of a 1 the tape is

    1^b0 0 1^b1 0 ... 0 1^bk 0 1^l  C>  0^g1 1 0^g2 1 ... 0^gr 1

a list of blocks (the interior), a last block l and a zone of single 1s. In a *regular* configuration b0 is a multiple
of 3, the other b_i are 2 mod 3, l is 1 mod 4, g1 is a positive multiple of 4 and the other gaps are 3 mod 4. One
*sub-round* (to the next such moment) does two independent things:

- **W** on the interior: `(..., x, 3a+2) -> (..., x+3, 2, ..., 2)` (a blocks of 2). In digits a_i = (b_i - 2)/3: drop the
  last digit a, add 1 to the one before, append a zeros.
- **the counter**: l and the zone are a binary counter; l + segments = 4m + 1 during the 2^m sub-rounds of round m
  (`enc`/`dec` in `py/model.py`).

A tail `(..., q, a)` becomes `(..., q+a+1)` after exactly 2^a steps of W, so a list with digits a_1..a_k is a single
block after exactly T = sum_i 2^(a_i + ... + a_k + k - i) steps: the list is the binary expansion of the time it has
left. All of this is proved in Lean for every size (`lean/Subround.lean`, `lean/Collapse.lean`), with the counter in a
more general form: any last block l >= 2 becomes a new gap of l - 1 cells (with the head's cell) and l = 1; with l = 1
the carry removes the leading gaps of 3, takes 4 cells from the next gap (any gap of at least 4) and sets l = 4n + 5, or,
if it meets two 1s side by side before a gap of at least 2, sets l = 4n + 4 and takes 2 from that gap.

With a single block of 3(k + 1) cells left, one sub-round (proved) cuts it into `3 2^k` and turns the last block into
a new gap of the zone (l - 4 cells). The digits of `3 2^k` give T = 2^k - 1, so on its own a rebuild brings back the
same single block after 2^k sub-rounds (`rebuild_cycle`). The single blocks grow because of the *small gaps*: the new
gap shrinks by 4 at each carry into it, and when a carry meets it at 1 or 2 cells (or 0 before 0 or 1) cells of the
counter move into the list. These few dozen sub-rounds per rebuild form the *transient*.

**One sweep machine for every sub-round.** All sub-rounds, the transients included, are the same two sweeps
(`lean/Pass.lean`, `lean/General.lean`). The left sweep erases the last block, moves the block before it one cell to
the right and adds 3 to the block before that; then the head turns right in state A. The right sweep reads the tape in
one of three phases A, E, C (the machine states) with an *open block*, the 1s just left of the head:

| phase | reads | does |
|---|---|---|
| A | 1 | writes 0: the open block closes, an empty one opens; then E |
| E, C | 1 | keeps it (the open block grows); E goes to C, C to A |
| C | 0 after a non-empty open block | the next moment: the open block is the new last block |
| C, E | 0 next to an empty open block | the two cells become `11`; then C |
| E | 0 after an open block | the open block moves one cell right, the block before it grows by 3; A again |
| A | `010` | the same, with one more 1 to read |
| A | `000` | `111`; then C |
| A | `001` | `101`: the open block closes at the middle cell (cells of the counter move into the list) |
| A | `011` | the machine halts |

W is a block of 3a + 2 read from A (`(011)^a 01`), the regular counter is A on `000` and on gaps of 3 (`0001` ->
`1111`); the small gaps are A on `001` and `010`. The function `pstep` is total and proved sound for every size and every
tape (`sub_moment`, `sub_halt`), so the only way the machine can halt is a carry that meets `011` in phase A; the halting
family below reaches the zone `4 3 ... 3 1 0` that way. With it the kernel evaluates the first two transients
(`lean/Transient.lean`), and with the counter in closed form (`lean/Counter.lean`: 4j more cells in the last block make
one counter step take 2^j) and part of a collapse read off the time left (`lean/Advance.lean`) a rebuild becomes a
checked map on three numbers (below), and the run from blank tape is proved to rebuild 200, a single block of 54,075
cells after more than 2^18,024 sub-rounds (`lean/MapRun.lean`).

| rebuild | single block | sub-rounds so far | list afterwards |
|---|---|---|---|
| 1 | 36 | more than 2^10 | `3 2^6 11 5^2 2^2 5` |
| 2 | 57 | more than 2^17 | `3 2^13 11 5^2 2^2 5 2^2 5` |
| 3 | 90 | more than 2^29 | `3 2^25 14 2^2 8 2^3 5` |
| 4 | 123 | more than 2^40 | `3 2^33 17 5 2 5 2^4 11 5 2 8^2 5 2^2 8 2 5` |
| 5 | 216 | more than 2^71 | `3 2^67 14 2^2 8 2^3 5` |
| 6 | 249 | more than 2^82 | `3 2^77 11 5^2 11 5 8 2^2 5 2 5` |
| 7 | 306 | more than 2^101 | `3 2^95 14 5 2^2 5^2` |
| 8 | 327 | more than 2^108 | `3 2^102 17 2^2 5 8 2 20 2^3 8 2^4 5 2^32` |

`py/model.py run` takes regular sub-rounds by arithmetic and everything else by direct simulation (`c/trans.c`): 986
rebuilds, more than 2^105,958 sub-rounds, no halt. Tapes of the same shape do halt: `1^(3k) 0 1^(4k-3) C>0`, k = 3..9.

## The rebuild map

At every rebuild from 4 to 200 the counter is regular when the single block arrives, so a *rebuild state* is three
numbers: a single block of 3(k + 1) cells and the counter in round m with r sub-rounds left (the bits of r, lowest
first, are the gaps of the zone: `cz m r` in `lean/Bits.lean`). The small gaps after the rebuild follow a law that only
the lowest bits of r decide (`py/rebuild_map.py`):

- the transient reads the lowest 3J bits of r, and nothing else decides J. In groups of three bits (value
  b0 + 2 b1 + 4 b2, lowest group first) the words where it stops are a prefix code, recognized by this automaton
  (start in A; `.` = the transient stops after this group):

  | state | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 |
  |---|---|---|---|---|---|---|---|---|
  | A | A | B | C | C | D | . | A | E |
  | B | B | F | B | B | . | C | . | . |
  | C | B | C | C | D | . | A | E | C |
  | D | . | B | C | C | G | . | E | E |
  | E | . | . | C | C | G | G | E | E |
  | F | F | . | . | C | C | G | G | E |
  | G | F | B | B | . | C | . | . | G |

- the list gains 4J - 1 units, so the next single block has 3(k + 4J) cells;
- the counter is regular again, in round m - 3J + 1 with 2(Y - 1) sub-rounds left, Y = floor(r / 8^J);
- the list left has time T = 2^(k+4J-1) - 1 - e(w), with a deficit e that depends only on the word w of the 3J bits.

The collapse takes those T sub-rounds (`collapse_regular`), so the next rebuild state is arithmetic:

    k' = k + 4J - 1,   V = 2^(m-3J+2) - 2(Y - 1) + T,   m' = floor(log2 V),   r' = 2^(m'+1) - V.

The map gives the rebuild state of the run exactly at all 197 rebuilds from 4 to 200 (`check-run 200`); on 1,000 random
rebuild states J, e and r' do not change with k or the bits above w, and the automaton gives J (`check-local 1000`). It
reaches rebuild 986 in about 30 seconds (the hybrid run takes 87 minutes) and rebuild 2,000 in 7 minutes, no halt:
807,819 cells, the counter in round 269,272. The longest transient so far reads 25,312 groups.

In Lean the map is *checked*, rebuild by rebuild. `rstep` (`lean/Map.lean`) takes (k, m, r) and a hint (the 0 bit
where the counter is cut, how many digits of `3 2^k` the transient may touch, its stretches, the next round), runs the
rebuild, the transient on those prefixes (`lean/Frame.lean`: a stretch computed on the first blocks and gaps holds for
every tape further out) and the collapse as arithmetic (`giter_cz`, `T_append`), and returns the next state or
`none`; `rstep_sound` proves that whatever it returns the machine reaches, without a halt. `py/gen_map.py` finds the
hints with Python mirrors of these functions, and `lean/MapRun.lean` has the kernel evaluate `rstep` once per rebuild,
from the third single block to rebuild 200 (`single_map_200`; about 8 minutes, most of it in a few long transients).

### The law for every word (a symbolic case analysis, in Python)

Fed the counter's bits three at a time, the transient stops between two groups at a *frontier*: the pass machine in
mid-sweep, in phase A or C, waiting on the last gap of the zone (the bits above may still add to it), which is then a
single gap of 0, 1 or 2 cells. The list there is a front of one or two blocks and a history of digits beyond them.
Ten shapes of frontier occur, each a family with at most two parameters, and named by the automaton state each one
is equivalent to they are the automaton:

| state | frontier: phase, open gap, front of the list (n, m >= 0; "digit" = the second block is a digit, 2 mod 3) |
|---|---|
| A | C, 0, 1 + 12n, 6 |
| B | C, 0, 8 + 12n, digit |
| C | A, 0, 1, 3, or A, 0, 2 + 12n, digit |
| D | A, 1, 1, digit |
| E | A, 1, 10 + 12n, digit |
| F | C, 0, 12 + 12n, 7 + 12m |
| G | A, 2, 6 + 12n, digit |
| stop | C, 0, 4, 3 + 12m; after it C, 0, 16 + 12n, 3 + 12m on zero groups, and C, 0, 17 + 12n, digit after a 1 |

`py/sym_law.py cases` (6 seconds) runs every shape on each of the 8 group values for every value of its parameters
and every history (`py/sym_engine.py`): the moves of the pass machine on blocks that are affine in the parameters and
on runs of equal blocks of any length; the regular sub-rounds as arithmetic on the list read as a number, 2^q at a
time as in `gfast`; the history as an unknown number whose digits are read only when a move needs one; a loop that
eats a run of any length taken at once, after checking one turn from the general state (induction); and a case split
wherever the parameters do not decide a move. All 80 pairs resolve, in 516 cases. None halts; each lands in one of
the ten families or ends the transient; and which one does not depend on the parameters or the history, except at the
stop shape, where a = 4 and a = 16, 28, ... differ on the group 1. The shapes then give exactly the table of the
automaton, which stops when the front reaches 4 3; after the stop the transient reads zero groups and one more
nonzero group (two after a 1) and ends. The start (the rebuild sub-round and the first groups, for every number z of
leading zero groups, when k >= 3z + 14) lands on the shape the automaton reaches from A, and
at all 27 end cases the counter is the law's, round m - 3J + 1 with 2(Y - 1) sub-rounds left.

So for every word the automaton gives J, the counter after the transient is the law's, and the transient does not
halt, as long as it ends below the top of the counter and the list is long enough for it (each case reads at most a
few digits of the history and borrows powers of 2 from its number, and the arithmetic says whether there are enough).
The list's time left after the transient is arithmetic on k and the word (the cases' operations on the history
number); its closed form 2^(k+4J-1) - 1 - e(w) is checked on random words only. Tests: the same engine run with
concrete histories gives J, T and the length of the list of `py/rebuild_map.py` on 1,000 random rebuild states
(`check 1000`), and every case, instantiated, agrees with the concrete run on 4,000 random parameter values and
histories (`leaves 50`). This is a Python check, not a Lean proof: the engine's rules are the Lean lemmas (`pstep`,
`gfast`, `T_append`, the frames), but the engine itself is not verified.

In Lean, `lean/Front.lean` states the frontiers for all parameters, every history and every counter above the group:
the open gap is `openZ u bs`, the gap u plus whatever the bits bs above add to it (a 0 bit closes it, a 1 bit adds 4).
`lean/FrontCases.lean` (generated by `py/gen_front.py`) proves the 13 cases that are pure moves of the pass machine:
the zero group on the shapes A, B, F, G, stop and C, 0, 17 + 12n, digit, and every nonzero group on that last shape,
where the transient ends. Each proof is the chain of moves, checked by `rfl` for every n, m, history X and bits bs.
The other 503 cases, the other 67 (shape, group) pairs, are proved by `lean/Cases/` (generated by
`py/gen_cases.py`, which replays the engine and writes each of its steps as a lemma of `lean/FrontLib.lean`; 7.8 MB
of Lean, generated by `lean/check.sh` rather than committed, and compiled one file per pair in parallel, about 20
minutes on 4 cores). Each theorem `case_<shape>_<v>` says: from the shape with any parameters, any counter above the
group and any history with enough digits (a length linear in the parameters, stated in the theorem), the machine
reaches the family the case analysis names, or ends the transient at a regular moment (`EndM`), without a halt. A
regular sub-round is `RC.arithG`: arithmetic on the list's time left T, with the counter's 2^q - 1, 2^q or j chunks of
2^q steps (`giter_pm1`, `giter_pow`, `giter_j`); a digit of the history is read by a case split on the list; a carry
into the history is a borrow (`borrow`, `borrowD`: some list D' with T(D') + 2^e = T(D) + c and a bound on its
length); a loop over a run is an induction on its length; a split on the parameters is a residue or an order split.
The Lean tree splits more finely than the engine: 784 leaves for the 503 cases. Not yet in Lean: the start (the
rebuild sub-round and the first groups), that the counter at the end is the law's, and the closed form of T.

### Can the run outgrow its counter or its list?

The case analysis covers a transient as long as it ends below the top of the counter and the list is long enough for
it, so these are the only two ways out of the law. `py/margins.py` measures both along the run of the map.

**The list never runs out first.** On 1,500 random words (`margins.py list 1500`, J up to about 45) the transient
gives the word's J and e for every list length k ≥ 3J: the list it needs is at most three cells per group read (at
most 3z + 15, z the leading zero groups). The counter must hold the word's 3J bits anyway, and m ≤ k at every rebuild (below), so a list
too short for its transient would need a word that has already reached the top of the counter.

**The top of the counter.** The map is exact arithmetic, and two cases cover it. With Y = r >> 3J and
V = 2^(m-3J+2) - 2(Y - 1):

- *normal*, V > e + 1: m' = k' and r' = (2^k' - 2^(m-3J+2)) + (2Y - 1 + e), with the last term below 2^(m-3J+2).
  So the bits the word did not read move down to the bottom, shifted up by one, plus e. On top of them comes a run of
  k' - m + 3J - 2 ones (7J - 3 when m = k), one 0 below it.
- *drop*, V ≤ e + 1: m' = k' - 1 and r' = 1 + e - V, far below 2^m'. So from the top of 1 + e - V to the top of the
  counter every bit is 0.

So m is k or k - 1 at every rebuild. The counter is a stack: each word reads its 3J bits off the bottom, and each
rebuild pushes a run of ones about 7J long on top. Runs of ones are cheap for the word only up to a point. In them the
automaton cycles through E, C and G, and it stops at the second separating 0 after one that falls on the middle bit
of a group while in E (about 5 separators in all, if the alignments are random). Stretches of 0s are different: A, B
and F loop on the zero group, so a word that enters one of them in those states reads all of it. Most long words
read such a stretch. The stretches come from e(w), which holds long runs of zeros, and above all from drops. A drop
needs J > about m/8.5 (e has 4J to 7J bits). It leaves 0s from the top of 1 + e - V to the top of the counter, the
stack buries them under new runs, and hundreds of rebuilds later they reach the bottom.

| drop at rebuild | J | m | 0s left on top | read again at rebuild | J there | 3J/m there |
|---|---|---|---|---|---|---|
| 84 | 411 | 3,413 | 2,234 | 140 | 883 | 0.32 |
| 241 | 2,141 | 19,044 | 13,186 | 493 | 4,835 | 0.32 |
| 493 | 4,835 | 45,164 | 33,730 | 987 | 25,312 | 0.72 |
| 987 | 25,312 | 105,958 | 72,447 | | | |

At rebuild 987 the word read the 33,523 zeros of the stretch, then the runs of 17,582, 14,039 and 9,384 ones that
the long words right after the drop had pushed on it. That is 75,936 of 105,958 bits, the closest the run has come
to the top of its counter. Its drop left the 72,447 zeros, but its own e(w) holds the word's runs of ones as runs of
zeros of nearly the same lengths, and the next word was short (J = 29), so no long runs sit on that stretch. After it
the cascade died out. From rebuild 988 to 6,000 there is no drop and no word reads more than 7% of the counter
(`margins.py run 6000`, 17 minutes: 3J/m at most 0.070, at rebuild 5,740 with J = 18,612). The single block reaches
2,919,690 cells (k = 973,229), the counter round 973,229: more than 10^292,970 steps.

So the run outgrows its counter only if one word crosses every separator above it. That means hundreds of runs of
ones, each a chance of about 1 in 5 to stop it, and at the top a drop's stretch of zeros it must enter in A, B or F.
Or a drop must leave no separators between the next word and its zeros. This is a heuristic, not a proof. The open
question is now the arithmetic of e(w), where the word's runs reappear, and of the separators' alignments mod 3.

## What is established

**Proved in Lean, kernel only** — The halting configurations: The machine stops exactly when it reads the symbol of a halting transition (F1); the generated statement covers every configuration. (`step_none_iff`, `lean/Blank.lean`)

**Proved in Lean, kernel only** — No halt in the first 10,000 steps: The list simulator of the shared library, proved to agree with the machine's semantics, runs 10,000 steps from blank tape without a halt, evaluated by Lean's kernel. (`blank_runs_kernel`, `lean/Blank.lean`)

**Proved in Lean with `native_decide`** — No halt in the first 10^7 steps: The same run, evaluated by compiled code. (`blank_runs_native`, `lean/Blank.lean`)

**Computed (trusted C/Python)** — No halt in the first 10^9 steps: The C simulator `tools/c/triage.c` runs 10^9 steps without a halt; at the end 189 cells have been visited and 86 of them hold a 1. (`holdouts/triage.json`)

**Proved in Lean, kernel only** — Three rounds of the run, for any tape further left: Three consecutive rounds of the run from blank tape (between moments the head is in C on the first 0 right of everything written), each proved for every tape left of the cells it visits, with its exact step count. (`lean/Rounds.lean` (generated by `py/gen_rounds.py`))

**Computed (trusted C/Python)** — No halt in 3·10^10 steps; three rebuilds: Direct simulation for 3·10^10 steps. At the moments the head is in C on the first 0 right of everything written the tape is a list of blocks of 1s separated by single 0s; the last block grows by 4 per round; in walking phases the rounds satisfy T′ = 2T + 4 exactly. Rebuilds of the list at steps 72,083, 11,004,261 and 22,558,329,283 (the table). (`tools/c/tmrun.c` (`at C R`))

**Computed (trusted C/Python)** — Between rebuilds: a binary counter that applies one list operation per tick: At the moments the head is in C on a 0 just right of a 1, the tape is a list of blocks of 1s separated by single 0s (the interior), a last block l, and to the right of the head a zone of single 1s. Call it regular if the first block is a multiple of 3, the other interior blocks are 2 mod 3, l is 1 mod 4, and the gaps of the zone are 0 mod 4 (the first, counted from the head) and 3 mod 4 (the others). From one such moment to the next (a sub-round) a regular configuration changes in two independent ways. The interior takes one step W: (..., x, 3a + 2) becomes (..., x + 3, 2, ..., 2) with a blocks of 2. The last block and the zone are a binary counter: with segments s1 = g1, si = gi + 1, a last block l ≥ 5 becomes a new first segment l − 1 and l = 1; with l = 1 the n leading segments equal to 4 are removed, the next segment loses 4 cells (blank tape supplies them if there is none) and l = 4n + 5. So l plus the segments is 4m + 1 for 2^m sub-rounds (one round, what earlier notes called the fast counter), then m grows by 1. Checked against the machine one sub-round at a time: of the 300,000 sub-rounds after step 2,918 (12.6 million steps) the 299,954 regular ones all follow this; the other 46 are the transients of the first two rebuilds. The rules are now proved in Lean for all sizes (the claims below); this check of the machine stays as a test. (`holdouts/1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---/py/model.py` (`check 300000`))

**Computed (trusted C/Python)** — The binary expansion, checked on the machine: With digits ai = (bi − 2)/3, W removes the last digit a, adds 1 to the digit before it and appends a zeros; the sum of all digits plus their number never changes. A tail (..., q, a) becomes (..., q + a + 1) after exactly 2^a steps, so an interior with digits a1, ..., ak is a single block after exactly T = Σi 2^ai + ... + ak + k − i steps of W: the positions of the 1s in the binary expansion of T are the partial sums of the list read from the right. Checked on the machine: the model predicts single blocks at sub-rounds 1,616 and 261,907 of that run and both are there; W steps and counter steps taken many at once agree with the machine in 28 test jumps; and after the third rebuild the lists at seven ends of rounds, up to step 2.8·10^10, are those of a direct run of the machine (`3 2^25 14 2 8 2 14 | 85` at step 22,558,329,286, ..., `3 2^12 20 2^6 14 2 8 2 14 | 109` at step 28,107,393,382). (`holdouts/1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---/py/model.py` (`check 300000`, `partial`, `rounds`))

**Proved in Lean, kernel only** — Every sub-round of the regular kind, for all sizes: Five machine rules, each for every value of its parameters and every tape further out: `glong` (last interior block 3a + 2, last block b + 2: W on the interior, the last block becomes 1 and a new zone gap of b + 1), `gshort` (last block 1: the carry removes the leading gaps of 3, takes 4 cells from the next gap, which has at least 4, and sets the last block to 4n + 5), `gzero` (the carry meets two 1s side by side before a gap of at least 2: last block 4n + 4), and the two rebuild sub-rounds below. Put together (`subround`): at the moments the head is in C on a 0 right of a 1, a configuration `1^(3q) 0 [digits] 0 1^l C> [gaps]` with at least one digit goes in one sub-round to W of its digits and one step `gstep` of the counter, which is defined for every last block and every zone except at the *small gaps* (a carry meeting a gap of 1 or 2 cells, or two 1s side by side before a gap of 0 or 1). The rules are proved by `rfl` steps, the crossing lemmas and `omega`; the earlier observation that W and the counter do not influence each other is now a theorem. (`glong`, `gshort`, `gzero` in `lean/Subround.lean` (generated by `py/gen_subround.py`); `subround` in `lean/Collapse.lean`)

**Proved in Lean, kernel only** — The list is the binary expansion of the time it has left: With T(x :: r) = 2^x (1 + 2 T(r)) on the digits listed nearest the head first, W lowers T by exactly 1 and keeps the first block plus the digits plus their number (`T_W`, `mass_W`). So from any configuration of this shape the machine reaches the single block of 3 · mass cells after exactly T sub-rounds, the counter advanced T times, if the counter meets no small gap on the way (`collapse`; `advance` for fewer sub-rounds). A regular counter (last block 1 mod 4, every gap 3 mod 4: the binary counter of the picture) never meets one (`regular_total`), so from a regular configuration the collapse always happens, without a halt (`collapse_regular`). (`T_W`, `collapse`, `regular_total`, `collapse_regular`, `lean/Collapse.lean`)

**Proved in Lean, kernel only** — The rebuild sub-round, and why single blocks grow: A single block of 3(k + 1) cells with last block b + 5 becomes `3 2^k` with last block 5 and a new zone gap of b cells in front (`rebuild`, rule `single`); with last block 1 and a first gap of at least 2 it becomes `3 2^k` with last block 4 and the first gap 2 shorter (`rebuild_one`, rule `singleone`). The digits of `3 2^k` give T = 2^k − 1 and mass k + 1, so if the counter meets no small gap the single block comes back with the same 3(k + 1) cells after 2^k sub-rounds (`rebuild_cycle`). The single blocks of the run grow (36, 57, 90, ...) only because small gaps move cells of the counter into the list; the new gap a rebuild makes (b, a multiple of 4 when the last block is 1 mod 4) is where the first small gap comes from. (`rebuild`, `rebuild_one`, `rebuild_cycle`, `lean/Collapse.lean`)

**Proved in Lean, kernel only** — The run from blank tape through the first rebuild, to step 71,355: The kernel evaluates the first 2,918 steps (to `3 2 8 5 14 | 9`) and the counter `gstep`; the rest is the rules above: 1,616 sub-rounds to the single block of 36 cells (`first_single`), the rebuild sub-round (`first_rebuild`, step 70,871: `3 2^11 | 5`), and 13 more sub-rounds to step 71,355, where the carry meets a gap of 2 cells, the first sub-round of the run the rules do not cover (`first_uncovered`). (`reach_2918`, `first_single`, `first_rebuild`, `first_uncovered`, `lean/Run.lean`)

**Proved in Lean, kernel only** — Every sub-round, small gaps included: the pass machine: At every moment (the head in C on a 0, a last block l on its left, then any blocks of 1s separated by single 0s, and on its right any zone of gaps) the next sub-round is the same two sweeps. The left sweep (`start`) erases the last block, moves the block before it one cell to the right and adds 3 cells to the block before that. The right sweep reads the tape in one of three phases A, E, C (the machine states) with an *open block*, the 1s just left of the head. On a 1, A writes 0 (the open block closes, an empty one opens) and E and C keep it; the phase goes A, E, C, A. On a 0: C after a non-empty open block is the next moment (the open block is the new last block); C or E next to an empty open block fill two cells; E after an open block, and A on `010`, move the open block one cell right, add 3 to the block before it and start again in A; A on `000` writes `111` and goes on in C; A on `001` writes `101` (the open block closes at the middle cell); A on `011` halts. Each move is a machine rule proved for every size (`lean/Pass.lean`, generated by `py/gen_pass.py`); `pstep` puts them into one total function, and `sub_moment` and `sub_halt` prove that a sub-round it computes is a run of the machine with exactly its number of steps, and that a halt it finds is a halt of the machine. So the halts of the machine are exactly the carries that meet `011` in phase A. W on the list and the binary counter (the rules above) are the cases where the right sweep only meets blocks 2 mod 3 and gaps 3 mod 4; the small gaps are the moves A on `001` and `010`, which move cells of the counter into the list. (`pstep_next`, `pstep_done`, `pstep_halt`, `sub_moment`, `sub_halt`, `subs_moment` in `lean/General.lean`; the moves in `lean/Pass.lean`)

**Proved in Lean, kernel only** — The run from blank tape through two transients, to the third single block: From step 71,355 (where the first small gap was the end of the proved run) the kernel evaluates the pass machine: 7 sub-rounds of the first transient to the regular configuration `3 2^6 11 5^2 2^2 5 | 5` with zone gaps 4 7 3 (`first_transient`); `collapse`, with the counter evaluated by the kernel (260,270 counter steps), gives the second single block, 57 cells (`second_single`); `rebuild` and 24 more sub-rounds of the pass machine give `3 2^13 11 5^2 2^2 5 2^2 5 | 9`, a regular configuration (`second_transient`); and `collapse_regular` the third single block, 90 cells, 536,840,942 sub-rounds later, with a regular counter (`third_single`). Direct simulation puts that block at step 22,558,329,283; the Lean proof does not evaluate any machine step past step 2,918, and the counter after the third block is left existential (it needs the counter in closed form). (`first_transient`, `second_single`, `second_transient`, `third_single`, `lean/Transient.lean`)

**Proved in Lean, kernel only** — The rebuild map, checked: the run from blank tape to rebuild 200, without a halt in more than 10^5,425 steps: Three pieces make a rebuild cost the kernel only the transient, on short prefixes, whatever the size of the single block. **Frames** (`lean/Frame.lean`): a stretch of the pass machine or of the counter computed on the first blocks of the list and the first gaps of the zone (`subsF`, `gfastF`, which return `none` when a move would need more) holds for every tape further out, and T(F ++ X) = T(F) + 2^σ(F) T(X). **The counter as a number** (`lean/Bits.lean`): `cz m r` is the regular counter in round m with r sub-rounds left, built from the bits of r; it is cut at a 0 bit into a low part the transient reads and a tail it never touches (`cz_split`), put back together after the transient (`cz_join`), and N counter steps are arithmetic on it (`giter_cz`). **The checked map** (`lean/Map.lean`): `rstep` takes a rebuild state (k, m, r) and a hint (where to cut the counter, how many digits of the list to keep, the stretches of the transient, the next round), runs the rebuild, the transient on the prefixes and the collapse, and returns the next rebuild state or `none`; `rstep_sound`: whatever it returns is reached by the machine, without a halt. When the counter has no 0 bit above the bits the transient reads, the zone is evaluated to its end (no tail on the right). `lean/MapRun.lean` (generated by `py/gen_map.py 200`, which computes the hints with Python mirrors of these functions) gives the 197 rebuild states from the third single block (`rcfg 29 28 28950`) to rebuild 200 and the kernel evaluates `rstep` once per rebuild. `single_map_200`: the run from blank tape reaches the single block of rebuild 200, 54,075 cells, the counter in round 18,024 (so more than 2^18,024 sub-rounds, more than 10^5,425 machine steps), and does not halt before it. This replaces the chain of segments to rebuild 40 (`lean/Chain.lean`, 3 minutes of kernel time; the map gets there in 21 seconds and to rebuild 200 in about 8 minutes, most of it in the few long transients). Its two lemmas stay in use: **scaling** (`giter_scale`, `gfast_sound`: with 4j more cells in the last block one counter step takes 2^j) and **part of a collapse** (`advance_to`: after M sub-rounds the digits are the only list D′ with T(D′) + M = T(D)). (`single_map_200`, `lean/MapRun.lean` (generated by `py/gen_map.py 200`); `rstep`, `rstep_sound`, `reach_step`, `lean/Map.lean`; `cz_split`, `cz_join`, `giter_cz`, `lean/Bits.lean`; `pass_frame`, `advance_frame`, `lean/Frame.lean`; `advance_to`, `lean/Advance.lean`; `giter_scale`, `gfast_sound`, `lean/Counter.lean`)

**Heuristic / observed** — How the small gaps evolve after each rebuild: a map on three numbers: At every rebuild from 4 to 200 the counter is regular when the single block arrives, so a *rebuild state* is three numbers: a single block of 3(k + 1) cells and the counter in round m with r sub-rounds left (the bits of r, lowest first, are the gaps of the zone). The transient (the sub-rounds with small gaps after the rebuild) follows a law that only the lowest bits of r decide. It reads the lowest 3J bits of r, and nothing else decides J: read in groups of three bits (value b0 + 2b1 + 4b2, lowest group first), the words where it stops form a prefix code recognized by a 7-state automaton (start in A, `AUTO` in `py/rebuild_map.py`). The list gains 4J − 1 units, so the next single block has 3(k + 4J) cells; the counter is regular again in round m − 3J + 1 with 2(⌊r/8^J⌋ − 1) sub-rounds left; and the list left has time T = 2^(k+4J−1) − 1 − e(w), with a deficit e that depends only on the word w of those 3J bits. The collapse then takes T sub-rounds (proved), so the next rebuild state is arithmetic: V = 2^(m−3J+2) − 2(⌊r/8^J⌋ − 1) + T, m′ = ⌊log2 V⌋, r′ = 2^(m′+1) − V. Checked: the map gives the rebuild state of the run exactly at all 197 rebuilds from 4 to 200 (`check-run 200`); on 1,000 random rebuild states J, e and r′ do not change with k or with the bits above w, and the automaton gives J (`check-local 1000`). For every word the automaton, the counter after the transient and the absence of a halt are now checked by a symbolic case analysis (next); the closed form of T, with e depending only on w, is checked on random words only, and in Lean each transient is still evaluated (below); the automaton is in The rebuild map above. (`holdouts/1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---/py/rebuild_map.py` (`check-run 200`, `check-local 1000`, `auto`))

**Computed (trusted C/Python)** — The rebuild law for every word: a symbolic case analysis of the transient: Fed the counter's bits three at a time, the transient stops between two groups at a *frontier*: the pass machine in mid-sweep, in phase A or C, waiting on the last gap of the zone (the bits above may still add to it), which is then a single gap of 0, 1 or 2 cells; the list there is a front of one or two blocks and a history of digits beyond them. Ten shapes of frontier occur, each a family with at most two parameters (the front block grows by 12 cells per loop). `py/sym_law.py` runs every shape on each of the 8 group values for every value of its parameters and every history: the moves of the pass machine on blocks that are affine in the parameters and on runs of equal blocks of any length; the regular sub-rounds as arithmetic on the list read as a number, 2^q at a time as in `gfast`; the history as an unknown number whose digits are read only when a move needs one; a loop that eats a run of any length taken at once, after checking one turn from the general state (induction); and a case split wherever the parameters do not decide a move. All 80 pairs resolve, in 516 cases: none halts, each lands in one of the ten families or ends the transient, and which one does not depend on the parameters or the history, except at the stop shape. Named by the automaton state each shape is equivalent to, the shapes give exactly the table of the automaton, which stops when the front of the list reaches 4 3; after the stop the transient reads zero groups and one more nonzero group (two after a 1) and ends. The start (the rebuild sub-round and the first groups, for every number z of leading zero groups, when k ≥ 3z + 14) lands on the shape the automaton reaches from A, and at all 27 end cases the counter is the law's, round m − 3J + 1 with 2(⌊r/8^J⌋ − 1) sub-rounds left. So for every word the automaton gives J, the counter after the transient is the law's, and the transient does not halt, as long as it ends below the top of the counter and the list is long enough for it; the list's time left after the transient is arithmetic on k and the word. Tests: the same engine run with concrete histories gives J, T and the length of the list of `py/rebuild_map.py` on 1,000 random rebuild states, and every case, instantiated, agrees with the concrete run on 4,000 random parameter values and histories. A Python check, not a Lean proof: the engine's rules are the Lean lemmas (`pstep`, `gfast`, `T_append`, the frames), but the engine itself is not verified. (`holdouts/1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---/py/sym_law.py` (`cases`, `check 1000`, `leaves 50`); `py/sym_engine.py`, `py/sym_lin.py`)

**Computed (trusted C/Python)** — What the regular rules leave, and the pass machine against the run: Before the pass machine: the hybrid run of `py/model.py` through 243 rebuilds with every directly simulated sub-round checked against the regular rules (`c/rules_check.c`): of 70,055 sub-rounds simulated directly in the transients, 67,154 follow a regular rule with its exact step count and none differs; 2,901 are not covered, 1,584 where the carry meets a small gap and 1,317 where cells the small gaps moved into the list leave a last block that is not 2 mod 3. The pass machine covers all of them. Its Python mirror `py/passm.py`, move for move the Lean function, agrees with the machine on 30,000 random tapes (configuration, step count and halts) and, in the hybrid run through 243 rebuilds, gives for every one of the 24,034 stretches the run simulates cell by cell (the transients and the sub-rounds where the counter reaches an irregular gap; 363,515,147 machine steps) exactly the configuration and step count of `c/trans.c`. (`py/rules_check.py`, `c/rules_check.c`; `py/passm.py` (`check 30000`, `hybrid 243`))

**Computed (trusted C/Python)** — Tapes of the same shape that halt: A rebuild starts when the interior is a single block. The tape 1^3k 0 1^4k−3 with the head in C on the 0 right of it, a single block of 3k cells meeting the counter exactly at the start of round k − 1, halts for every k from 3 to 9 (after 311, 659, 1,343, 2,699, 5,399, 10,787 and 21,551 steps; direct simulation). So no property of the shape alone can show that the machine never halts: it depends on which single blocks and counter values the run from blank tape produces. (`holdouts/1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---/py/model.py` (`halting 9`), `c/trans.c`)

**Proved in Lean, kernel only** — Every frontier case of the law, for all parameters: `lean/Front.lean` states the frontiers of the case analysis in Lean, for every value of the parameters, every list beyond the front and every counter above the group: the open last gap is `openZ u bs`, the gap u plus whatever the bits bs above add to it (`openZ_false`, `openZ_true`, `openZ_eq`). `lean/FrontCases.lean` (generated by `py/gen_front.py`) proves the 13 of the 516 cases that are pure moves of the pass machine: the zero group on the shapes A, B, F, G and the stop shape and on C, 0, 17 + 12n, digit, and every nonzero group on that last shape, where the transient ends at a moment. Each proof is the chain of `pstep` moves, each checked by `rfl` with n, m, the history and the bits above as variables. The other 503 cases (the other 67 pairs of shape and group) are proved by `lean/Cases/`, generated by `py/gen_cases.py`, which replays the engine and writes each of its steps as a lemma of `lean/FrontLib.lean` (7.8 MB of Lean, generated by `lean/check.sh` rather than committed, about 20 minutes on 4 cores). Each theorem says: from the shape with any parameters, any counter above the group and any history with enough digits (a length linear in the parameters, stated in the theorem), the machine reaches the family the case analysis names, or ends the transient at a regular moment, without a halt. A regular sub-round is arithmetic on the list's time left with 2^q − 1, 2^q or j chunks of 2^q counter steps (`RC.arithG`); a digit of the history is a case split on the list; a carry into the history is a borrow (some list D′ with T(D′) + 2^e = T(D) + c, with a bound on its length); a loop over a run is an induction on its length. So the step from every frontier to the next is proved for every word. Not yet in Lean: the start, that the counter at the end is the law's, and the closed form of the list's time left. (`front_G_0`, `front_C5D_1`, ..., `lean/FrontCases.lean`; `case_C007_1`, ..., `lean/Cases/` (generated by `py/gen_cases.py`); `RC.arithG`, `borrow`, `borrowD`, `lean/FrontLib.lean`; `openZ`, `Reach`, `ReachM`, `lean/Front.lean`)

**Computed (trusted C/Python)** — Outgrowing the counter or the list: the arithmetic of the map, to rebuild 6,000: The law for every word covers a transient as long as it ends below the top of the counter and the list is long enough for it. The list never runs out first: on 1,500 random words the transient gives the word's J and e for every list length k ≥ 3J, and m ≤ k at every rebuild. The map is exact arithmetic in two cases, with Y = ⌊r/8^J⌋ and V = 2^(m−3J+2) − 2(Y − 1): if V > e + 1, m′ = k′ and r′ = (2^k′ − 2^(m−3J+2)) + (2Y − 1 + e), so the unread bits move to the bottom and a run of about 7J ones goes on top; if V ≤ e + 1 (a *drop*), m′ = k′ − 1 and r′ = 1 + e − V, so the top of the counter is all 0s. `py/margins.py run 6000` checks these identities at every rebuild from 4 to 6,000 (17 minutes). The automaton loops on zero groups in A, B and F, so a stretch of 0s that reaches the bottom of the counter is read whole: the long words. Drops happen at rebuilds 5, 84, 241, 493 and 987 only; the stretch left at 493 (33,730 zeros) was read at rebuild 987 together with the long runs of ones on it, 75,936 of 105,958 bits (3J/m = 0.717), the closest the run has come to the top of its counter. From rebuild 988 to 6,000 there is no drop and no word reads more than 7% of the counter; the single block reaches 2,919,690 cells, the counter round 973,229 (more than 10^292,970 steps). That the run never reaches the top is a heuristic: a word must cross every separating 0 above it, hundreds of them, each a chance of about 1 in 5 to stop it. (`holdouts/1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---/py/margins.py` (`run 6000`, `list 1500`))

**Heuristic / observed** — 986 rebuilds without a halt: A run that takes the regular sub-rounds by arithmetic (any number at once, with the two rules above) and gives everything else to the machine itself, cell by cell: the transient after each single block, and the sub-rounds where the counter reaches an irregular gap of the zone. It passes 986 rebuilds; by then the counter has made more than 2^105,958 sub-rounds, so the machine more than 10^31,896 steps, and the single block has 317,877 cells. A halt could only be found by the direct part and none was. The sub-rounds the arithmetic part takes are of the kinds proved in Lean for all sizes (W and the regular counter); the direct part is now covered by the pass machine as well (proved for every sub-round); what rests on Python is the arithmetic that takes many regular sub-rounds at once (`applyW`, `enc`/`dec`); through rebuild 200 that arithmetic is now proved too (above). The small gaps never hold the counter for long: in the segments of `py/gen_chain.py` through rebuild 200 (single block 54,075 cells), each of the 1,410 places where the counter is stuck is cleared by 1, 2 or 3 sub-rounds of the pass machine (403, 933 and 74 times). The rebuild map (above) gives the same rebuild 986 (single block 317,877 cells) in about 30 seconds instead of 87 minutes, and goes on to rebuild 2,000 in 7 minutes without a halt: a single block of 807,819 cells, the counter in round 269,272 (so more than 10^81,058 steps); the longest transient so far reads 25,312 groups of the counter's bits. Through rebuild 986 it does not rest on the law alone: `py/gen_map.py 986` computes the hints of all 983 rebuilds from the third single block with the Python mirrors of the Lean checker (each transient evaluated by the pass machine on prefixes and checked to stay inside them, 12,166 stretches, 4 minutes), and every next state is the one the map gives. Past rebuild 986 the run rests on the law above. (`holdouts/1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---/py/model.py` (`run 986`), `c/trans.c`, `py/rebuild_map.py` (`run 2000`), `py/gen_map.py` (`986`))

**Open** — Does it halt from blank tape?: Not known. Every sub-round is proved, with its exact step count, and the only halting move is a carry that meets `011` in phase A (a gap of one cell followed by two 1s side by side). Tapes of the same shape do halt that way (the halting family above ends with the zone `... 3 3 1 0`). So the question is arithmetic: whether the single blocks and counters that this run produces ever lead a carry to such a place. The halting family needs the single block to arrive exactly when a round of the counter starts, a coincidence of two binary numbers that the run has avoided so far. The rule for the counter at the moment the single block arrives is now found: a rebuild is a map on three numbers (above), proved in Lean as a checked map and run by the kernel to rebuild 200 (more than 10^5,425 steps). The law for every word of the automaton is now checked by a symbolic case analysis in Python (above), and in it no transient halts; in Lean every step of that analysis from one frontier to the next is proved for every word, the start and the end not yet. So the machine can halt only where that analysis does not reach: a transient that runs to the top of the counter (the automaton has not stopped within its m bits, as in the halting family, where the single block meets the counter at the start of a round) or a list too short for its transient. Whether the run of the map, pure arithmetic on k, m and r, ever gets there is the open question. Its arithmetic (above) says that the list never runs out before the counter does and that the long words are stretches of zeros left by big words; the run came closest at rebuild 987 (75,936 of 105,958 bits), and from rebuild 988 to 6,000 no word reads more than 7% of the counter.

## For later

1. Lean: the rest of the law for every word. Every frontier case is proved (`lean/FrontCases.lean`, `lean/Cases/`);
   left are the start (the rebuild sub-round and the first groups, for every number z of leading zero groups), the
   end (the counter after the transient is the law's, round m - 3J + 1 with 2(Y - 1) sub-rounds left), chaining the
   cases along the automaton, and the closed form 2^(k+4J-1) - 1 - e(w) of the list's time left, with e depending
   only on the word.
2. Lean: push the checked map past rebuild 200 (`py/gen_map.py R`). Most rebuilds cost the kernel well under a second,
   but the cost grows fast with the length J of the word (rebuild 140, J = 883: 100 s), and one of rebuilds 901 to
   1,000 reads 25,312 groups, so the long words need the law of item 1 rather than evaluation.
3. The arithmetic of e(w): its runs of zeros mirror the word's runs of ones, and it decides when a drop happens and
   what the next words read. A bound on e and on the separators' alignments mod 3 could turn the heuristic of
   "Can the run outgrow its counter or its list?" into a proof, or find the rebuild where a word reaches the top.
4. The same skeleton appears in `1RB0RF_1RC1LB_1LD1RE_1LB0LD_1RF0RC_1RA---` (blocks 2a + 1, last block a multiple
   of 5) and probably in `1RB0RE_1LC0RA_1RE1LD_0LB0LF_1RA1RA_0LD---`; their sub-rounds may be sweep machines as well.

## Reproduce

```sh
. /etc/profile.d/lean.sh      # after scripts/setup-lean.sh
holdouts/1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---/lean/check.sh
gcc -O2 -o tmrun tools/c/tmrun.c && ./tmrun 1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE--- 30000000000 at C R 400      # 2 minutes; the round ends that py/model.py rounds compares with
gcc -O2 -o triage tools/c/triage.c && ./triage 1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE--- 1000000000
python3 holdouts/1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---/py/model.py check 300000     # machine against model, sub-round by sub-round
python3 holdouts/1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---/py/model.py partial          # jumps of many sub-rounds against the machine
python3 holdouts/1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---/py/model.py rounds           # round ends after the third rebuild against the direct run
python3 holdouts/1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---/py/model.py halting 9        # the halting tapes 1^(3k) 0 1^(4k-3) C>0
python3 holdouts/1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---/py/model.py run 986          # the hybrid run (87 minutes; run 243 takes 5)
python3 holdouts/1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---/py/gen_subround.py > lean/Subround.lean   # the Lean rules
python3 holdouts/1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---/py/rules_check.py 243      # 8 minutes: the regular rules against every directly simulated sub-round
python3 holdouts/1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---/py/gen_pass.py > lean/Pass.lean      # the moves of the pass machine
python3 holdouts/1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---/py/passm.py check 30000     # the pass machine against the machine, random tapes
python3 holdouts/1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---/py/gen_map.py 200 > lean/MapRun.lean     # the hints of the checked map to rebuild 200
python3 holdouts/1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---/py/rebuild_map.py check-run 200   # the map against the rebuild states of the run
python3 holdouts/1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---/py/rebuild_map.py check-local 1000   # J, e, r' from the low bits alone
python3 holdouts/1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---/py/rebuild_map.py run 2000   # the map to rebuild 2,000 (7 minutes)
python3 holdouts/1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---/py/sym_law.py cases        # the law for every word: every frontier shape and group, symbolically (6 seconds)
python3 holdouts/1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---/py/sym_law.py check 1000   # the engine with concrete histories against the rebuild map (1 minute)
python3 holdouts/1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---/py/sym_law.py leaves 50    # every symbolic case against concrete runs (30 seconds)
python3 holdouts/1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---/py/gen_front.py > lean/FrontCases.lean   # the 13 frontier cases that are pure pass machine moves
python3 holdouts/1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---/py/gen_cases.py holdouts/1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---/lean   # the other 503 frontier cases, lean/Cases/ (3 minutes; check.sh runs it)
python3 holdouts/1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---/py/margins.py run 6000     # the map's identities and margins to rebuild 6,000 (17 minutes)
python3 holdouts/1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---/py/margins.py list 1500    # the list each word needs (30 seconds)
python3 holdouts/1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---/py/passm.py hybrid 243      # 6 minutes: against every directly simulated stretch of the hybrid run
```

Pages: [`explainer.html`](../../pages/holdouts/1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---/explainer.html), [`proof-status.html`](../../pages/holdouts/1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---/proof-status.html).
