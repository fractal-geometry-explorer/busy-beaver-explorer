# The mark rules of 1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LD1RE, proved from the transition table

**State of play (October 22).** Details in the sections below; this is the short version.
- *Proved:* the mark rules (from the transition table) and that, within them, the machine can halt only through a
  right-end run of about log₂ n meetings, or through marks touching.
- *Exhaustive (mark model):* every clean tape n < 2^61 reaches the next without halting or contact: at least
  1.8 × 10^52 steps (to 2^59: 2.9 × 10^50). Two independent drivers: the disk engine to 2^51 and the depth-first engine to 2^59, which matches
  it at all 50 shared levels. The longest chain below 2^59 is 19 (n = 114,928,805,503,523,374, predicted by the line
  search before the exhaustive run reached it), the largest jump 327.
- *Two-marker reduction:* every halt starts at a GMM state (gap, marker m, end marker) whose own segment halts. Every
  such state up to width 262,143 was run: only (4, 13) halts, and the machine never reaches it.
- *Route exclusion, all widths:* the 759,918 ways from a GMM state into the plain loop decided within 46 binary
  digits (the same at every ratio m/E) leave 866,445 candidate states below their lock caps, and none halts; nor do
  the 1,989 chains through the extra-wall loop. They include the way into every sampled deep run that uses the loop;
  the undecided share is 2.0 × 10⁻⁷. With the sharp lock this needs no search above width 2^49.7: every plain entry
  in the route tree to 62 binary digits has a σ ceiling of at most 52.86 (no halt above width 2^59.24, inside the
  exhaustive range), and the undecided share there is 8.2 × 10⁻¹⁰ (October 23, "Route ceilings").
- *Why chains fail on these tapes:* a loop that contracts c directions runs without a 2-adic limit only in families
  with at least c free numbers (plain loop 2, extra-wall loop 3, k extra walls 2 + k). GMM states have 2, so the
  extra-wall loop has a fixed cap per way in (observed 0 to 3), and the plain loop is stopped by the lock at two thirds
  of the halvings. Each cycle's own states have 1.
- *Rules alone allow halts:* hand-built tapes with 3 or more free numbers halt at every width tried.
- *The machine's tail is a staircase of lines:* every GMM state a class of n reaches is a line of GMM states; on a line
  the plain loop costs 6 digits per pass (1.5 per halving) until a hard reach, and lines that reach further are rarer
  by about a digit per halving. Three lines carry most of the machine's share at 10, 11–12 and 13–14 halvings, and the
  machine's lines are no luckier than random lines of the same shape. So the 1.9 digits per halving its tail shows
  from 8 to 12 halvings cannot persist; on average the price is the plane's 2.5 (see "Where the price goes back up").
- *Records beyond the exhaustive range:* following the luckiest lines gives explicit clean tapes, checked by direct
  runs and the certified macro simulation: 16.5 halvings at 52 digits and 16.6 at 55 (chain 16, both below 2^55 and
  both found by the exhaustive run too), 19.7 at 57, 20.8 at 68, 22.1 at 75, 23.1 at 77, 25.4 at 85, 29.6 at 94. The closest approach stays near 0.3 of the binary length: a cycle gets about a third of the way to a halt
  (see "How close anything comes to halting").
- *How late a run enters the loop:* a run that halts through the plain loop needs σ = 3s + 2λ ≥ log₂W − 6.38 at its
  first pass start, where the right end sits 2^-s of the width W away and |L₁| = 2^λ·W. σ is unchanged by a pass, and
  an exact search of the loop's end shows the run can close only from R ≤ 176 with L₁ in fixed residue classes
  (|L₁| ≥ 256 at R = 176). Every loop entry seen in the machine's own runs has σ ≤ 32.2 (halts only below width
  2^38.6); the latest entries any mechanism gave, a staircase run to its limit (36.45) and an extra-wall lead-in
  (39.17), allow halts only below 2^42.8 and 2^45.6. Beyond the exhaustive range (widths 2^60) a halt through the plain
  loop needs σ ≥ 53.6, about 14 more than anything found: entering the loop at least about 12.4 halvings below the
  width, which only extra-wall passes could supply (see "How late a run can enter").
- *Heuristic odds* of a halt beyond 2^55: 1 in 10^24 or less, before counting the route exclusion. From the machine's
  own exact tail (2.27 × 10⁻¹² of even n at x = 14, 54 digits), about 2^b/8.97 visited clean tapes in [2^b, 2^(b+1)), a
  halt needing x ≈ b and the average price of 2.5 digits per halving beyond 14: Σ_{b≥55} = 2 × 10⁻²⁷ (6 × 10⁻²⁶ if a
  halt needs only x ≥ b − 2). At the frontier's price of 3 to 3.3 digits per halving: 10⁻³³ to 10⁻³⁷. From random GMM
  states hit like random points (the two-marker reduction): 10⁻²⁵ to 10⁻²⁴.
- *Open:* the segments that need more digits, and a proof. The remaining statement is of Collatz type.

Three Python files, no dependencies:

| File | What it does | Run |
|---|---|---|
| `symtm.py` | Symbolic simulator: tapes may contain `(10)^n` repeats and unknown stretches `L`, `R`. Proves the three cycle lemmas. | `python3 symtm.py` |
| `proofs.py` | States and proves every rule below, plus the repeated bounces by induction. | `python3 proofs.py` → `ALL PROVED` |
| `casesim.py` | Runs the machine using only the proven rules, checking before each one that the tape really matches it. | `python3 casesim.py 1434` (about 1 s) |

## How a rule is proved

A rule says: from tape pattern *before*, the machine reaches tape pattern *after* in exactly *n* steps, for every
value of the counts (`m, j ≥ 0`) and for any tape `L` to the left and `R` to the right.

The proof runs the machine on the pattern itself, one transition at a time, straight from the table. It never looks
at `L` or `R`: the simulator stops with an error if it would. It only unrolls a repeat `(10)^n` when it already
knows that `n ≥ 1`. When the head has to cross a repeat, it uses one of three cycle lemmas:

| Lemma | Before → after | Steps | Cycle |
|---|---|---|---|
| PASS | `E>(01)^k` → `(01)^k E>` | 2k | E0 F1 |
| SHIFT | `A>(01)^k` → `(10)^k A>` | 2k | A0 B1 |
| CARRY | `(10)^k A>1 1` → `A>1 1 (10)^k` | 4k | A1 E1 B0 C0 |

Each lemma is proved by running its cycle once without reading the surrounding tape, then by induction on k. At the
end of a run, the result has to equal the stated *after* pattern exactly, step count included.

## The rules

`S>` means the head is in state S on the next cell. `0^∞` is blank tape.

Vocabulary: gap `000`, marker `11`, wall `00`, block `111`, stripes `1010…`. A packet is the `11` that the head
carries left in state A.

| Rule | Before | After | Steps |
|---|---|---|---|
| BOUNCE | `L 0 0 E>0 (10)^(m+2) 1 1 0 R` | `L 0 1 0 0 E>0 (10)^m 1 1 0 1 0 R` | 6m+30 |
| SWAP | `L 1 0 0 E>0 1 1 0 R` | `L 1 1 0 0 E>0 1 0 R` | 21 |
| MERGE | `L 1 0 0 E>0 1 0 1 1 0 R` | `L A>1 1 1 0 1 0 0 1 0 R` | 31 |
| WALLBOUNCE | `L 0 0 E>0 (10)^(m+1) 0 R` | `L 0 1 0 0 E>0 (10)^m 0 R` | 6m+12 |
| MEET→marker | `L 1 0 0 E>0 0 (10)^j 1 1 0 R` | `L (10)^j 1 0 1 0 1 0 0 E>0 R` | 2j+8 |
| MEET→wall | `L 1 0 0 E>0 0 (10)^j 0 1 R` | `L A>1 1 (10)^j 1 0 1 1 1 R` | 6j+13 |
| MEET→block | `L 1 0 0 E>0 0 (10)^j 1 1 1 0 R` | `L A>1 1 (10)^j 1 0 1 0 1 0 0 R` | 6j+19 |
| MEET→blank | `L 1 0 0 E>0 0 (10)^j 0^∞` | `L A>1 1 (10)^j 1 0 1 1 0^∞` | 6j+13 |
| GAP→blank end | `L 1 0 0 E>0 0^∞` | `L A>1 1 1 0 1 1 0^∞` | 13 |
| MEET→end marker | `L 1 0 0 E>0 0 (10)^j 1 1 0^∞` | `L A>1 1 (10)^j 1 0 1 0 1 0 1 1 0^∞` | 6j+29 |
| BLOCK→marker | `L 1 0 0 E>0 (10)^m 1 1 1 0 (10)^j 1 1 0 R` | `L 1 0 0 (01)^m 0 (01)^j 0 1 0 1 0 0 E>0 R` | 2j+2m+9 |
| BLOCK→wall | `L 1 0 0 E>0 (10)^m 1 1 1 0 (10)^j 0 1 R` | `L 1 0 0 (01)^m 1 0 0 E>0 (10)^j 1 1 1 R` | 6j+2m+17 |
| BLOCK→block | `L 1 0 0 E>0 (10)^m 1 1 1 0 (10)^j 1 1 1 0 R` | `L 1 0 0 (01)^m 1 0 0 E>0 (10)^j 1 0 1 0 0 R` | 6j+2m+23 |
| BLOCK→blank | `L 1 0 0 E>0 (10)^m 1 1 1 0 (10)^j 0^∞` | `L 1 0 0 (01)^m 1 0 0 E>0 (10)^j 1 1 0^∞` | 6j+2m+17 |
| PACKET→gap | `L 0 0 0 A>1 1 R` | `L 0 1 0 0 E>0 R` | 7 |
| PACKET→wall | `L 1 0 0 A>1 1 R` | `L 1 1 0 0 E>0 R` | 7 |
| PACKET→marker | `L 1 0 1 A>1 1 R` | `L A>1 1 1 1 0 R` | 5 |
| PACKET→left end | `0^∞ A>1 1 R` | `0^∞ 1 0 0 E>0 R` | 7 |
| PACKET→left-end marker | `0^∞ 1 A>1 1 R` | `0^∞ 1 0 0 E>0 1 0 0 R` | 18 |
| PACKET→marker after gap | `L 1 0 0 0 1 A>1 1 R` | `L A>1 1 1 0 1 0 0 R` | 15 |
| PACKET→block | `L 0 1 1 A>1 1 R` | halts (state D reads 1) | 4 |

Repeated bounces, by induction on k (the end of one bounce is the start of the next, with the count lowered):

- BOUNCE^k: `L 0 0 E>0 (10)^(m+2k) 1 1 0 R` → `L (01)^k 0 0 E>0 (10)^m 1 1 0 (10)^k R` in 6km + 6k² + 24k steps
- WALLBOUNCE^k: `L 0 0 E>0 (10)^(m+k) 0 R` → `L (01)^k 0 0 E>0 (10)^m 0 R` in 6km + 3k² + 9k steps

The packet patterns are written after CARRY. CARRY takes every `10` pair it can, including the `1 0` made by the
last cell of a marker or block and the 0 after it. So "marker" shows up as `1 0 1 A>`, and "block" as `0 1 1 A>`.

## How the rules give the round recurrence

Positions are counted from the leftmost 1. G g is a gap at cells g..g+2, M p a marker at p, p+1, W q a wall, and
B r a block at r..r+2. d = p − g − 3 is the number of stripe cells between a gap and the next marker.

| Step of the recurrence (`clean_recurrence.py`) | Rules used | Effect |
|---|---|---|
| Gap meets marker, d ≡ 0 (mod 4) | BOUNCE^(d/4), then SWAP | marker → g + d/2 − 1, gap → g + d/2 + 1 |
| Gap meets marker, d ≡ 2 (mod 4) | BOUNCE^((d−2)/4), then MERGE | wall at g + d/2 + 3; a packet goes left |
| Gap meets wall q | WALLBOUNCE^k, then one MEET rule | gap and wall vanish; a shift runs right to the next mark |
|   …the next mark is a marker p | MEET→marker | a gap opens at p |
|   …a wall q′ | MEET→wall | block at q′; a packet goes left |
|   …a block r | MEET→block | wall at r + 2; a packet goes left |
|   …blank tape | MEET→blank | new end marker, w += 2; a packet goes left |
| Gap with nothing to its right | WALLBOUNCE^k, then GAP→blank end | new end marker, w += 3; a packet goes left |
| Pass reaches a block r | BLOCK→marker, →wall, →block, →blank | wall at r − 1 while the gap sleeps, then a shift as above; a packet coming back turns that wall into M r − 2 and an active gap at r |
| Packet reaches a gap h | PACKET→gap | gap → h + 2 and wakes |
| Packet reaches a wall q | PACKET→wall | M at q − 1, active gap at q + 1 |
| Packet reaches a marker | PACKET→marker | crosses it (the marker keeps its position) |
| Packet reaches the left end | PACKET→left end, or →left-end marker | new round with a gap at 1: positions shift +2 (or +4 when a marker sits at cell 0; it becomes the wall W 5) |
| Packet reaches a block | PACKET→block | the machine halts |

PACKET→marker after gap is proved, but it never comes up in the run and the recurrence has no step for it.

## What this establishes

- **Every step of the recurrence is a theorem about the machine.** Each one is proved from the transition table, for
  all stripe lengths and any surrounding tape, with an exact step count.
- **The run is reproduced by the theorems alone.** `casesim.py` starts from the blank tape. It takes the first 17
  steps directly and then only proven rules, checking before each rule that the tape matches it exactly.
  - It reproduces the 2,994,703,671-step direct run: all 1,434 rounds and 284 clean tapes, with every mark position
    and step count exact. This takes about a second.
  - A 20-minute run reached step 16,470,069,173,330,669,103 (about 1.6 × 10¹⁹). That is 2,539,907 rounds and
    499,352 clean tapes, the last one n = 4,529,102, with a tape about 9 million cells wide.
  - It never met a configuration that no rule covers, and it never halted.
  - At every checkpoint, the clean tapes agree with `next_clean` in `clean_recurrence.py`.
- **Halting has exactly one route.** Among the rules, only PACKET→block halts. In the recurrence, blocks are always
  to the right of the active gap or packet:
  - a block appears only where a shift ends, and the packet then starts from there, going left;
  - a block disappears as soon as a pass or a shift reaches it;
  - gaps, shifts and packets only ever deal with the nearest mark.

  So the recurrence never halts.

## What is not proved

- **That the machine stays inside the recurrence forever.** The rules need marks not to touch in a few degenerate
  ways. For example, no rule covers a packet arriving at a marker that sits directly after a wall. Other contacts
  would merge two marks into a run of four, or leave a block left of the head.
- **Checked by run, not proved.** No such contact happens in the certified run, up to about 1.6 × 10¹⁹ steps.
- **A regular invariant was tried and did not close.** I searched for a language, defined by windows of 3 or 4
  neighbouring marks, that excludes these contacts and is closed under all the rules. An exact automaton check
  covered every value of the counts. Every window language I tried still let in configurations that the run never
  reaches, and some of those lead to a contact. They differ from real configurations only in distances between
  marks that are far apart, which a fixed window does not see.
- **The never-halts proof is still open.** A full proof would need to control those distances for every clean tape n.

## Residue classes of n, and the spare-digit bound

`../csearch/nrefj3.c` (Python prototype `nrefine.py`) runs the round recurrence on a whole residue class at once.

- **Classes.** For n = ρ (mod 2^k), write n = 2^k·j + ρ and leave j unknown. Every mark position is then α·j + β.
- **What is exact for every j.** A swap/merge test reads d mod 4. When α is a multiple of 4 that is β mod 4 for
  every integer j, and the halvings are exact too. Otherwise the test needs the next binary digit, and the class is
  split in two.
- **Settled classes.** A class is settled when its cycle reaches the next clean tape this way.
- **The only j-dependence.** What remains is the order of positions with different α: which mark is next to the
  right, which is the last mark, where the packet stops, and the equality checks. Each such test is a linear
  condition (α_y − α_x)·j + (β_y − β_x) ≷ 0.
- **The threshold.** The program records all of these conditions and returns j_min, the smallest j that satisfies
  them. Every integer n = ρ + 2^k·j with j ≥ j_min makes exactly the same choices as the class at every step.
  It therefore has the same next clean tape, rounds and right-end chain, and in particular it does not halt.

**Spare-digit bound (checked for every class that settles within 44 digits):** j_min is 0 or 1. So an integer
follows its class as soon as it has a 1-bit above the digits the class reads. j_min = 1 only where the integer ρ
itself differs; mostly these are n + 2 = 2^v exactly.

**Covering every n below 2^45.** Take n with b binary digits.
- If its class settles at some depth k ≤ b − 1, then n ≥ 2^k, so j ≥ 1 ≥ j_min, and the bound applies.
- Otherwise its class is still open at depth b − 1. That class contains exactly one integer with b digits,
  ρ + 2^(b−1), and the program runs it directly.

So the refinement plus the direct runs decides every n < 2^45.

Checks:
- For all n < 2^20, the covering agrees with brute force on next clean tape, rounds and chain.
- For every class up to 22 digits, the integers with j = j_min, j_min + 1 and j_min + 2 match, and j = j_min − 1
  really differs whenever j_min = 1.
- The direct-run engine equals the integer C model on 100,000 consecutive n from 2^40.

**Result to 44 digits** (`nrefj3 44`, log `../nrefj3_44.log`):
- 44,769,064 settled classes. Every one has j_min ≤ 1, and only 56 have j_min = 1.
- 143,413,790 direct runs, all of which reach the next clean tape. No class and no direct run halts.
- So, within the mark model, **every clean tape n < 2^45 ≈ 3.5 × 10^13 reaches the next clean tape without
  halting.**
- Also, every n ≥ 2^44 whose residue mod 2^44 lies in a settled class has exactly that class's cycle. That covers all
  but 2.8 × 10^-6 of residues, and those n do not halt either.
- The longest right-end chain anywhere below 2^45 is 14 meetings, for example n = 363,165,946,702.

**Result to 48 digits** (`../csearch/nrefdisk2.c`, chunked and resumable; log `../nd_run.log`): 242,983,886
settled classes and 765,398,154 direct runs, none halting; every class has j_min ≤ 1; no jump exceeds 297; the longest
chain is still 14. So within the mark model **every clean tape n < 2^49 ≈ 5.6 × 10^14 reaches the next clean tape
without halting.** Levels 45 to 48 add no new small contact minimum.

**Result to 49 digits** (October 20, `../csearch/nrefdisk3.c`, the same program with a streaming merge; log
`../nd_run.log`, closest approaches `../global_after49.txt`): level 49 adds 125,855,520 settled classes and 396,558,750
direct runs, none halting, no problem class, every class with j_min ≤ 1, no jump above 297, longest chain still 14
(e.g. n = 583,794,162,897,742), and none of the 39 closest-approach minima changes. In all, 368,839,406 settled
classes and 1,161,956,904 direct runs: within the mark model **every clean tape n < 2^50 ≈ 1.1 × 10^15 reaches the
next clean tape without halting**, and every n of any size whose residue mod 2^49 is settled (all but 7.0 × 10⁻⁷ of
residues) has its class's cycle and does not halt. The machine therefore needs at least
(1.5/297)·∫(x − 298)² dx ≈ **2.4 × 10^42 steps** to reach a clean tape ≥ 2^50 (about 2.4 × 10^44 at the central pace).

**Result to 50 digits** (October 20, `../csearch/nrefdisk4.c`, the same program storing only parents from level 51
on; log `../nd_run.log`, closest approaches `../global_after50.txt`): level 50 adds 191,261,915 settled classes and
601,855,585 direct runs, none halting, no problem class, every class with j_min ≤ 1, no jump above 297, longest chain
still 14 (e.g. n = 1,146,744,116,319,054). None of the closest-approach minima changes; the only new line is the first
appearance of a shift between two blocks, at a separation of about 2^50.8. In all, 560,101,321 settled classes and
1,763,812,489 direct runs: within the mark model **every clean tape n < 2^51 ≈ 2.3 × 10^15 reaches the next clean tape
without halting**, and every n whose residue mod 2^50 is settled has its class's cycle. The machine therefore needs
at least (1.5/297)·∫(x − 298)² dx ≈ **1.9 × 10^43 steps** to reach a clean tape ≥ 2^51 (about 2.0 × 10^45 at the
central pace). Level 51 was half done when the depth-first engine below overtook it; see "Result to 54 digits".

**Result to 54 digits** (October 20, night; `../csearch/nrefdfs2.c` in 48 parts, `../dfs/K54/`, merged
`../dfs/merged54.txt`). Levels 1 to 50 equal nrefdisk's lines exactly (the only differences are which of several n
with the same longest direct chain is named first, at levels 34, 35, 39 and 40). Levels 51 to 54 add 290,827,579,
439,644,681, 660,672,729 and 993,443,454 settled classes and 912,883,591, 1,386,122,501, 2,111,572,273 and
3,229,701,092 direct runs; in all 2,944,689,764 settled classes and 9,404,091,946 direct runs, none halting, no problem
class, every class with j_min ≤ 1. The longest chain in a settled class is still 14, but two direct runs have 16:
n = 3,617,714,363,521,582 (level 51, 16.45 halvings) and n = 30,335,806,016,335,582 (level 54, 16.57, the one the
lucky-line search had predicted); both are confirmed by the certified macro simulation. The largest jump is now 303
(n = 23,360,241,842,174,558, a cycle of 26 segments and 170 rounds). Among the closest approaches the only new line is
a shift between two blocks at a separation of about 2^52.2; none of the small minima changes. So within the mark model
**every clean tape n < 2^55 ≈ 3.6 × 10^16 reaches the next clean tape without halting**, and the machine needs at least
0.5·(2^55)³/303 ≈ **7.7 × 10^46 steps** to reach a clean tape ≥ 2^55 (about 8.3 × 10^48 at the central pace). The
settled classes also give the machine's tail at 54 digits (all n, as n → ∞ in each class; doubled for even n):
8.62 × 10⁻⁵, 9.40 × 10⁻⁸, 9.47 × 10⁻⁹, 4.95 × 10⁻¹⁰, 3.80 × 10⁻¹², 2.27 × 10⁻¹² for x = 4, 8, 10, 12, 13, 14, within
1% of the 48-digit tree to x = 12 and 4% at 13 and 14, with no settled class reaching 15 (open measure 1.8 × 10⁻⁷).

**Result to 56 digits** (October 21; the same engine in 96 parts at split level 28, `../dfs/K56/`, merged
`../dfs/merged56.txt`, 11.6 CPU hours). Levels 1 to 54 equal the 54-digit run's lines exactly (only which of several
n with the same longest direct chain is named first differs, at level 35). Levels 55 and 56 add 1,505,505,413 and
2,303,238,431 settled classes and 4,953,896,771 and 7,604,555,111 direct runs; in all 6,753,433,608 settled classes and
21,962,543,828 direct runs, none halting, no problem class, every class with j_min ≤ 1. The longest chain in a settled
class is now 16 (first at level 56); the longest direct run is 19, at n = 114,928,805,503,523,374 (level 56, 19.70
halvings), the tape the lucky-line search had already found and certified. The largest jump is 312
(n = 127,047,863,822,740,014). The only new closest-approach line is again a shift between two blocks (about 2^50.8).
So within the mark model **every clean tape n < 2^57 ≈ 1.4 × 10^17 reaches the next clean tape without halting**,
and the machine needs at least 0.5·(2^57)³/312 ≈ **4.8 × 10^48 steps** to reach a clean tape ≥ 2^57 (about 5.3 × 10^50
at the central pace).

**Result to 58 digits** (October 22; the same engine in 192 parts at split level 30, `../dfs/K58/`, merged
`../dfs/merged58.txt`, about 31 CPU hours over three container restarts, finished parts kept). Levels 1 to 56 equal
the 56-digit run's lines exactly (`merge.py --cmp`: no mismatch). Levels 57 and 58 add 3,541,898,803 and
5,446,272,330 settled classes and 11,667,211,419 and 17,888,150,508 direct runs; in all 15,741,604,741 settled
classes and 51,517,905,755 direct runs, none halting, no problem class, every class with j_min ≤ 1. The longest chain
in a settled class is still 16. The longest direct runs at levels 57 and 58 are again 19 meetings
(n = 222,537,095,569,168,942 and 381,348,839,312,808,494, at 19.45 and 19.46 halvings), so n = 114,928,805,503,523,374
(19.70) stays the closest approach found below 2^59. The largest jump is 327 (n = 534,260,472,410,180,530, 23 segments
and 178 rounds, closest end meeting 4.35 halvings). The closest-approach minima are identical to the 56-digit run's:
no new line at all. So within the mark model **every clean tape n < 2^59 ≈ 5.8 × 10^17 reaches the next clean tape
without halting**, and the machine needs at least 0.5·(2^59)³/327 ≈ **2.9 × 10^50 steps** to reach a clean tape
≥ 2^59 (about 3.4 × 10^52 at the central pace). Widths below 2^60 are covered, so by the sharp lock a halt beyond needs
σ ≥ 53.6 at the plain loop's first pass start.

**Result to 60 digits** (October 26; the same engine in 384 parts at split level 31, `../dfs/K60/`, merged
`../dfs/merged60.txt`, over several container restarts, finished parts kept). Levels 1 to 58 equal the 58-digit run's
lines (`merge.py --cmp`: no mismatch; at level 57 the first n with the longest direct chain is reported differently,
195,642,498,725,403,182 instead of 222,537,095,569,168,942, both 19 meetings, because the parts are traversed in a
different order). Levels 59 and 60 add 8,359,095,400 and 12,829,211,648 settled classes and 27,417,205,616 and
42,005,199,584 direct runs; in all 36,929,911,789 settled classes and 120,940,310,955 direct runs, none halting, no
problem class, every class with j_min ≤ 1. The longest chain in a settled class grows to 17 (at level 60). The longest
direct runs at levels 59 and 60 are again 19 meetings (n = 635,064,930,931,792,430 and 1,304,830,048,624,138,798). The
largest jump is 345 (n = 1,222,608,482,984,076,798). The closest-approach minima are identical to the 58-digit run's.
So within the mark model **every clean tape n < 2^61 ≈ 2.3 × 10^18 reaches the next clean tape without halting**, and
the machine needs at least 0.5·(2^61)³/345 ≈ **1.8 × 10^52 steps** to reach a clean tape ≥ 2^61. Widths below 2^62 are
covered, so by the sharp lock a halt beyond needs σ ≥ 55.6 at the plain loop's first pass start. (The audit of the
trailing-wall slip covered this engine to 46 digits; the whole run was later repeated with the fixed engine, with the
same output: see "The trailing wall, fixed".)

**The mark model against the real machine, at these sizes** (October 20, night). The certified macro simulation
(`cycles.py`: the proven rules applied to the real tape, with every rule's preconditions checked) runs a whole cycle
in about 2 ms even at 90 binary digits. For 21,300 random clean tapes, 300 for each binary length from 20 to 90, and
600 more in [2^53, 2^55), it reaches the same next clean tape in the same number of rounds as the mark model
(`../csearch/lined.c`, point mode, 128-bit positions), with no exception; so does every record tape listed under "How
close anything comes to halting".

**A depth-first engine, an independent driver** (October 20, night; `../csearch/nrefdfs.c`, `nrefdfs2.c`,
`../dfs/run_parts.sh`, `../dfs/merge.py`). Same mark model and the same tests as nrefdisk; only the driver differs.
- *Refining in place.* nrefdisk re-runs every open class from the clean tape at each level. The depth-first engine
  keeps, for each class, its state at the start of the round where a test first needs another digit and refines that
  state: with j = 2j' + δ, a position a·j + b becomes 2a·j' + (aδ + b). The comparison thresholds are kept on n rather
  than on j, so they carry over unchanged and j_min stays exact.
- *Direct runs.* The direct run of n = ρ + 2^k (the one member of an open class with k + 1 digits) starts from the
  class's state at the start of the split round, evaluated at j = 1, whenever every earlier comparison holds there
  (otherwise from the clean tape). Identical results with and without this shortcut.
- *Sorted marks* (`nrefdfs2.c`). The marks sit in a sorted linked list, so "next to the right", "last" and "nearest
  non-marker to the left" are neighbours rather than scans. An order comparison, with its threshold, is made for every
  pair that becomes adjacent or moves, which is all the list's order needs; nrefdisk's scans also compare non-adjacent
  pairs, whose thresholds those imply, so j_min can only be smaller (in practice it is identical). Separations are
  probed only for pairs that changed since the last probe of the same phase; a refined child inherits its parent's
  probe state, whose values were taken at a smaller n and so bound its own from below. The minima are the same as
  probing every pair at every step.
- *Checks.* Run alone, both versions reproduce nrefdisk's per-level line exactly (settled, open, longest chain, largest
  j_min, direct runs and the n of their longest chain) at every level compared, and their outputs are identical to
  each other, closest approaches included. Speed: 38 levels in 18 s (nrefdisk needed hours per level beyond 45);
  about 6 times the throughput overall. The run is split by the class's residue at level 26 into 48 parts.
- *What did not help* (`nrefdfs3.c`). Direct runs are about two thirds of the time. A variant lets each class carry
  its smallest member (the n of its parent's direct run) and settle it with the class whenever every comparison holds
  there, probing separations on a second track at that n. It gives identical results (to 34 levels, closest
  approaches included), but it saves only a third of the direct runs: of the 384,089 integers a 30-level run covers
  individually, 125,658 settle with their class and 43 diverge, while the 129,196 classes still open at the last level
  need both their smallest members run directly (258,388 runs), and the last level dominates. With the second probe
  track it is no faster.

**Why the open classes grow 1.53-fold per digit** (`../csearch/settle.c`, 200,000 random 48-bit n). The depth at which
n's class settles is set by how many times its cycle returns to a GMM state, not by how close it comes to the end:
mean settle depth 1.0, 2.4, 5.0, 8.5, 12.1, 15.4, 19.1, 22.3, 26.3, 30.4 for 0 to 9 returns, about 3.5 binary digits per
return. Each return happens with odds about 0.35, and 0.35^(1/3.5) ≈ 0.74 is close to the measured 0.766 share of
classes still open per digit. In two thirds of the classes the last undecided test is not a meeting with the end
marker. So almost all the work of the exhaustive check goes into cycles that keep restarting, not into cycles that
come close to halting.

**Contacts.** The same probes as the trajectory follower record the closest approach of neighbouring marks, for each
pair of mark types and each phase. For a class this is evaluated at j = 1, its smallest member: the order is the same
for every j ≥ 1 and separations only grow with j. Every cycle that sets one of these minima is certified with
`cycles.py`, which uses only the proven rules and checks the tape exactly. There are 14 such cycles: n = 2, 4, 6, 14,
30, 46, 174, 466, 2514, 10706, 13822, 41998, 327854 and 1242238. Levels 35 to 44 add no new small minimum; the only
new entries are wall–gap separations of about 6.6 × 10^10. The only separations of 0 are a gap against a marker, the
ordinary swap, and they occur inside certified cycles.
*Checked against what the rules do not cover* (October 21). The stepper's checks, tested against the bare transition
table on 40,000 tapes with marks packed close together (no round that passed them disagreed with the real machine),
say a step leaves the proven rules only when: a packet crosses a marker with a wall or gap directly on its left; a
gap has a wall or gap directly on its left; two marks of the same kind of cells (0-runs G, W or 1-runs M, B) touch;
marks overlap; or the gap meets the end marker within 2 cells. In the 56-digit run's minima (every class below 2^57,
`../dfs/merged56.txt`, separations counted in stripe cells between neighbours) the relevant ones are: packet phase W–M
10 and G–M 22; gap phase W–G 39; same-kind neighbours G–W 1, W–W 19, M–M 3, M–B 1,493, B–M 37, B–B 515,329; nothing
negative; and no class problem, which is how a gap or shift running into a gap, or an odd distance, would show up. The zero separations (G–M in the gap phase, the swap; M–G in the shift and packet phases, the marker and gap
that PACKET→wall leaves side by side) are ordinary configurations of the rules. So below 2^57 none of the uncovered
configurations occurs, read straight off the minima; the comparison with certified cycles is a second check. The
58-digit run's minima (every class below 2^59, `../dfs/merged58.txt`) are identical, line for line.

**Not proved:** that j_min ≤ 1 holds at every depth, and anything about the classes still open at 44 digits.

**Towards every depth.** Write each position as λ·(2n + 6) + c.
- All j-coefficients are even, so two marks at different λ differ by at least 2 per unit of j.
- The low-digit part always pushes a comparison the way the class expects.
- So j_min ≤ ⌊D/2⌋ + 1, where D is the largest c_x − c_y over compared pairs with λ_x < λ_y. This holds at every
  depth.
- In every class up to 34 digits, D = 3, and pairs with a coefficient gap of 2 have c_x − c_y ≤ −2. Together these
  give j_min ≤ 1.
- Proving D ≤ 3 in general would give j_min ≤ 2 at every depth. It needs an invariant that survives every rule:
  measured near the gap, marks already passed sit at least 1.39 below it in c, and marks ahead of it at most 3 below.

**Where the thin margins are** (`../csearch/nrefthin*.c`). A member with j ≥ 1 can only leave its class at a
comparison between neighbouring marks whose j-coefficients differ. Rules move marks by only a few cells, so that needs
two such marks to come within a few cells of each other in the smallest member. Measured at j = 1, these margins have
only two sources:
- **Left end.** A new gap at cell 1 against the last left halving marker, or the wall it merges into, at 2m or m + 4
  where m is the odd part left after halving. For j ≥ 1 these sit at cells ≥ 4, so the margin is 0 to 3 cells but
  never negative. For j = 0 with m = 1 (n + 2 a power of 2) the marker lands inside the gap, which is where every
  j_min = 1 class comes from.
- **Everywhere else.** The smallest coefficient gap between differently scaling neighbours is about 2^(k+1−L)/2.6,
  and never below about 2^(k+1−L)/32, where L is the class's number of right-end meetings. The minimum separation
  grows from 374 cells at depth 12 to 817,635 at depth 30.

So the right-end margin is set by how far the cascade has halved the right end, and the spare-digit bound could only
fail in a class whose smallest member's cascade comes within a few hundred cells of the end. That is also the only
way a contact or a halt can arise. **All three questions (spare digits at every depth, contacts, halting) reduce to
one: does any clean tape's right-end cascade come within a few hundred cells of the end?** Below 2^45 the closest is
about 30 halvings short.

## In machine steps

- **Per cycle.** Every cycle from clean tape n starts with the gap meeting the end marker at distance 2n. That takes
  BOUNCE^k with k = ⌊n/2⌋, which is at least 6k² ≥ 1.5(n − 1)² steps. In 633 certified cycles, from n = 2 to about
  10^14, the smallest ratio of steps to (n − 1)² was 2.25.
- **Largest jump.** No n < 2^45 jumps by more than 252 (`../csearch/nrefjmax.c`; the largest is at
  n = 4,310,782,069,630).
- **The bound.** So the clean tapes below 2^45 are at most 252 apart, and the machine needs at least
  (1.5/252)·∫(x − 253)² dx ≈ **8.6 × 10^37 steps** to reach its first clean tape ≥ 2^45. Combined with the result
  above, it does not halt within its first 8.6 × 10^37 steps. This relies on the mark model and the contact standard.
- **To 2^49.** No n < 2^49 jumps by more than 297, which gives at least 3.0 × 10^41 steps before the first clean
  tape ≥ 2^49 (about 3 × 10^43 at the central pace).
- **Central estimate.** 300 certified trajectory cycles from n = 10^12 + 1 average 4.77·n² steps and a jump of 8.97.
  That gives steps ≈ 0.1772·N³, matching the 0.177 of the certified run to n = 4.5 × 10^6. So it takes about
  7.7 × 10^39 steps to reach 2^45.

## How close anything comes to halting (`../csearch/nrefmd.c`)

For every n < 2^45, the smallest right-end meeting distance in its cycle, as halvings log2(width / distance):

| Digits | Best halvings | Needed to halt | Example |
|---|---|---|---|
| 17 | 10.3 | 16.2 | 73,742 |
| 30 | 12.4 | 29.1 | 575,152,510 |
| 39 | 14.0 | 38.5 | 391,305,139,022 |
| 45 | 14.7 | 44.8 | 29,640,302,498,638 |

No class has a closest distance that stays fixed as n grows.

**Beyond the exhaustive range, by following lucky lines** (October 20, night; `../csearch/lined.c`,
`../lines/frontier.py`, `../lines/reach28_c46.txt`). Every GMM state that a class of even n reaches within 28 digits is
a line of GMM states in the class parameter (64,665 lines). `lined` runs one segment over a line exactly (positions in
128-bit integers, the class split on each undecided digit, as in the depth-first check), to 46 more digits. The share of
lines whose segment comes within 2^-x is 0.149, 0.068, 0.030, 0.017, 0.0066, 0.0028, 0.0016, 0.0009, 0.0004, 0.0002 for
x = 10 to 19 (about one digit per halving, the same at every line depth from 16 to 28). For the 1,072 lines that reach
13 (and, from `../lines/reach30_c46.txt`, the 76,132 lines at depth 29 to 30, whose shares are the same: 0.152,
0.066, 0.032, 0.016, 0.0064 for x = 10 to 14), the shallowest class above each threshold (to 56 digits) gives explicit
integers, each run directly in the mark model and through the certified macro simulation of the real machine
(`cycles.py`: same next clean tape and rounds in every case; the 68-digit cycle takes 4.6 × 10⁴² steps):

| Digits | Best halvings found | Needed to halt | Chain | n |
|---|---|---|---|---|
| 52 | 16.45 | 51.7 | 16 | 3,617,714,363,521,582 (found by the exhaustive run, not by the lines) |
| 55 | 16.57 | 54.8 | 16 | 30,335,806,016,335,582 |
| 57 | 19.70 | 56.7 | 19 | 114,928,805,503,523,374 |
| 57 | 18.51 | 56.5 | 18 | 104,886,771,549,952,558 |
| 59 | 17.59 | 58.4 | 17 | 372,795,940,376,369,710 |
| 60 | 19.58 | 59.1 | 19 | 635,064,930,931,792,430 |
| 60 | 17.62 | 59.4 | 17 | 765,139,844,716,780,078 |
| 68 | 20.78 | 67.8 | 21 | 253,591,897,524,813,984,894 |
| 73 | 21.19 | 72.6 | 21 | 7,315,920,139,807,735,884,722 |
| 75 | 22.08 | 74.4 | 22 | 24,749,695,764,955,168,991,358 |
| 77 | 23.12 | 76.9 | 23 | 144,810,797,413,517,776,873,598 |
| 78 | 21.62 | 78.0 | 21 | 300,419,646,203,500,033,433,102 |
| 79 | 21.13 | 79.0 | 19 | 588,157,873,818,542,041,299,794 |
| 81 | 23.10 | 80.5 | 22 | 1,735,210,305,894,448,940,015,326 |
| 84 | 24.10 | 83.2 | 23 | 11,406,616,862,811,482,337,664,734 |
| 85 | 25.42 | 84.5 | 23 | 28,185,530,691,921,718,117,285,598 |
| 94 | 29.55 | 93.6 | 28 | 14,690,414,442,211,083,106,227,634,386 |
| 97 | 27.55 | 96.8 | 26 | 133,532,658,213,607,589,496,543,559,890 |
| 88 | 25.54 | 87.3 | 24 | 186,380,578,653,460,961,569,063,122 |

These are lower bounds for the best at each length (only lines to depth 28 were searched), but they track the
exhaustive records: the closest approach stays near 0.3 of the binary length (0.33 at 45 digits, 0.30 at 55, 0.33 at
60, 0.31 at 68, 0.29 at 81), so a cycle gets about a third of the way to a halt. The 55-digit one is below 2^55 and is
the first chain longer than 14: it is the smallest member of its class mod 2^55, so the exhaustive check meets it as a
direct run at level 54, and it does (the depth-first run's part 29: "direct runs ... longest chain 16 at
n = 30335806016335582", found independently of the line search). The guess above that 15 meetings need a class
deeper than 50 digits holds. Every one of these runs (`../lines/anatomy.py`, the longest chain of end
meetings, each at pred of the last) starts within 2.1 halvings of the full width and is one lead-in meeting, one
stretch of the plain loop and an exit of at most 3: loop meetings 10, 12, 15, 15, 17, 19, 21, 21 of 14, 16, 17, 19,
21, 21, 22, 23 for the records at 39, 55, 59, 60, 68, 73, 81 and 84 digits. So the record runs are exactly the
pattern the route exclusion addresses, and their length is set by the line-up, not by the lock, which at 84 digits
would allow about 60 loop meetings (15 passes). And every one of them enters the loop through a prefix of the 46-bit route tree
(`../lines/reccover.py`: from the GMM state that starts the segment holding the record run, m/E between 0.0015 and
0.99, the shapes and outcomes to its first G W W W are one of the 759,918 listed prefixes, entry measure 6 × 10⁻⁵ down
to 3 × 10⁻⁸), so these are runs that the route exclusion already rules out at every width. Which countdown ends them (`../csearch/lined.c`, PASSES mode, R = E − c − 1 and
L₁ = 147b + 280E − 392c − 578 at each pass start): in all nine records from 39 to 84 digits the trailing zeros fall by
exactly 4 and 6 per pass (e.g. 12, 8, 4 and 21, 15, 9 for the 57-digit one; 20, 16, 12, 8, 4 and 31, 25, 19, 13, 7 for
the 84-digit one), L₁ stays ≡ 3 (mod 7), and the run leaves when R is down to 3 or 4 zeros. In seven of the nine L₁
still has enough zeros for another pass, and in the other two both run out together; |L₁| never exceeds 2^6.2·E, so
the lock (280E) is never what stops them. The records are limited by the end countdown's line-up. Why about a third: a line of depth d is the luckiest of about 1.53^d lines, so its
best route lines up about 0.61d digits, one loop meeting per digit; its own points then pay 1.5 digits per loop
meeting. An n with b digits on a line of depth d can therefore have about min(0.61d, (b − d)/1.5) loop meetings, at
most about 0.32b (at d ≈ 0.52b), and the records, searched only on lines of depth ≤ 30, have 0.22b to 0.26b. A halt
needs about b meetings in one run, three times the luckiest line's share. Ranking by the smallest member instead (`../lines/records.py`: on each
of the 2,267 lines with reach ≥ 13, the smallest member of the classes reaching each threshold; 13,136 candidates, each
run directly and the new ones through `cycles.py`), the smallest known clean tape coming within 2^-x has 33 binary
digits for x ≤ 13 (n = 6,151,594,450, 13.09 halvings), 39 for 14, 52 for 15 and 16 (the exhaustive check's
3,617,714,363,521,582, found again this way), 57 for 17 to 19 (n = 114,928,805,503,523,374, 19.70 halvings), 68 for
20, 73 for 21, 81 for 22 and 23, 84 for 24: x stays between 0.29 and 0.36 of the binary length. **Deeper lines,
screened by their line-up** (`../lines/records2.py`, `../lines/kappa34_c30.txt`): the line-up prediction (below,
under "A line's reach is predicted by its line-up") run on all 628,853 lines at depths 31 to 34 (12 minutes) gives the
same shares as before, about one digit per halving (15% predicted to reach 12, 0.27% 18, 0.016% 22, 0.003% 24, the best
26.9). The 478 lines predicted to reach 20 or more, run in full to 56 digits (true reach up to 25.54; 38 reach 20 and
11 reach 22), give 5,566 candidates and new records, all certified: 22.08 halvings at 75 digits, 23.12 at 77 and
25.54 at 88 (rows above). Each is again one lead-in meeting, 20 loop meetings and 1 to 3 exit meetings, entering the
loop through a listed prefix. The same screen on all 1,024,956 lines at depths 35 and 36 (shares 16% predicted to
reach 12, 0.26% 18, 0.011% 22, 0.003% 24; best 30.6) picks 611 lines; run in full to 56 digits their true reach is at
most 25.54 again (48 reach 20, 9 reach 22; the predictions of 26 to 30.6 need members beyond the 56-digit cut), and
6,750 candidates give one new frontier point: 25.42 halvings at 85 digits (row above; certified; a 23-meeting run
from 3.4 halvings with 20 loop meetings and 3 exit meetings), the highest ratio found beyond 60 digits (0.301). The
smallest known tape for each x is now 33 digits for x ≤ 13, 39 for 14, 52 for 15 and 16, 57 for 17 to 19, 68 for 20,
73 for 21, 75 for 22, 77 for 23, 84 for 24 and 85 for 25: from x = 16 to 25 about 3.7 binary digits per halving, and
x settles near 0.29 to 0.30 of the binary length. The 15 lines predicted to reach 26 or more (best 30.6) need
members beyond the 56-digit cut; run to 72 digits (`../lines/records3.py`, 30 seconds) they give 398 candidates and
the record so far: **29.55 halvings at 94 digits** (n = 14,690,414,442,211,083,106,227,634,386, certified; a 28-meeting
run from 2.55 halvings: one lead-in meeting, 26 loop meetings, one exit meeting), from the line predicted to reach
30.55. So the smallest known tape for x = 26 to 29 has 94 digits, and the deepest lines deliver within about a
halving of their line-up prediction once the cut lets their members in (the 30.55 line's member needs 58 digits of
the line parameter: 22 for the route into the loop and 1.5 per loop meeting). Ranking by class depth
misses records whose smallest member happens to have leading zeros, as the 52-digit one does (its class has 62
digits). Along the frontier both rankings give about 3 to 4 binary digits per halving, against 2.5 in the average
tail.

## The two-marker reduction (October 20; `../csearch/gmmseg.c`, `checkflags.py`)

Every halt from a clean tape happens inside one **segment**: the rounds from a GMM state (gap at 1, marker at m, end
marker at E − 2, nothing else on the tape) to the next GMM state or the clean tape. Even n reach their first GMM state,
(n + 2, 2n + 11), after one round (the first meeting, at distance 2n, is a swap to the middle); odd n reach the clean
tape n + 3 in two fixed rounds. A segment depends only on (m, E). So from any clean tape the machine can halt only by
reaching a GMM state whose own segment halts; call that set H. This is a statement about a fixed two-number family,
independent of which states the machine visits.
- **Real machine, every GMM state up to width 1201** (all even m from 4 to E − 7: the 176,715 of `gmmreal`, plus the
  edge cases m = 4 and m = E − 7 that the earlier scans left out): exactly one halts, (m, E) = (4, 13), at step 567.
  Its end meetings run 6, 2, 0 and the last is a swap that fuses the end marker into a block, the same ending as the
  hand-built tapes; the marker touches the gap. The machine's narrowest GMM state is (4, 15), for n = 2, so it never
  reaches (4, 13).
- **Mark model with contact detection, segment only, every GMM state up to width 262,143** (8,589,344,778 states, 34
  CPU minutes): only 7 states, all of width 11 to 29, come within 2 cells of the end or let marks touch, and on the real
  machine only (4, 13) of them halts. Closest approach per width range, in halvings: 9.9, 8.5, 9.2, 11.2, 12.0, 13.3,
  13.9 for 2^11–2^12 up to 2^17–2^18, against 11 to 16.7 needed. A segment ends in another GMM state in 34.38% of
  states.
- So H ∩ {E ≤ 262,143} = {(4, 13)}. With the per-state odds measured on random GMM states (2.46 binary digits per
  halving), the expected number of halting GMM states of width about 2^k is 2^(0.24 − 0.46k): about one below 2^16,
  which is what was found, and about 0.014 beyond 2^18. The universal statement "H = {(4, 13)}" would imply that the
  machine never halts from any clean tape; it is checked to width 2^18 and heuristically holds with odds of about 99%.
- A halt of the machine itself also needs its own sequence to land on a state of H. It visits about one GMM state per
  cycle while the width grows about 18 per cycle, so if a state of width about 2^k were hit like a random point, with
  odds of about 2^-(k+2), the expected number of halts beyond 2^50 would be about Σ 2^(0.24 − 0.46k)·2^-(k+2) ≈ 10^-23
  to 10^-22. The top-running fit above gives 10^-17; it extrapolates a heavier tail (1.8 digits per halving, which the
  exact tail of the machine's own family confirms from 8 to 12 halvings), measured
  on integers selected for long activity, and would mean the machine's own states hit H 2^(0.35k) times more often
  than random points, against the evidence that its early segments are tamer than random.
  Both figures predate the route exclusion below, which removes, at every width, the routes into 99.7% of the runs
  that come within 2^-8 (and all 30 sampled runs within 2^-11). If the remaining routes carry a similar share of the
  odds at halting depth, both drop by another factor of about 300; rarer routes cost more digits, so their share
  probably shrinks with depth rather than grows.
- **The main route never halts, at any width** (`../mainroute_cands.py`, `../csearch/candseg.c`). Every main-route
  entry (G M M → G M M M → G M M W → G M W W → G W W W) starts at a GMM state, i.e. at a segment start, so the plane
  covers every stage of every cycle. With the route's countdowns R = (3E − m + 13)/8 and L = (5978E − 2401m − 7210)/16
  in the GMM state's (m, E), a halt at width E ∈ [2^k, 2^(k+1)) needs p ≥ (k − 12)/4 plain passes (at most 3 route
  meetings, 4 per pass, at most 8 exit meetings, proved), hence R ≡ 0 (mod 16^p) and L ≡ 0 (mod 64^p). Eliminating m,
  E ≡ −38423/1225 (mod 2^(4p+3)) and then m is fixed mod 2^(6p+4). For k = 18 to 56 that leaves 21,581 candidate
  states (none at all for k ≥ 45, where the residue of m is larger than E); run through their segments, none comes
  within 2 cells of the end or lets marks touch. Beyond 2^55 the lock alone forbids it (p ≤ log₆₄(280E)). With the
  full scan below 2^18: within the mark model, no GMM state of any width halts through the main route, the route
  taken by 230 of the 256 longest cascades below 2^49. The candidates show how far a tuned state gets: one of width
  2^44.5 (m = 23,756,126,766,192, E = 25,362,002,766,881) runs the loop for 8 passes and comes within 2^-33 of the
  width before the left countdown runs out, against the machine's own record of 2^-14.7.
  (Redone with a safe pass requirement, see the correction below: 332,846 candidates for k = 17 to 61, none halting;
  the best gets to 1,030 cells from the end at width 2^46.0, m = 35,561,341,614,704, E = 72,383,467,752,225, 36.0
  halvings, 8 passes.)
- **Twelve routes, 95% of long segments, never halt** (`../conc/routeexclude.py`, `../run_routes.sh`,
  `../routes_excl.log`). The same argument works for any route r into the plain loop (the shapes and outcomes from
  the GMM state to the G W W W where a pass starts; a route that reaches the loop mid-pass is completed by the pass's
  last two rounds). With H_r the most halvings the route itself can make (from the affine form of the end distance
  over 0 < m/E < 1), a halt at width 2^k needs p ≥ (k − 9 − H_r)/4 passes; the forced congruences of route + p passes
  form a 2-D coset in (m, E), and every lattice point of it in the width range is run through its segment. Beyond
  k = 3H_r + 45 the lock forbids it. Among 200 million random GMM segments at width 2^40, the 12 commonest routes into
  the loop carry 468 of the 493 that come within 2^-8 of the width (95%). For each, k = 17 to 62 (66 for the route
  with H_r = 6.1) leaves 0 to 1,353 candidates, 2,565 in all; none comes within 2 cells of the end or lets marks touch.
  Best approaches: 30.6 halvings at 2^39.8 (main route), 29.2 at 2^37.9 (G M W, G W W, G B, G M M M M, G M M M M M,
  G M M W M M, G M M W, G M W W, G W W W), 22.3 at 2^29.1. So within the mark model no GMM state of any width halts
  through one plain stretch entered by any of these routes. Not covered: the rarer routes (5% of long segments) and
  runs that chain an extra-wall stretch into the loop.
  **Correction (October 20, evening).** The pass requirement used above and in the main-route paragraph was a
  quarter pass too strict. With x = d + 2, a meeting maps x to x/2 (d ≡ 2 mod 4) or x/2 + 5, so x at most halves; a
  halt needs x ≤ 4; the loop divides R = E − c − 1 exactly by 16 per pass; and at most 8 meetings follow the loop. So a
  halt at width 2^k needs only 4p ≥ k − H_r − 10, not k − H_r − 9 (for the main route, p ≥ (k − 13)/4, not
  (k − 12)/4), and some widths were searched with one pass too many. Everything is redone below with two more halvings
  of margin, 4p ≥ k − H_r − 12, and the matching lock cap k ≤ 3H_r + 54.3 (from 64^p ≤ |L₁| < 280E), for all 2,767
  prefixes found within 30 bits; they include the main route and the twelve routes. The earlier 26-bit run had also
  stopped at k = 70 for 11 prefixes whose cap was up to 77; those were completed (0 candidates) before the redo.
  **All routes to 30 bits** (`../conc/routetree.py`, `routeexclude2.py` with slack 12, `../rt30s_summary.txt`,
  `../rt30s_check.txt`): following every branch of a free GMM segment exactly (at m/E = 1/2), 617 distinct prefixes
  end at a G W W W within 26 binary digits and 2,767 within 30 (2-adic measure 8.76 × 10⁻³ of all GMM states;
  undecided at the cut 1.7 × 10⁻⁴ and 4.4 × 10⁻⁵). By entry measure the main route is 89% of them, but long runs weigh
  differently. **Coverage, measured exactly** (`../csearch/runentry.c`, `../conc/covercheck.py`): of 1,020 random
  segments at width 2^40 (all ratios m/E) that come within 2^-8 of the width, the shapes and outcomes from the GMM
  state to the loop entry of their *deepest* run match one of the 26-bit prefixes for 1,009 (98.9%) and one of the
  30-bit prefixes for 1,017 (99.7%); deeper runs are no different: of 4 × 10⁹ random segments, the 30 that come
  within 2^-11 all enter their deepest run through one of the 30-bit prefixes. (The earlier figure of 99.4% counted the first loop entry; in 48 of the 1,020 the
  deepest run is a later one in the segment. One never enters the plain loop: from the extra-wall state its walls are
  used up one per round, G W M W W, G B, G W W, G B, G W M M, G W, G M, with a meeting in nearly every round, 8.9
  halvings in all.) Each prefix was run in both loop phases, k from 17 to its cap: 832,256 candidates, none within 2
  cells of the end, no contact; best approach 36.0 halvings at width 2^46.0 (m = 35,561,341,614,704,
  E = 72,383,467,752,225), 10 short of a halt. So within the mark model no run that enters the plain loop through
  one of these 2,767 prefixes can halt, at any width. For 433 of them not even one plain pass is consistent after the
  route; for the rest exactly one loop phase is.
  End-to-end check of the enumeration (`../conc/enumcheck.py`): of 3 million random GMM states at width 2^18, the 25
  that follow the main route and then complete the one pass a halt there needs are all in the candidate list.
  **All routes to 42 bits** (`../csearch/rtree.c`, `../rtree2json.py`, `../conc/routeexclude3.py`,
  `../rt42_summary_0*.txt`, `../rt42_check_0*.txt`). The Python tree was slow because its coset basis was never
  reduced and its entries grew without bound; `rtree.c` keeps the basis of (m, E) in Hermite normal form and positions
  as dyadic forms in 64-bit integers, with order taken at the same asymptotic point. It reproduces the Python output
  exactly at 22, 26 and 30 bits (every prefix, every measure), and runs 30 bits in 0.25 s and 42 bits in 20 s.
  `routeexclude3.py` is routeexclude2 with integer positions and passes added incrementally (identical per-route
  results on the first 300 routes). Prefixes into G W W W: 617, 2,767, 10,636, 45,482, 191,415 at 26, 30, 34, 38, 42
  bits; into G W W W W: 20, 144, 628, 2,737, 11,507; undecided measure 1.7 × 10⁻⁴, 4.4 × 10⁻⁵, 1.2 × 10⁻⁵, 3.0 × 10⁻⁶,
  7.7 × 10⁻⁷ (about 3.9 times less per 4 bits). From 34 bits on, every one of the 1,019 sampled deep segments (h ≥ 8)
  that enters the plain loop does so through a listed prefix; the 1,020th never enters it. In no run of the 42-bit tree
  (first or later in its segment; a run is a chain of end meetings, each at pred of the last) does an end meeting
  before the run reaches G W W W come closer than 2^-10.65 of the width at any ratio (7.61 at 30 bits, 9.24 at 38), so
  a run that never reaches the plain loop is nowhere near a halt within these digits. All 191,415 prefixes, in
  both phases, with slack 12 and widths up to each cap (at most 2^100): 862,168 candidate states, none within 2 cells
  of the end, no contact; the best is still the main-route state at 2^46.0 (36.0 halvings), then 35.2 at 2^46.5 and
  34.7 at 2^45.9. First entries into G W W W W up to 42 bits (8,946 prefixes with a single G W W W W), by the
  extra-wall words their position map allows: 8,304 none, 552 one pass, 82 two, 8 three, none four (entry measure
  2.06 × 10⁻⁵, 7.2 × 10⁻⁸, 2.7 × 10⁻¹⁰, 9.8 × 10⁻¹²), the same proportions as the families built by hand below.
  **To 46 bits** (`rtree 46`: 759,918 prefixes into G W W W, 39,957 into G W W W W, undecided 1.96 × 10⁻⁷, most
  pre-loop halvings 12.63). The 568,503 prefixes new since 42 bits, through the same exclusion (`../rt46_summary_0*.txt`,
  caps up to 2^110): 4,277 more candidates, none halting or touching (best 34.8 halvings at 2^44.2), so 866,445 in all
  for the 759,918 prefixes. The 22,102 new first entries into G W W W W give 1,243 more chains (X 612, Z 322, U 154,
  Y 93, T 48, V 14), and none leaves a candidate (`../chains46_summary.txt`): 1,989 chains in all. The undecided measure falls by a factor 0.730, 0.704, 0.710, ... per bit from 20 bits on,
  settling near 0.710 by 40 to 45 bits (0.7098, 0.7097, 0.7093, 0.7096), close to 2^-1/2 = 0.7071: asymptotically the
  undecided segments branch about every second binary digit. The 22,102 new first entries into G W W W W allow, by
  their position maps, no pass (20,812), one (1,132), two (144), three (13) and, for the first time, four (one entry,
  measure 2.8 × 10⁻¹⁴, words Q P Q P and Q P Q Q). An explicit GMM state takes it: m = 45,072,343,224,448,
  E = 73,042,261,923,305 (width 2^46.1) runs its route and Q P Q P, four extra-wall passes in a row, and its segment
  still comes no closer than 18.6 halvings (46 needed).
  **Every chain from these entries** (`../conc/chains42.py`, `../chains42_summary.txt`): for each of the 8,946 first
  entries, the extra-wall words allowed on the route's own coset (8,308 none, 548 one pass, 82 two, 8 three), each
  followed by every drop into the plain loop that stays consistent: 746 chains (X 343, Z 201, U 98, Y 72, T 20, V 12,
  so 130 that keep their progress). Run through the exclusion with slack 12 up to each cap (at most 2^109): 636 of the
  1,492 route-phase rows allow some plain passes, and no chain leaves a single candidate state at any width.
  **The tree does not depend on where the marker sits.** With order taken at m/E = 1/64, 1/16, 1/8, 1/4, 5/16, 3/4,
  7/8, 15/16 and 63/64 instead of 1/2, the trees to 34 bits (and to 42 bits at 1/64, 5/16, 63/64) are identical,
  prefix for prefix and measure for measure. Instrumented (`rtree_cmp.c`), none of the 250.8 million order
  comparisons in the 38-bit tree has a leading part (a·m + b·E with the coefficient differences) that changes sign
  between m/E → 0 and m/E → 1; 50.3 million have equal leading parts and are decided by constants. So every branch
  holds for all large E at every interior ratio, and the coverage and exclusion statements hold for every m/E, not
  just near 1/2.
  **Route ceilings: the sharp lock does this exclusion by algebra** (October 23; `../csearch/rtree3b.c`, outputs
  `../rt3/`; the lock is under "Sharpened by the exact end of the loop"). At every phase-0 plain entry the tree
  reaches (a G W W W followed by G B W and G M B, in any run of the segment, after any extra-wall pieces), R₁ and L₁
  are forms in (m, E), so as E → ∞ the entry's σ is a function of t = m/E alone. Its maximum over 0 < t < 1 is the
  entry's **σ ceiling**, and by the lock no GMM state following that route can halt through that plain stretch at a
  width above 2^(ceiling + 6.38). The main route has R₁ = (3E − m + 13)/8 and L₁ = (854E − 343m − 1030)/16, so
  σ(t) = 3 log₂(8/(3 − t)) + 2 log₂((854 − 343t)/16) runs from 15.72 (t → 0) to 15.99 (t → 1): **the main route, 90% of
  pass-start lines, cannot lead to a halt above width 2^22.4 for any GMM state at all.** Over the whole tree (two
  parts each to 58 bits, 80 minutes there; sixteen parts at 62 bits, 5.6 CPU hours):

  | cut | undecided share | largest ceiling | no halt through a listed entry above | most halvings in a run before G W W W |
  |---|---|---|---|---|
  | 30 bits | 4.4 × 10⁻⁵ | 30.15 | 2^36.5 | 7.61 |
  | 46 bits | 1.96 × 10⁻⁷ | 42.26 | 2^48.6 | 12.63 |
  | 50 bits | 4.97 × 10⁻⁸ | 42.26 | 2^48.6 | 13.19 |
  | 54 bits | 1.26 × 10⁻⁸ | 43.32 | 2^49.7 | 15.63 |
  | 58 bits | 3.23 × 10⁻⁹ | 47.29 | 2^53.7 | 16.65 |
  | 62 bits | 8.25 × 10⁻¹⁰ | 52.86 | 2^59.2 | 16.66 |
  | 64 bits (checked arithmetic) | 4.14 × 10⁻¹⁰ | 54.25, excluded by its own R₁ ≡ 12 (mod 16); next 52.86 | 2^59.2 | 16.66 |

  (The parts split the tree at 20 binary digits, so entries found before that are seen by every part; the combined
  figures subtract the 19-digit tree's entries for every part but one, which reproduces a single-run 46-digit tree
  exactly. Only the ceilings' shares below 22 were affected; the maxima and undecided shares never were.) The tree is
  identical, entry for entry and measure for measure, with order taken at m/E = 1/2, 1/64, 63/64 and 5/16 (46 digits),
  so the ceilings hold at every ratio, as the chain lemma says.

  The ceilings' tail at 58 bits, as a share of GMM states: ≥ 20: 6.4 × 10⁻⁶, ≥ 25: 7.8 × 10⁻⁹, ≥ 30: 1.2 × 10⁻⁹,
  ≥ 35: 6.7 × 10⁻¹¹, ≥ 40: 4.8 × 10⁻¹⁴, ≥ 45: 4.5 × 10⁻¹⁷ (about one binary digit per unit of σ, as the extra-wall
  price predicts). The largest ceiling grows by about a unit per digit of depth at the tail end, so the first entry
  with a ceiling of 53.6 (the one that could matter beyond the exhaustive range) should appear near 64 digits.
  Checks on the engine, each entry rebuilt as integer GMM states in its coset: the 38.965 entry (route G M M M,
  G M M W, G M W W, G W W W, G B W, G W W M M, …) at width 2^60 follows the route at m/E = 0.99 and 0.5 and enters with
  σ = 38.961 and 38.799; the 46.772 entry (37 rounds, through G M M W W, G M W W W, G M B W and G M M B pieces) at width
  2^62 enters with σ = 46.771 and s = 11.34; the largest at 58 digits, 47.293 (G M M M, …, G M M W W, G M W W W, G M B W, G M W W W,
  G W W W W, G B W W, G M M W W, …, G M B W, G M M W, G M W W, G W W W, G B W, G W W W, G B W, G M B), enters with
  σ = 47.292 and s = 12.76 at m/E = 0.99 and 47.225 at 0.3; the largest at 62 digits, 52.855 (61 digits, 41 rounds:
  G M M M, G M M W, G M W W, G W W W, G B W, then two Q-like passes, a P and loop pieces), enters 15.08 halvings below
  the width with σ = 52.854 at width 2^64, so it allows a halt only below 2^59.24, inside the exhaustive range with
  0.76 digits to spare. On that route `../stepper/pincand.js` (exact candidates: every point of the route's coset with
  R₁ = 16^p · r for r in the close set and L₁ in r's class, tested against brute force on 300 random lattices) finds
  13,378 states with R₁ pinned at widths 2^40 to 2^62 and none with L₁ in its class.
  **Exact candidates for every decided route, at every width** (`../rt3/pinforms.py`, reading the entry forms the
  tree prints; the enumeration agrees with brute force on a 2^34 box, 43 pinned points both ways, and the forms agree
  with the engine at random coset points). For all 232,456 plain entries of the 46-digit tree, at every width from
  2^17 to the entry's lock limit 2^(ceiling + 6.38): **no GMM state has both R₁ = 16^p·r and L₁ in r's class**, so none
  can halt through its plain stretch; the pinning is a necessary condition (the full closing coset at R = 176 has
  density 2⁻¹¹, its L₁ projection 2⁻⁷), and even it is never met. Below 2^18 every GMM state was run directly
  (October 20). This replaces the 866,445 slack-12 candidates of the 46-digit exclusion with an exact count of zero;
  the 64-digit tree is being run with the forms of every entry of ceiling ≥ 20 printed (all 130 million entries
  would be 40 GB; those below 20 can only matter below width 2^26.4). What excludes the 232,456 entries
  (`pinclass.py`): the route's own tests fix R₁ modulo a power of 2 (mod 4 for 201,698 entries, mod 8 for 26,843, up
  to mod 256 for 3), and for 11,305 no closing value 16^p·r lies in that class at all; for 7,915 more the L₁ class is
  inconsistent on every pinned line; for the remaining 213,236 both congruences are consistent and the pinned lines
  simply carry no coset point in the width window the lock leaves.
  **Arithmetic check (October 24, morning).** The 64-digit tree (`rtree3c`, 64 parts, 12 CPU hours) gave undecided
  4.1 × 10⁻¹⁰, largest ceiling 54.249, no other entry above 53.6, and no exact candidate among its 5,983,365 entries
  of ceiling ≥ 20 at any width from 2^17 — but 37 of its 52 part files dropped a few paths as invalid (a negative
  distance), which never happened to 52 digits. Printing them shows position forms whose constants reach 7 × 10¹⁸
  after about 57 halvings in one segment: the form coefficients are 64-bit integers, and offset × 2^e overflows there.
  So the deep paths of the 64-digit tree, and possibly a few at 62, are suspect; the top entries at 58 and 62 were
  verified on the engine and stand. `rtree3d` checks every form addition in 128-bit arithmetic and drops a path as
  undecided at the first overflow, so every entry recorded before it is exact; it reproduces `rtree3c` bit for bit at
  30 and 40 digits. The 64-digit tree was rerun with it (next paragraph), which settles the 62-digit figures too; those to 58
  digits were never affected (their forms stay below 2^61).
  **The 64-digit tree, rerun with checked arithmetic (October 24, afternoon; `rtree3d`, 64 parts at split level 20,
  `../rt3/c64d/`, about 16 CPU hours over three restarts).** No path was dropped as invalid this time; 113,555 paths
  of total measure 8.1 × 10⁻¹⁵ stopped at a coefficient overflow and are counted as undecided. Entry measure
  2.072721 × 10⁻³, undecided 4.141 × 10⁻¹⁰, largest ceiling 54.249 (63 digits, the R₁ ≡ 12 (mod 16) route), then 52.855
  (61 digits), 49.003 (64), 48.633 (61), 47.611 (61); among the entries decided within 62 digits the largest ceiling is
  52.855. The tree has 5,983,365 entries of ceiling ≥ 20, the same count as the provisional run, and the exact
  candidate check over all of them at every width from 2^17 to each entry's lock limit finds none (`pin64d_all.txt`: entries 5983365, candidates 0). So the 62- and
  64-digit figures above stand without the arithmetic caveat; the 62-digit tree is not rerun separately, because every
  route decided within 62 digits is an entry of the 64-digit tree with at most 62 digits.
  *What the routes to late entries are made of* (`passtail.py` over the 5,983,365 entries): an entry whose route
  contains no round of the extra-wall loop has ceiling at most 33.63; the highest ceilings sit on routes with about 20
  such rounds (54.25 with 20, 52.85 with 21, 49.00 with 19), and every ceiling above 41.6 has at least 8. Complete
  passes of the extra-wall loop (the 8-round words P or Q) are rarer than pieces: 2,401 entries have one complete
  pass on the way (1,454 through P, 947 through Q; measure 6.5 × 10⁻¹⁴ in all) and one entry has two (P P, ceiling
  47.10, measure 2⁻⁶⁴); by ceiling bucket the one-pass routes carry 30 to 50% of the measure from 40 upward (3.4 versus
  1.5 × 10⁻¹⁴ at 40–44, 6.0 versus 3.7 × 10⁻¹⁷ at 44–48), and none below 20 is counted.
  **The first route past the threshold** (64-digit tree, part 1 of 16): ceiling 54.249 (63 digits; the 52.855 route
  with G M M W M, G M W W M, G M B M for its G M M W, G M W W, G M B), which the lock alone would allow at widths up to
  2^60.63. On its coset R₁ ≡ 12 (mod 16) at the entry, so it can neither complete a pass (R₁ ≡ 0 mod 64) nor close
  (R₁ ∈ {2, 4, 8, 16, 24, 32, 48, 64, 176}): **excluded at every width by the congruence alone**, no enumeration needed. A run that never reaches G W W W makes at most the halvings in the last column, and one that
  reaches it in the other phase without entering makes at most 8 meetings more (the exit search), so neither can halt
  at these widths; the cone-based count above (at most 8 meetings from any loop state without a phase-0 pass start)
  makes this exact. The tree drops no path as halted (packet reaching a block) or invalid at 46 digits (counted), so
  every path it follows ends in a clean tape, a GMM state, or the cut. Hence, within the mark model, **no GMM state
  whose segment the 62-bit tree decides can halt at a width above 2^59.24**, with no candidate search at all; the searches above to 2^100 and beyond were bound to find nothing
  past 2^48.6, the 46-bit tree's limit. For the machine, whose tapes below width 2^60 the exhaustive check covers,
  every GMM state decided within 62 binary digits is excluded, and the undecided share is 8.2 × 10⁻¹⁰, falling 0.71
  per digit. The first entry above 53.6, which would need the exact candidate search, should appear within a few
  more digits. The extra-wall chains
  that reach H = 18.9 (σ ≈ 66) were built by forcing their words past the cut and are part of that undecided share;
  their words cost 14 to 18 digits per pass on top of a 45-digit entry, so they lie well past 58 digits.
  **Late entries all go through the extra-wall loop** (`../csearch/rtree5.c`). Splitting the entries by whether the
  segment used any extra-wall shape (G W W W W, G B W W, G M B W, G M W W W, G M M W W) before the entry: at 46 digits
  the plain-only lead-ins stop at ceiling 30 (4.2 × 10⁻¹², nothing at 31 or above), at 50 digits at 32 (1.8 × 10⁻¹⁵),
  while every entry with a higher ceiling, up to the 42.26 maximum, has an extra-wall piece before it. That fits the
  census of repeating patterns: without extra walls every pattern parks at a fixed lateness, and the latest exits from
  those limits found by sampling give σ = 36.45. So beyond the exhaustive range, where the lock needs σ ≥ 53.6, a halt
  through the plain loop has to be led in by the extra-wall loop (measured, not proved: the plain-only bound rests on
  the sampled census), and a halt without the plain loop needs the extra-wall family anyway. Either way the extra-wall
  loop is the gate, and on the machine's two-number GMM families it is capped per family (see "Why chains fail on
  these tapes").
  *How often the machine should meet an entry the lock allows (heuristic).* The ceiling tail at 58 digits, converged up
  to σ = 42, falls 1.35 binary digits per unit of σ (log₂ P(ceiling ≥ x) ≈ 10.9 − 1.35x). The machine visits about
  1.6 GMM states per cycle (sampled at 30, 40 and 50 digits) and 2^b/8.97 clean tapes per octave, so about
  0.09 · 2^k GMM states of width near 2^k. If they hit routes like random points, the expected number beyond width 2^60
  with any plain entry that the lock allows (ceiling ≥ log₂W − 6.38) is about 0.13, or about 2 if the tail flattens
  to the extra-wall price of 1.13 digits per unit. So the lock by itself leaves of order one candidate entry in the
  machine's whole future. Each still has to line up: R₁ must equal one of 16^p · {2, …, 176} exactly and L₁ must sit in
  its class modulo 7 · 2^(6p+j), about 2^-(2.5(log₂W − s) − 11), which for an allowed entry at width 2^60 is about
  2^-106. Together, of order 10⁻³² expected halts. Counted instead as (route tail) × (exact pinning): per GMM state
  near width 2^k about 2^(10.9 − 1.35(k − 6.38)) × 9 · 2^(−2.5(k − s)) with s = (k − 20)/3 at the lock's edge, times
  0.09 · 2^k states, gives 2^(−2k − 2) per octave and about 10⁻³⁷ beyond 2^59. The two counts differ in how the
  pre-entry halvings are priced (0.9 extra per halving from the extra-wall measurement, or 4 per halving from the route
  tail); either is far below the earlier 10⁻²⁴ to 10⁻²⁷.
  **Why: the marks always form a chain.** Write each position as α·m + β·(E − m) + constant. The GMM state's marks
  sit at (α, β) = (0, 0), (1, 0) and (1, 1) (the end marker and the end both at (1, 1)). Every rule makes new positions
  in only two ways: a gap meeting the next mark to its right puts both, or the new wall, at their midpoint (plus a few
  cells), and everything else (packets turning walls into a marker and a gap, shifts, the end moving by 2 or 3, the
  round's shift) moves marks by constants. The midpoint of two neighbours that are ordered in both coordinates lies
  between them in both, so by induction the marks, read left to right, always have nondecreasing α and nondecreasing
  β. Two marks therefore differ by Δα·m + Δβ·(E − m) with Δα, Δβ ≥ 0, which has the same sign for every 0 < m < E: the
  order of the marks, and so every branch of the tree, never depends on m/E (only on the constants when Δα = Δβ = 0).
  Checked in the tree (`rtree_chain.c`): 16.6 million neighbouring pairs to 38 bits, no exception. In these
  coordinates a segment is a bisection process on a monotone chain from (0, 0) to (1, 1); a right-end run moves the
  last wall halfway to (1, 1) at every meeting, and a halt needs it to get within about 1/E of that corner.
  The same argument works from any starting configuration whose distances are free: in the coordinates "distance to
  the previous mark" the starting marks form a chain, so the order of marks, and every branch, is the same for every
  geometry with large distances. This proves the geometry independence that the exit search (`exit1.py`), the
  extra-wall loop words (`mixsolve.py`, `mixdrop.py`) and the virtual-point models had only checked.
  **No fixed-distance contacts on decided branches** (`rtree_contact.c`): among the 68.8 million pairs of neighbouring
  marks checked at round starts in the 42-bit tree, 13.1 million have equal leading parts, and every one of them is the
  end marker next to the end (distance 2 by definition). No other two marks ever sit at a width-independent distance,
  so the contacts the rules exclude (a marker against a wall, marks merging) cannot occur on a decided branch once the
  width is large; they would need a branch that is undecided at 42 bits or a near-coincidence at small width.
  **Chains** (`../conc/ewroutes.py`, `ewforms.py`, `ewwords.py`, `ewdrop2.py`): 144 prefixes reach the extra-wall
  state G W W W W within 30 bits (measure 2.07 × 10⁻⁵; 20 within 26). 130 allow no extra-wall pass at all, 6 allow P
  alone and 8 Q alone, and none allows any two-letter word. After the one pass, 15 drops into the plain loop are
  consistent: 11 resetting ones (X, Y, Z) and 4 that keep the progress (U, after Q three times and after P once).
  Run through the same exclusion, none of the 15 admits a candidate: after the four U drops not even one plain pass is
  consistent, and the X, Y, Z continuations leave no lattice point in any width range. So for these entries the
  extra-wall loop cannot carry a run: it runs at most once, and what follows is a single plain stretch that the lock
  and the candidate runs exclude. Since a single stretch can only finish from widths below about 2^(3H_r + 54) anyway,
  and the excluded routes carry 99.7% of the deep runs, the heuristic expectation of further halting GMM states beyond
  2^18 drops from about 0.014 to well below 0.001.
- **The extra-wall loop needs three free numbers, exactly** (`../conc/ewmap.py`, `ewlock.py`, `ewlock2.py`,
  `ewlock3.py`, `ew2pass.py`, `ewcap.py`). One P pass is an affine map of (w1, w2, w3, w4, E): w1 is forgotten (its
  column is zero), E moves by 24, and the rest contracts in three directions, R = E − w4 − 1 by 16, the left
  countdown −63w2 + 105w3 − 308w4 + 236E − 179/7 by 64, and a second direction with eigenvalue 1/16 tied to R (a Jordan
  block). Q contracts R by 16 and the (w2, w3) block by the 2-adic factors 2^-7 and 2^-5 (real eigenvalues
  (13 ± √153)/256). So every pass needs three countdowns to keep growing powers of 2. In a family of tapes with d free
  numbers they are three affine forms in d unknowns. With d ≥ 3 they can be met for any number of passes (only the
  archimedean size limits them). With d ≤ 2 they obey a linear relation, and its constant, one fixed number per
  family, must then be divisible by a growing power of 2 as well: each family has a hard cap on extra-wall passes,
  independent of the width. Tests on random affine families of wall positions with the right parities: with 3 or 4
  free numbers, P^n is either impossible from the start or consistent for every n tried (to 8), and 16 or all 32 of
  the P/Q words of length 5 are consistent; with 1 or 2 free numbers, no family allowed more than one pass of any word
  (for P^n, 59 of 60 and 56 of 60 allowed none; for all P/Q words with 2 free numbers, 37 of 40). GMM-born entries
  are two-number families, and their position map alone decides it: for all 144 entries the words allowed on the bare family (only m even, E odd) are exactly those allowed
  on the route's coset, 130 with cap 0 and 14 with cap 1 (0.3% of the entry measure). After the one pass, the second
  fails on a digit of the right countdown E − w4 (conditions 1, 5, 10 or 15 of P) or of its partner. This is the
  plane's version of the line-up found for clean tapes, where the plain loop already needs one per pass: a loop that
  contracts c directions can run unboundedly, 2-adically, only in families with at least c free numbers. The plain
  loop has c = 2 and the extra-wall loop c = 3; GMM states have two free numbers, each cycle's own states one. The
  tapes that halt with three free numbers (P¹⁰UL¹⁸, P¹⁷UL³¹) sit exactly at that threshold. The cap is per family, so
  it is not uniform: among infinitely many entry routes some will allow more passes, and each extra pass needs four
  more digits of one number to line up (6% of the time at random; 14 of 144 entries allow one).
  The partner of R is simply the last gap, w4 − w3 (`../conc/lineup.py`). On each entry family the three
  countdowns (taken without their constant terms) obey one relation with integer coefficients of 3 to 8 digits and an
  integer right side κ of 5 to 8 digits; for the commonest entry it is
  −75850(E − w4) + 16368(w4 − w3) + 335(−63w2 + 105w3 − 308w4 + 236E) = −61209. v2(κ) is 0, 1, 2 for 93, 36, 14 of the 144 entries and 6
  for one: the trailing zeros of a random integer, slightly favouring odd. So the cap behaves like the trailing zeros
  of a random number: no uniform bound, but every extra pass costs four more of them.
  **The rule holds for every number of extra walls** (`../conc/extkdim.py`, `../extkdim.txt`). For the loop with k
  extra walls (the plain loop with k walls appended, k = 0 to 3; k = 1 is P), the pass map forgets the first wall,
  keeps E neutral and contracts exactly 2 + k directions (14, 18, 22, 26 congruences per pass). Families through a
  point that makes one pass, with d random even directions: for d < 2 + k all 10 families stop after one pass (three
  of the 40 at k = 2, 3 get a second); for d ≥ 2 + k all 10 run every pass tried (5). So a family follows a loop
  2-adically without limit exactly when it has as many free numbers as the loop has countdowns. Two-marker states
  (d = 2) can do that only for the plain loop, where the archimedean lock still stops them at two thirds of the
  halvings; each cycle's own states (d = 1) can do it for no loop at all.
  **Caps above one exist, and get rarer by about a factor of 10 per pass** (`../conc/entrysfx.py`, `entrycaps.py`,
  `capdepth.py`, `construct2.py`, `../entrycaps.txt`). Taking each of the 2,767 30-bit routes into the plain loop,
  0 to 2 plain passes, and each of the 22 observed ways from G W W W into G W W W W gives 190,923 entry families. By
  their position maps alone: 190,263 allow no extra-wall pass, 571 one, 81 two, 8 three (checked to words of 10:
  none allows four). So each extra pass is about 7 to 11 times rarer than the last. The coset method then gives
  explicit GMM states whose segments really run them (mark model): m = 664,460,784, E = 12,963,564,217 (width 2^33.6)
  runs its route, 2 plain passes, the entry and Q Q; m = 793,076,764, E = 41,575,487,909 (2^35.3) runs P Q P; and
  m = 1,724,631,069,212, E = 4,031,531,220,709 (2^41.9) runs 2 plain passes, the main entry and P P P. These are not
  close calls: after the cap the run drops and starts over, and their segments come no closer than 13 to 15 halvings
  (against 33 to 42 needed). The "at most one pass" of the 144 tree entries is therefore a statement about the
  commonest entries, not a law; what is a law is that each family has a cap, fixed by its position map.
  **Chains built from them** (`../conc/chainfam.py`, `chainroutes.py`, `../chain_summary.txt`): for the families with
  a cap of 2 or 3, a progress-keeping drop (T or U) after one or two extra-wall passes is consistent in 15 cases, and
  then, as the rule predicts for the plain loop (2 countdowns, 2 free numbers), every plain pass tried (8) is
  consistent on the bare family: these chains are limited only by the archimedean lock. Run through the exclusion
  (route, plain passes, entry, extra-wall word, drop, then p plain passes; slack 12; widths up to each cap, 78 to 100),
  all 15 leave no candidate at any width: the route's own digits plus the chain's leave no lattice point in range.
  **What such a chain can do** (`../conc/chainconstruct.py`): for the chain route 5, 2 plain passes, entry, Q, Q, T,
  the smallest GMM state that also runs q more plain passes has width 2^37, 2^43, 2^45, 2^53, 2^57, 2^64, 2^68, 2^73,
  2^77 for q = 0 to 8 and comes within 14.0, 14.0, 15.8, 19.8, 23.8, 27.8, 31.8, 35.8, 39.8 halvings of the end
  (e.g. q = 8: m = 2,968,377,119,794,420,964,848, E = 297,817,672,592,472,448,977,593). Each plain pass adds 10 binary
  digits to the coset, so about 5 to the width the first such state needs, and buys 4 halvings: the shortfall grows by
  about one halving per pass (38 short at q = 8). This is the two-number counting made concrete: 2·log₂E digits at
  2.5 per halving buy at most about 0.8·log₂E halvings, and the lock allows only two thirds of log₂E in one stretch.
- **The same tails, exactly, from the 2-adic tree** (`../csearch/rtail.c`, `../rtail46.txt`, `../rtail50.txt`). Each
  completed branch of the tree is a coset of (m, E); for each of its end meetings, with the distance d = a·m + b·E + c
  over 2^e, the ratios t = m/E at which d ≤ 2^-x·E form an interval (the leading part is linear in t), so the share of
  t in (0, 1) at which the segment comes within 2^-x is exact. Weighted by the cosets' measures, the 50-bit tree
  (3,227,592 prefixes into G W W W, undecided 5.0 × 10⁻⁸) gives, for x = 3 to 18: 4.1336 × 10⁻², 1.7660 × 10⁻³,
  2.0761 × 10⁻⁴, 5.4962 × 10⁻⁵, 8.084 × 10⁻⁶, 2.561 × 10⁻⁶, 1.940 × 10⁻⁷, 5.509 × 10⁻⁸, 8.01 × 10⁻⁹, 2.57 × 10⁻⁹,
  1.85 × 10⁻¹⁰, 5.20 × 10⁻¹¹, 7.2 × 10⁻¹², 2.3 × 10⁻¹², 1.1 × 10⁻¹³, 2.7 × 10⁻¹⁴ (to x = 12 they change by under 1%
  from 46 to 50 bits). They agree with the count of every GMM state of width 2^17 to 2^18 below (4.13 × 10⁻²,
  1.765 × 10⁻³, 2.07 × 10⁻⁴, 5.48 × 10⁻⁵, 8.06 × 10⁻⁶, 2.52 × 10⁻⁶, 1.95 × 10⁻⁷, 5.45 × 10⁻⁸, ...), so the tail is
  an asymptotic property, not a finite-width effect. It falls with period 4, one pass of the plain loop: from x = 8 to
  16 by 2^20.08, i.e. exactly 10 binary digits per 4 halvings. Halving by halving the price repeats as 3.7, 1.8,
  2.8, 1.65 digits (x = 8 → 9, ..., 11 → 12 and again 12 → 13, ..., 15 → 16), the four meetings of a pass.
- **Exact per-segment tails** (`gmmseghist.c`, every GMM state, segment only): the share with h ≥ x is the same at
  every width, 4.1 × 10⁻², 1.76 × 10⁻³, 2.07 × 10⁻⁴, 5.4 × 10⁻⁵, 8.0 × 10⁻⁶, 2.4 × 10⁻⁶ for x = 3 to 8, then (widths
  2^15–2^16, 4 × 10⁸ states) 1.9 × 10⁻⁷, 4.5 × 10⁻⁸, 5.0 × 10⁻⁹, 2.5 × 10⁻⁹ for x = 9 to 12: about 2.43 binary digits
  per halving from x = 4 to 12, where x/log₂E reaches 0.8. The best state per width range stays 3 to 4 halvings short
  of a halt from 2^12 to 2^18. At widths 2^17–2^18 (all 6.44 × 10⁹ states): 4.13 × 10⁻², 1.765 × 10⁻³,
  2.07 × 10⁻⁴, 5.48 × 10⁻⁵, 8.06 × 10⁻⁶, 2.52 × 10⁻⁶, 1.95 × 10⁻⁷, 5.45 × 10⁻⁸, 9.0 × 10⁻⁹, 2.0 × 10⁻⁹,
  1.6 × 10⁻¹⁰ for x = 3 to 13 (2.47 digits per halving from 4 to 12; the last values rest on 13 and 1 states).

## The top of the class tree, explicitly (`../csearch/residuejump.c`)

Running the class cycle at depth 5 settles 29 of the 32 residues (for every member n ≥ 32): n' = n + 3 for odd n (2
rounds), n + 6 for n ≡ 0 (mod 4) (3 rounds), n + 9 for n ≡ 6, 10 (mod 16) (5 rounds; chain 1 and 2 respectively), and
n + 12 for n ≡ 2 (mod 32) (6 rounds, chain 2). Only n ≡ 14, 18, 30 (mod 32) need more digits, and every right-end chain
of 3 or more meetings lies in those residues (the records 73,742, 363,165,946,702 and 391,305,139,022 are all
≡ 14 mod 32). Within them the jump is a 2-adic tree: along n = 2^40 + 14 + 32t, J = 15 whenever t ≡ 3 (mod 4), 18
whenever t ≡ 4 or 6 (mod 8), 21 when t ≡ 13 (mod 16), and anything from 21 to 54 deeper down.

## The trajectory as a track (`../csearch/tmap.c`, `../csearch/fastfollow.c`)

- **A finite map.** For settled residues the jump depends only on n mod 2^k. So the trajectory mod 2^k is an orbit of
  T(r) = r + J(r), which branches only at open residues.
- **Laps repeat.** Mod 2^20, each lap of 3·2^20 visits a third of the residues, and consecutive laps share 99.3%.
- **Each class is visited once per lap or never.** For example, the 11-meeting class first visited at
  n = 37,558,132,238 returned at exactly n = 140,637,347,342 = 37,558,132,238 + 3·2^35.
- **The track favours cascades.** Deep cascades occur about 2.3 times as often as in a random n. Most of this is
  parity and low residues, and it is fully explained by a Markov chain (October 20, `../csearch/trajbias.c`,
  `trajres.c`, `trajmarkov.c`, `trajent.c`, 10⁸ cycles of the real trajectory from n = 999,385,276,430):
  - Odd n always have a one-meeting chain and jump by exactly 3; they are 35% of the trajectory's visits.
  - A chain of 2 or more meetings happens exactly when n ≡ 2 (mod 8), or for n ≡ 14 (mod 16) in about two thirds of
    cases. The trajectory visits n ≡ 2 (mod 16) 18% of the time instead of 6.25%.
  - Build the chain on residues mod 2^k whose transition r → r + J (mod 2^k) has the frequencies of Haar-random n.
    Its stationary law is far from uniform (from 0.015 to 2.9 times uniform mod 16, up to 3.05 mod 1024, with 54 of
    256 residues mod 256 essentially never visited), and the trajectory's visit frequencies match it to a total
    variation distance of 0.010 mod 16, 0.0032 mod 256 and 0.0041 mod 1024, about the sampling noise. So the
    trajectory is a typical path of that chain: no extra attraction to, or avoidance of, any residue class.
  - At depth 14 and beyond, the trajectory's visits are uniform on a set of 2^k/3 residues (entropy within 0.1 bits
    of k − log₂3), the lap structure above: each lap passes once through each n ≡ 2 (mod 3) residue it touches.
  - Among even n, chains of 2 to 6 meetings are 1.6 to 2.2 times more common on the trajectory than in random even
    n, and chains of 10 or more about 2 times. So along the trajectory the odds of any deep class are within a factor
    of about 3 of their 2-adic measure.
- **The follower.** It looks jumps up in the table of classes settled by 33 digits and simulates only the open
  residues, checking itself every 2^20 steps. It reached n = 10^12 after 110,250,943,952 cycles, with 103,032
  checks passed. Longest cascade: 14 meetings, at n = 391,305,139,022.

## Heuristic odds of a halt above 2^45 (`halt_odds2.py`)

- Only top-running integers can halt. Fit to all of them with 22 to 41 digits: their number with b digits that get x
  halvings is about A·G^b·r^-x, with G = 1.63 and r = 3.52. The fitted r stays between 3.43 and 3.69 at every size.
- A halt needs x ≈ b, so each digit multiplies the expected number by G/r ≈ 0.46.
- Expected number of halting integers above 2^45: about 5 × 10^-16, and about 10^-16 along the trajectory. With
  r = 3.0 it would be about 6 × 10^-13.
- This is an extrapolation, not a proof. The largest number of halvings observed among the 9.2 million top-running
  41-digit integers is 13.
- **The machine's own family, exactly** (October 20, evening; `../csearch/rtree1d.c`, `../rtree1d_44.txt`). The
  2-adic tree of whole cycles from even clean tapes: positions are forms (a·n + c)/2^e, order as n → ∞, every undecided
  test splits the class, and each class is followed through all its segments to the clean tape. It reproduces the
  exhaustive check's settled-class counts level by level (6, 12, 18, 43, 46, 62, 95, 163, 283, 498, 606, 834, 1,378,
  2,222 at 10 to 23 digits) and runs 44 digits in under 5 minutes (68.5 million classes, undecided 4.3 × 10⁻⁶). At 48
  digits it completes 368,839,405 classes, exactly the exhaustive check's 368,839,406 settled classes through 49 digits
  less the one odd class. Share
  of even n whose cycle comes within 2^-x of the end, as n → ∞ in its class, for x = 4 to 12: 8.58 × 10⁻⁵,
  1.55 × 10⁻⁵, 1.37 × 10⁻⁶, 2.43 × 10⁻⁷, 9.26 × 10⁻⁸, 2.29 × 10⁻⁸, 9.29 × 10⁻⁹, 9.8 × 10⁻¹⁰, 4.9 × 10⁻¹⁰ (still rising
  by a few percent per 4 digits; extrapolated limits about 9.4 × 10⁻⁸ at x = 8 and 5.2 × 10⁻¹⁰ at x = 12). Against a
  single two-marker segment this is 30 times thinner at x = 8 but only 5 times at x = 12: the line's tail falls 2.46
  digits per halving from x = 4 to 8, like the plane's, and only about 1.9 from 8 to 12, close to the top-running fit's
  1.82. But the tail is lumpy (`rtree1d_chain.c`, `rtree1d_deep.c`): 95% of the share with x ≥ 12 is two classes at
  depth 32, those of n = 575,152,510 (the 12.4-halving record below 2^30) and n = 4,321,786,462; without them the share
  at x ≥ 12 is about 2 × 10⁻¹¹ and the fall from 8 to 12 about 2.8 digits per halving. Past that lump the tail is
  steep again: at 48 digits the shares at x = 12, 13, 14 are 4.93 × 10⁻¹⁰, 3.65 × 10⁻¹², 2.25 × 10⁻¹², and from x = 8
  (9.36 × 10⁻⁸) to x = 14 the fall is 2.55 digits per halving. The 14-halving classes are the
  known records (363,165,946,702 at depth 40; 391,305,139,022, 3,185,173,435,214 at 41; 7,646,547,907,406 at 42). The
  shallowest class reaching a chain of L meetings sits at depth 18, 23, 27, 27, 28, 28, 32, 32, 40, 40 for L = 5 to 14:
  about 2.4 digits per meeting along the frontier. A halt at b digits needs about b meetings, so a class of depth near
  2.4b whose smallest member has only b digits, odds of about 2^(-1.4b) per digit level, which sums to about 10⁻²² beyond
  2^51 if the frontier keeps its slope. It seems to steepen: the exhaustive check found no chain longer than 14 among
  all n < 2^51, and since every class has j_min ≤ 1, a class of depth up to 50 with a chain of 15 would have shown
  members there. So 15 meetings need a class deeper than 50 digits, 10 or more digits after 14 first appears at 40. Deep runs on the line come from rare shallow classes with unusually
  long chains. The likely reason: on a one-number line each plain pass costs 6 digits of n plus a line-up that belongs to the
  route (the gap of "On the machine's own tapes, each gap is a count of binary zeros"), so where a route's gap allows
  them, passes cost 6 digits each instead of the 10 a two-number family pays. Gaps are bounded per route (none above 12
  by 43 digits), so for much deeper runs the price should rise back toward 2.5 digits per halving, but where that
  happens is not measured, and with the tail this lumpy no fit to x ≤ 12 settles it. Extrapolating 1.9 digits per
  halving from x = 8 (share 9.4 × 10⁻⁸) to the x ≈ b a halt at b
  digits needs gives about 3 × 10⁻¹⁷ over all n ≥ 2^51 (the top-running fit's 10⁻¹⁷ is the same estimate); 2.5 digits
  per halving gives about 10⁻²⁵, and the plane-based count 10⁻²² to 10⁻²³. So the heuristic odds should be quoted as
  roughly 10⁻²⁵ to 10⁻¹⁶, before the route exclusion.
- **Where the price goes back up: lines of GMM states, measured** (October 20, night; `../csearch/rline.c`,
  `../csearch/r1dlines.c`, `../lines/sample.py`, `../lines/machlines.py`, `../lines/lines_46_3.json`). `rline` is the
  exact tree of one segment over a line of GMM states m = m0 + a_m·t, E = E0 + a_E·t (t free, order as t → ∞, which the
  chain lemma makes legitimate for every 0 < a_m < a_E). Checked against direct runs of 133,000 points on two lines.
  - *Lines are very unequal.* Of 6,000 random lines (primitive directions up to 31, random offsets, 46 digits of t),
    49% never come within 2^-3 of the end at all; on (2t + 2, 6t + 5) the best of 133,000 points is 1.26 halvings, while
    (2t, 6t + 1) has 7.4% of its points past 3 halvings. Averaged over the lines the tail is the plane's (4.16 × 10⁻²,
    1.79 × 10⁻³, 2.05 × 10⁻⁴, 5.53 × 10⁻⁵, 7.25 × 10⁻⁶, 2.59 × 10⁻⁶, 1.97 × 10⁻⁷ for x = 3 to 9, against 4.13 × 10⁻²,
    1.77 × 10⁻³, 2.08 × 10⁻⁴, 5.50 × 10⁻⁵, 8.08 × 10⁻⁶, 2.56 × 10⁻⁶, 1.94 × 10⁻⁷), but from x = 10 on almost all of it
    sits on a few lines: the top 1% of lines carry 95% of the share at x = 10 and all of it from x = 12.
  - *The price splits in two.* On the lines that reach x + 4, the next four halvings cost a median of 6.50, 6.00, 5.99,
    6.30 digits of t for x = 10 to 13: exactly one plain pass paid with the left countdown alone. The share of lines that
    reach x falls by 1.04, 0.83, 1.10, 1.27, 1.45 digits per halving for x = 11 to 16 (779, 378, 212, 99, 41, 15 of the
    6,000 lines reach 11 to 16): about four digits per pass, which is the right countdown's line-up, paid once by the
    line rather than by its points. Together, 10 digits per pass, the plane's 2.5 per halving. This is the dimension rule
    seen from inside: a one-number family runs the plain loop at 1.5 digits per halving until its own line-up runs out,
    and going deeper means a different line that lines up further, at one more digit per halving.
  - *The machine's lines are ordinary.* Every GMM state that a class of even n reaches within 24 digits is itself a line
    in the class parameter (11,730 of them; all have a_E = 2^(depth + 2), so E is fixed to that many digits, and a_m is
    2 × odd in 98%). Against random lines of exactly that shape, each run 30 digits deep: the share that reaches x is
    0.523, 0.433, 0.173, 0.054, 0.027, 0.0086, 0.0047, 0.0005 for x = 4, 6, 8, 10 to 14, against 0.487, 0.446, 0.187,
    0.050, 0.018, 0.0072, 0.0032, 0.0016; the mean tail per line is lower than random at x = 6 to 10 (by 2 to 9 times) and
    similar at 11 to 14. So the machine's own lines line up no more often than random ones.
  - *The lumps are lucky lines* (`../csearch/r1dseg.c`, `../lines/seg40.txt`). For every class of even n completed
    within 40 digits whose cycle comes within 2^-10, take the segment that holds its closest meeting and the line of GMM
    states that segment starts from. The 386 classes with x ≥ 10 sit on 31 lines, and one line, (7138t + 72,
    8192t + 93) at depth 11, carries 81% of their share; the 80 with x ≥ 11 sit on 14 lines, half the share on
    (18t + 8, 512t + 229) at depth 7; the 6 with x ≥ 12 sit on 6 lines, 98% of the share on two. Each of these lines
    stops at a fixed reach: 12.50 halvings for (18t + 8, 512t + 229), unchanged at every depth from 34 to 70 digits of
    t (undecided 6 × 10⁻¹⁷ at 70: on this line the segment tree all but closes), 10.38 for the line that dominates
    x = 10, 12.38 and 12.12 for the next two; and up to it the line's tail falls exactly 6 digits per 4 halvings
    (1.9 × 10⁻⁶ at x = 8 to 3.0 × 10⁻⁸ at x = 12 on the depth-7 line). So at any depth the machine's tail is a staircase
    of lines, each paying 1.5 digits per halving until its line-up runs out and then nothing.
  - *The extra-wall loop on the machine's lines* (`../lines/w5_28_c40.txt`). Counting G W W W W round ends in every
    completed class of one segment, over all 64,665 lines of depth ≤ 28 followed 40 digits further: 46,805 lines never
    reach that state, 12,390 at most once per class, 5,041 twice, 359 three times, 69 four times and one line five
    times. In measure (even n): 1.2 × 10⁻⁷ reach it at all, 1.5 × 10⁻¹¹ three or more times. The five-time class
    (n = 307,127,793,147,373,625,554, checked by `cycles.py`) completes one extra-wall pass and starts a second, and
    its cycle comes no closer than 7.0 halvings. On the machine's own tapes the extra-wall loop is a curiosity: about one
    pass at most where it occurs at all, far from any close approach.
  - *A line's reach is predicted by its line-up* (`../csearch/lined.c`, KAPPA mode, `../lines/kappa28_c30.txt`). At
    every three-wall state in a line's tree, R = E − c − 1 and L₁ = 147b + 280E − 392c − 578 are linear in the class
    parameter y; the most loop meetings any member can make is the largest j for which some y has v2(R) ≥ j + 1 and
    v2(L₁) ≥ ⌊3j/2⌋ + 1 (one zero of R and on average 1.5 of L₁ per meeting), found by solving two congruences mod
    powers of 2. Predicted reach = halvings so far + j + 3. Run on all 64,665 lines of depth ≤ 28 with only 30 digits
    of tree (56 s), against their true reach at 46 digits: selecting predicted ≥ 16 picks 730 lines (1.1%) and catches
    all 58 lines with true reach ≥ 17 (all 26 with ≥ 18, all 15 with ≥ 19); for lines with true reach ≥ 14 the error
    has median 0 halvings (quartiles −0.9 and +1.5). So the passes a line allows are set by the trailing zeros of its
    two countdowns, exactly as the line-up argument says, and lucky lines can be found without following the loop.
    The predictor also measures the one assumption behind the odds directly: the share of lines whose best route
    allows at least j loop meetings is 0.236, 0.070, 0.0186, 0.0055, 0.0017, 5.4 × 10⁻⁴, 1.7 × 10⁻⁴ for j = 4, 6, ...,
    16 over the 64,665 lines of depth ≤ 28, and 0.186, 0.057, 0.0152, 0.0041, 0.0010, 3.2 × 10⁻⁴, 6.2 × 10⁻⁵ over the
    628,853 at depths 31 to 34: 0.85 to 0.99 binary digits per loop meeting, the odds of one more trailing zero. So the
    line-ups behave like the trailing zeros of random numbers, out to 20 meetings.
  - *The tail to 14 halvings has converged.* Summing 2^-depth times each line's own share over the 140,797 lines of
    depth ≤ 30, each followed 46 digits further (up to 76 digits of n), gives 4.96 × 10⁻¹⁰ at x = 12 and
    2.28 × 10⁻¹² at x = 14, against 4.935 × 10⁻¹⁰ and 2.245 × 10⁻¹² from the 48-digit tree: the lumps are final, not a
    truncation effect. Beyond 14 the same sum is still incomplete (each line depth from 27 to 30 adds about 2^-54 at
    x = 15, with no sign of decay yet), so it is not quoted.
  - *Reaches are not fixed forever.* A line is itself a one-number family, and other routes on it can go further with
    many more digits. For 12 live lines sampled from the machine's 64,665 lines of depth ≤ 28 (8 of 20 are dead, below
    2 halvings at every depth), the reach of one segment rose from 9.0 halvings on average at 40 digits of t to 9.8 at
    50, 11.1 at 60 and 12.2 at 70, about 0.1 halving per digit (one line went 8.4, 9.2, 11.4, 16.4). The undecided share
    of a line falls about 0.59 per digit, faster than the plane's 0.71.
  - *What this does to the odds.* The 1.9 digits per halving that the machine's tail shows from 8 to 12 is what a few
    shallow lines produce while their line-ups last (1.5 digits per halving on each, diluted by the lines that drop
    out). It cannot persist: every line has a cap, and lines that reach deeper are rarer by about a digit per halving,
    for the machine's lines as for random ones. On average the price is the plane's 2.5 digits per halving, so the
    random-point figure of 10⁻²³ to 10⁻²² (before the route exclusion) is the better estimate, and the extrapolation to
    10⁻¹⁶ has no support. This remains a heuristic; it says nothing about a single unlucky line.

## Summary of the right-end theory (October 19)

1. **Halting route.** The machine can only halt when a right-end run of meetings brings the last wall within a couple
   of cells of the end (or when marks touch, which the contact standard excludes on the machine's own tapes). This is
   confirmed in both directions: hand-built small tapes on which the loop drives the wall to the end do halt (72
   cells, 10,302 steps), and on every three-wall round start of width 40 to 130 the machine halts only when the mark
   model's run reaches d ≤ 2 or marks touch.
2. **One loop.** Every long run uses one 8-round loop, 4 meetings per pass. A pass is two exact countdowns: R = E − c − 1
   (÷16) and L₁ = 147b + 280E − 392c − 578 (÷64). Cost: exactly 10 bits per pass. It is the cheapest way to continue a
   run (exact branching from generic block states).
3. **The lock.** L₁ ≡ 3 (mod 7) is never 0 and |L₁| ≤ 280E, so one stretch of the loop makes at most log₆₄(280E) passes.
   Leaving the loop is exhaustively short (≤ 8 meetings, no return). In general: any repeated pattern with a
   non-integral fixed point repeats a bounded number of times. Small tapes (≲ 2^17 cells) are inside the window where
   one stretch can finish from mid-tape, which is why hand-built halts exist there.
4. **Clean tapes.** With one free number n, the two countdowns become two 2-adic targets. The left side reads digits
   faster, so the right end's digits are decided in advance; each entry has a hard cap (its gap). The largest gap
   grows about 0.25 digits per digit of depth (12 by 43 digits), while a halt needs about one per digit.
5. **What escapes the lock.** Loops with k extra walls exist for every k (10 + 4k bits per pass, each with its own
   never-zero countdown), and with an extra wall a second pass type (the detour, irrational eigenvalues) lets runs mix
   pass types, which no single fixed point locks. Mixtures cost 16 to 18 bits per pass. None occurs in clean cycles
   to 40 digits (631 runs touch the one-extra-wall loop, all short, none with two stretches).
6. **The mark rules alone allow a halt at every scale.** One detour between two stretches of the one-extra-wall loop is
   enough: hand-built round starts with a gap and four walls (at 0.65%, 12.5%, 46% and 87% of the width) halt the
   machine on tapes of width about 2^56, 2^200 and 2^1000 and at every width 2^K for K = 16 to 400, through proven
   rules only, and on the bare transition table at 67,431 and 131,487 cells (see "Halting at every scale" below). The
   tapes pass the machine's one conserved count (1s plus state weight, mod 3). So no argument about the rules alone
   can prove non-halting. A stretch of that loop followed by a drop into the plain loop that keeps its progress is
   cheaper still (17/6 bits per meeting): three free numbers are enough, and such tapes halt at 2^120 and 2^200 cells,
   while the machine's runs live in a family of two (see "How many free numbers a halt needs").
7. **Status.** No halt below n = 2⁴⁹ (exhaustive). What a proof must still show is a property of the tapes the
   machine actually reaches: there, each run starts on a one-parameter family (a line in n), and every long run needs
   that line to pass unusually close, 2-adically, to fixed targets. Per pass, a line pays 6 binary digits of n plus one
   4-digit line-up (plain loop) or two (extra-wall loop); each gap is the count of trailing binary zeros of a small
   number Δ; the commonest route into the loop has a closed-form gap that never exceeds 8; and none of the 94
   extra-wall entries to 36 digits can complete a single pass. In counting terms: a halt costs at least 17/6 binary
   conditions per halving, a family of d free numbers supplies d per halving, every cycle runs inside the two-number
   family of GMM states (really on a one-number line in it), and the measured odds there fall 2.4 to 2.5 digits per
   halving at every width. The remaining statement is Collatz-like: heuristically overwhelming, with no proof method in
   sight.

## Additions of October 20 (details under "How many free numbers a halt needs")

1. **Threshold 17/6.** One plain stretch covers at most two thirds of the halvings and ends the run, so the first
   third must come from the extra-wall loop (14 conditions per 4 meetings), followed by a drop into the plain loop that
   keeps the progress (12 conditions). A halt needs more than 17/6 ≈ 2.83 free numbers' worth of digits: three, not
   four. Three-number tapes halt at 2^120 and 2^200 (P¹⁰UL¹⁸, P¹⁷UL³¹), where extra-wall-only words fail, and a small
   drop-route tape (129,963 cells) halts on the bare transition table at the predicted step.
2. **Odds per state.** The share of GMM states coming within 2^-h of the width falls about 2.4 to 2.5 binary digits
   per halving, independent of width, on the whole plane and on the machine's own line; the line is 20 to 30 times
   thinner.
3. **Cycles are chains of segments.** Each segment runs between returns to a GMM state and returns with odds about
   0.34. On the machine's line the r-th state lies on one of few lines at first (1, then 2, then dozens), and the
   per-segment odds of a close approach climb from 0 to the plane's level by the seventh to ninth segment. The first
   segment is proved never to come within 2^-1.62 of the width.
4. **Why verification is expensive.** A class's settle depth grows about 3.5 digits per return, and returns happen
   with odds 0.35: that gives the 1.53-fold growth of open classes per digit. It is not driven by closeness to the end.
5. **No halt below 2^61** (exhaustive, mark model): 36.93 billion settled classes and 120.94 billion direct runs; at
   least 1.8 × 10^52 steps (to 2^59: 15.74 billion classes, 2.9 × 10^50 steps) (disk engine to 2^51, depth-first engine to 2^59, identical on the shared levels).
6. **The two-marker reduction.** Every halt from a clean tape starts from a GMM state whose own segment halts. All 8.6
   billion GMM states up to width 262,143 were run through their segments: only (4, 13), 13 cells wide and never
   reached by the machine, halts. The plane's odds predict about one halting state below 2^16 and 0.014 beyond 2^18.
7. **The machine's sequence of clean tapes is typical.** Its residues mod 2^k follow the stationary law of a Markov
   chain built from random n (total variation at the noise level mod 16, 256, 1024); deep classes get at most about 3
   times their 2-adic share. For 29 of 32 residues the next clean tape is explicit (n + 3, 6, 9 or 12).
8. **Every route to 46 bits is excluded, at every width.** 759,918 prefixes from a GMM state into the plain loop (a C
   tree, `rtree.c`, matching the Python one exactly), with a safe pass requirement (an earlier one was a quarter pass
   too strict; corrected), leave 866,445 candidate states, none of which halts or lets marks touch; the 1,989 chains
   through the extra-wall loop leave none. From 34 bits on
   they include the way into the deepest run of every sampled segment that comes within 2^-8 of the width and uses
   the loop; the segments undecided at 46 bits are 2.0 × 10⁻⁷ of all GMM states.
9. **The extra-wall loop needs three free numbers 2-adically, not just by counting.** Each pass must keep three
   countdowns divisible by growing powers of 2; in a two-number family one fixed number must line up four more
   digits per pass, so each family has a hard cap. All 144 GMM-born entries within 30 bits allow at most one pass,
   decided by their position map alone; random two-number families never allowed two, random three-number families
   allowed all five-pass words. The same holds for k extra walls: 2 + k countdowns, unlimited passes
   exactly in families with at least 2 + k free numbers (k = 0 to 3 tested). Rarer entries do allow more: of 190,923 entry
   families built from all 30-bit routes, 81 allow two passes and 8 three, none four; explicit GMM states near 2^35
   and 2^42 run three extra-wall passes in a row and still come no closer than 13 to 15 halvings.

## The cycle that carries every long cascade (`../conc/`)

`../conc/conc.py` runs the mark model with every position kept as an affine form in some unknowns. Order tests use a
concrete or scaled-up point; each d (mod 4) test becomes a congruence on its form. `../conc/tree4.py` tracks the set
of unknowns still allowed as a coset of a lattice, so a test is either already decided or splits it in half (one bit).

**One cycle.** Every right-end run of 9 or more meetings in the classes settled by 33 digits spends at least 4 of its
meetings in the same 8-round loop of shapes, and all 256 classes with 13 or 14 meetings below 2^49 spend 7 to 9 there
(`../csearch/template.c`). Of the 168 runs of exactly 7, 55 never complete a pass. The loop is

    G W W W → G B W → G M B → G M W W → G M B → G M W W → G W W W → G B W → (repeat)

with 4 right-end meetings per pass. From the state `G, W a, W b, W c, end E` at its start:
- **Right condition** (`cyccost.py`, `cycbasis.py`): m loops need E − c ≡ 1 (mod 2^(4m+1)). This is the end
  countdown: each meeting merges and uses one trailing zero of E − c − 1.
- **Left condition**: a relation between b and the right end, with 2-adic limit b = 16E/21 + 62/49
  (`leftrat.py`). Plus a odd and E ≡ 0 (mod 4); a is otherwise free.
- **The loop is two exact countdowns.** Put R = E − c − 1 and L = 1029b + 1960E − 2744c − 4046. One pass maps the
  start state to a' = b/64 + c/16 + 3E/16 + 339/32, b' = b/64 + c/8 + 5E/8 + 629/32, c' = c/16 + 15E/16 + 369/16,
  E' = E + 24, and these give exactly R' = R/16 and L' = L/64. So the state completes m passes exactly when
  v2(R) ≥ 4m + 1 and v2(L) ≥ 6m + 1 (with a odd, E ≡ 0 mod 4). This predicts the number of passes for all 4,000
  planted states (`fuelfit3.py`) and every pass start in the real runs. (The cruder left quantity
  1029b − 784(c + 1) − 1302 is L − 40·49R; using it instead misses by one pass 19% of the time.)
- **Cost.** With a, b, c, E independent, m loops fix exactly 10m + 4 binary digits (2-adic Smith form of the forced
  system; solvable for every m checked up to 8).
- **Arbitrarily long runs exist from block states.** `cycsolve.py` solves the conditions for 12 loops and builds such
  a state at about 2^150; the integer model then runs the loop 12 times, 50 meetings in a row.

**Exact run probabilities from block states** (`tree_block.py`, checked by `../csearch/bsrun.c`). Start from
`G 1, B r, W R`, end E with r, R, E free (r even, R odd, E even) at a fixed geometry. Summing all branches exactly:
P(run ≥ 2..8) = 0.4375, 0.1328, 0.02539, 0.01074, 1.160e-3, 2.518e-4, 5.53e-5; 20 million random states give
0.4374, 0.1329, 0.02540, 0.01077, 1.158e-3, 2.53e-4, 5.56e-5. From 6 meetings on, the ratios between successive
P(run ≥ L) repeat 9.26, 4.61, 4.55, 5.27 exactly (checked to L = 25), whose product is 1024. So each further loop of 4
meetings costs exactly 10 bits, 2.5 bits per meeting, and no other way of continuing a run is cheaper.

**Clean tapes: two targets, one unknown.** On a clean tape every position is an affine function of the single number
n, so the two conditions become two 2-adic targets t_L and t_R for n.
- Along the loop the left clocks read about 1.5 new digits of n per meeting and the right end 1 per meeting, so the
  right end only ever reads digits the left has already fixed (`thread.py`: in the 14-meeting run of
  n = 363,165,946,702 every right-end test inside the loop is decided in advance, and 6 of the 14 tests per loop read
  new digits).
- So once the left side is satisfied, whether the right end keeps merging is already settled. The run lasts while n
  agrees with both targets.
- **Each entry has a hard cap.** `tree1d.py` fixes the digits that reach a run's first meeting and then sums over
  every continuation, up to 40 to 45 further digits. For all 100 entry classes tried, the run has a largest possible
  length, reached by exactly one thread of digits: no choice of further digits goes past it. For 93 of them the cap is
  the run actually seen; 7 allow 1 to 4 meetings more. (`capscan.py`)
- **All 256 runs of 13 or 14 meetings below 2^49 follow one template** (two variants): they enter the loop the same
  way, complete one or two passes, and leave when the right-end countdown runs out of trailing zeros, with 4 or 5
  meetings on the way out. At the first pass start they all have the same fuels: v2(1029b − 784E − 1302) = 11 and
  v2(E − c − 1) = 8 (template with 13), or 10 and 7 (with 14).
- **The gap of a line.** On a clean tape (or a residue class of them) R = λ_R·N + κ_R and L = λ_L·N + κ_L are affine
  in the one unknown, so Δ = λ_R·κ_L − λ_L·κ_R is fixed for the whole family, and λ_R·L − λ_L·R = Δ for every member.
  Put G_L = v2(Δ) − v2(λ_R) and G_R = v2(Δ) − v2(λ_L) (they do not depend on how the family is parametrised). Then
  v2(L) ≤ G_L or v2(R) ≤ G_R, so **no member completes more than max((G_L − 1)/6, (G_R − 1)/4) passes**, whatever
  its higher digits. G_R is v2 of R at the left target, and G_L is v2 of L at the right target. After a pass both gaps
  drop by exactly 6 and 4.
- For all 245 runs of 13 meetings, (G_L, G_R) = (7, 8) at the first pass start; for the 9 runs of 14, (4, 7). Their
  left fuel varies (14 to 26, halving in frequency with each extra digit, as fresh digits should), but the right fuel
  is pinned at G_R: that is why they all stop at the same place. (`delta.py`, `../csearch/gaps.c`)
- In the language of the 4-variable state: a clean tape's entry states form a line, and the loop needs a point on a
  codimension-2 target. A line generically misses it; the gaps measure its closest approach.

**The loop cannot run long on any tape** (exact). L₁ = L/7 = 147b + 280E − 392c − 578 is an integer, and every term
but the last is a multiple of 7, so L₁ ≡ 3 (mod 7): **L₁ is never 0**. Each pass divides L₁ by 64 (checked
symbolically, `L1' = L1/64`), and it must stay an integer, so a loop episode makes at most log₆₄|L₁| passes. L₁ is
linear in b and c over 0 ≤ b ≤ c ≤ E, so its extremes are at the corners: 280E, −112E and 35E. Hence |L₁| ≤ 280E and
**at most (log₂E + 7.2)/6 passes** (at real pass starts |L₁| < 2^5.9·E: `../csearch/lsize.c`). Each pass divides R by 16, so one episode can bring
the right end at most a factor (819E)^(2/3) closer: about two thirds of the halvings a halt needs.

**Leaving the loop, exhaustively** (`exit1.py`). Start from a pass-start state `G, W a, W b, W c`, end E with every
position free (b even, c odd, E even; a either parity) and follow every branch of one pass with no cut on bits. Either
the pass completes, which has probability exactly 2⁻¹⁰, and the state is again a pass-start state; or the run ends at
most 8 meetings after the pass start, without ever returning to 4 consecutive loop rounds. The search is finite (356
exits, no path reaches 80 bits) and gives the same tree for five different geometries. By induction, **a run that
reaches the loop makes 4k + r meetings from there, with r ≤ 8, k ≤ log₆₄(280E), and it never re-enters the loop.**
(Geometry independence was first only checked; it is now proved by the chain lemma under "The tree does not depend on where the marker sits": in the gap coordinates a, b − a, c − b, E − c the starting marks form a chain, every new position is the midpoint of two neighbours plus a constant, so every comparison is a nonnegative combination of the gaps and has the same sign for every geometry with large gaps.)

**One fixed point, seen two ways.** The pass map is affine with linear part dividing R by 16 and L₁ by 64, so it has
a single fixed point, R = L₁ = 0 (b = 16E/21 + 62/49, c = E − 1, up to the slowly moving E). Over the reals the map
contracts toward it: after a few passes b/E → 16/21 and c/E → 1 on every tape, so c − b stays near 5E/21. Over the
2-adics it expands away from it: staying in the loop needs the state ever closer to the fixed point. L₁ is the
integer displacement that is both: it shrinks 64-fold per pass as a number and must gain 6 trailing zeros per pass.
That is the whole reason the loop is short.

**The next run starts far from the end** (`exit_break.py`). In the exhaustive exit search, the meeting that breaks
the run has distance d = Σ β_k t_k + const with all β_k ≥ 0 on the cone generators (t₃ = c − b, t₄ = E − c), and
every one has β₃ ≥ 1/8. With c − b near 5E/21 after a pass, d ≥ about E/34: the next run starts within about 5
halvings of the full width, matching the measured 4.

**Lead-ins, exhaustively, and where that stops** (`leadin_ex.py`, `closure.py`). Every run starts at the meeting
that broke the previous one, so run-start states are the round-start states of final rounds, plus the clean tape.
From a run-start state with every position free (end marker tied to the end), the exhaustive search with no bit cut:
- from the clean tape G M: the first run ends after 1 meeting and the next starts from G M M;
- from G M M: at most 4 meetings, never reaching the loop; next runs start from G B, G B M, G M M or G M M M;
  (the whole first segment of a clean tape, followed symbolically in the one variable N = 2n + 6 through its run
  breaks, `firstseg_sym.py`: for every even n it ends within a few rounds, 81% at the next clean tape and 19% at a new
  GMM state, in 5 paths and no cut; so no clean tape enters the loop in its first segment, and the machine's loop
  entries all come from later segments, whose GMM states lie on lines of other slopes);
- from G B, G B M and G M M M: G W W W within 3 meetings, or the run ends within 6; from G W M M, at most 1;
- every one of these searches is finite and all order comparisons are forced (geometry-independent).
Iterating this to a closed set of shapes fails at G M B: with fully independent positions it reaches a variant of
the loop with one extra wall (G W W W W, G B W W, G M B W, ...), and that search does not terminate within 30 bits.
The variant is real but rare: none in 20 million clean cycles (G M W W W and G M B W once each, inside short runs),
three hits in 10^8 random G M B states near one geometry (`../csearch/extfind2.c`).

**The extended loop has the same obstruction** (`extpass.py`). One pass of `G W W W W → G B W W → G W W W W → G B W W →
G M B W → G M W W W → G M B W → G M W W W` from walls a < b < c < d and end E makes 18 tests and fixes exactly 14 bits
per pass (forced repetition, 5 passes checked), so it is rarer than the plain loop (10 bits). Its pass map is
a' = b/64 + c/64 + 271/64, b' = b/64 + 5c/64 + 3d/16 + E/4 + 899/64, c' = c/16 + d/4 + 11E/16 + 179/8,
d' = d/16 + 15E/16 + 369/16, E' = E + 24, with eigenvalues 1, 1/16 (twice, a Jordan block), 1/64 and 0. The right
countdown is E − d − 1 (÷16), and the left countdown is
L₂ = −441b + 735c − 2156d + 1652E − 179 (÷64). Again every variable coefficient is a multiple of 7 and the constant
is 3 mod 7, so **L₂ is never 0** and the extended loop also makes at most log₆₄|L₂| ≤ log₆₄(4984E) passes.
The 1/64 direction's fixed point has denominator 63 = 7·9 in both loops; the 7 never cancels.

**A whole family of loops, one lock** (`ext2.py`, `extk_map.py`, `extk_forced.py`). The loop also runs with k extra
walls near the end, for every k tried. From generic states with the real geometry the exact probability of one pass
is 2⁻¹⁴ (k = 1) and 2⁻¹⁸ (k = 2). Forcing the outcome pattern [2]^(5+2k) [0 0] [2]^(2+k) [0 0] [2]^(3+k) (read off k = 0,
1, 2), the pass runs for k up to 16, and forced repetition fixes exactly 10 + 4k bits per pass (checked for 3 passes,
k ≤ 8). The right walls are smoothed by the binomial kernel (1, 4, 6, 4, 1)/16 each pass, one factor 1/2 per meeting.
For every k ≤ 16 the 1/64 left countdown has all variable coefficients divisible by 7 and a constant that is not,
so **it is never 0, and every loop in the family makes at most log₆₄|L| passes**.
- **The general pass map** (`loopfamily.py`, read off the forced runs for k ≤ 7 and reproducing the simulated
  countdowns exactly): with walls w₀ = a, w₁ = b, w₂ … w_{k+2} and end E,
  a' = (w₁ + w₂)/64 + 271/64; b' = (w₁ + 5w₂ + 12w₃ + 12w₄ + 4w₅)/64 + 895/64 (915/64 for k = 0, 899/64 for k = 1);
  w_j' = (w_j + 4w_{j+1} + 6w_{j+2} + 4w_{j+3} + w_{j+4})/16 + 22, plus 1/16, 6/16, 17/16 for the last three walls;
  E' = E + 24; positions past the last wall count as E. The map is triangular, so the countdown follows by forward
  substitution.
- With the sign normalised, the countdown's constant is ≡ 6·3^k (mod 7) and its coefficients ≡ 0 for **every
  k ≤ 2500**, so no loop of this family can ever sit at its fixed point. The interior coefficients grow by the root
  2 + √2 of 4(r + 1)⁴ = r⁴, about 3.41 per wall. The
coefficients grow about 3.4-fold per wall (the first is 21·(−3)^k·7), so |L| < C_k·E with log₂C_k ≈ 1.8k + 7.

**Gaps grow slowly with depth** (`../csearch/nrefgap.c`, every settled class to 40 digits; `../csearch/gaps.c`,
10^9 random n near 10^13). The largest (G_L, G_R) over all pass starts: (5, 7) by 23 digits, (7, 8) by 31, (8, 9)
by 35, (10, 11) by 36, (11, 11) by 40, (10, 12) by 43 (and still 12 at 44); the random sample's largest is (10, 11). Weighted by density, pass starts
with G_R = 8 have 8.2 × 10⁻⁸ of all n and G_R = 9 only 1.5 × 10⁻¹⁰. So there is no fixed cap: the closest approach of
entry lines to the target improves as more lines appear, at roughly 0.3 to 0.4 digits of gap per digit of depth.

**A halt needs one long run.** (`../csearch/endseq.c`, `runstart.c`, `runparts.c`)
- After every run break the end distance resets: over 29 million run starts (n near 10^12) the first meeting of a
  run is never more than 3.6 halvings from the full tape width. Closest approach = start (≤ 3.6) + run length.
  Whatever the previous run reached, the next one starts within about 4 halvings (`runchain.c`: after runs ending at
  5 to 10 halvings the next starts at ≤ 3.9; after the 13- and 14-meeting runs, at 1.0). This is typical, not a law:
  a staircase of short runs can push run starts to 5.65 halvings (October 21, under "How late a run can enter the
  loop"), and its own map stops it at a fixed fraction of the width.
- Every run is a short prefix, at most one loop episode, and a short exit. Over 146.6 million runs (10^8 n near
  10^12), none enters the loop twice and none has more than 6 meetings outside its loop stretch (in the classes to
  33 digits, at most 2 before the loop, 5 after, or 7 with no loop at all). The exact branching from block states
  agrees: no path to 60 bits re-enters the loop.
- **Conditional bound.** If run starts stay within c halvings of the width, runs have at most C meetings outside a
  single loop episode, and the loop bound above holds, then the closest approach is at most
  c + C + 7 + (2/3)(log₂W + 7.2) halvings, while a halt needs about log₂W. With c = 4 and C = 7 (both measured) that
  rules out a halt once log₂W > about 68; the exhaustive check reaches log₂W ≈ 50. The three structural claims are
  measured, not proved.

**How late a run can enter the loop, and the exact end of the loop: the lock now sits 12 digits inside the exhaustive
range** (October 21, sharpened October 22;
`../csearch/runshape.c`, the depth-first engine's model with a probe at every loop entry). The conditional bound above
adds worst cases. Done per run it is sharper. Take a run's first pass start in the right phase (a G W W W followed by
G B W and G M B; the other G W W W of each pass, followed by G B W and G W W W, is where the countdowns are not exact),
and put s = log₂(W/R) and λ = log₂(|L₁|/W) there, W the width.
- *Proved, given the exit search:* if the run halts, then log₂W ≤ σ + 24, where σ = 3s + 2λ. Reason: the first
  meeting after a pass start has D = d + 2 = R exactly, every meeting has D' ≥ D/2 (D/2 for a merge, D/2 + 5 for a
  swap), and a halt needs D ≤ 4; at most 8 meetings follow the last pass start, so R there is at most 2⁹ and
  R ≤ 2^(4k+9) at the first of k + 1 pass starts. Completing k passes needs v2(L₁) ≥ 6k + 1, and L₁/64^k is then an
  even number ≡ 3 (mod 7), so |L₁| ≥ 4·64^k. Eliminating k gives the bound (k = 0 gives log₂W ≤ σ + 23.8).
- **Sharpened by the exact end of the loop: log₂W ≤ σ + 6.38** (October 22; `../conc/endsym.py`, `endL.py`,
  `endsym_small.py`, outputs `endsym_g*.txt`, `endsym_hi*.txt`, `endsmall_*.txt`; cross-checked on the stepper's
  engine by `../stepper/endcheck.js`). A pass divides R by 16 and L₁ by 64 exactly, so 3 log₂R − 2 log₂|L₁| is the
  same at every pass start of an episode, and log₂W = σ + 3 log₂R − 2 log₂|L₁| holds at each of them (up to the 24
  cells a pass adds to W), in particular at the last. What limits a halt is therefore the set of pass-start states
  from which the run can reach d ≤ 2 without starting another pass. `endsym.py` searches that set exactly: start
  G 1, W a, W b, W c with R = E − c − 1 held fixed and a, b, E free; follow the stepper engine's rules with all of its
  checks for uncovered cases; split on every low-bit test the class does not decide, with no cut; stop at d ≤ 2, at
  a packet reaching a block, at a break of the end chain with the end far away, at a new phase-0 pass start, or when
  the first two rounds are not G B W, G M B. Result for every even R from 2 to 4096, identical in five geometries and
  unchanged with a or b − a as small as 3: the run reaches d ≤ 2 only from R = 2, 4, 8, 16, 24, 32, 48, 64 and 176
  (density 1, 1, 2⁻³, 2⁻⁵, 2⁻⁷, 2⁻⁶, 2⁻⁸, 2⁻⁷, 2⁻⁸ of the start class), never by a packet reaching a block first,
  and with no uncovered case anywhere. **Verified geometry-free** (October 23, `../csearch/gx2.c` mode `endgame`,
  output `gxend_g0.txt`): the C explorer, a separate implementation that decides every order comparison on the cone
  of large gaps and counts any it cannot, finds the same nine closing R with the same densities, each closing coset
  inside the L₁ class below, no cut (80 bits), no invalid or halted path, and **none of its 6,743,075 comparisons
  depended on the geometry**; the closing cosets are byte-identical for three geometries. So the table holds for
  every pass-start state with large gaps, not only the sampled ones. With the second and third walls a fixed small
  distance apart (3 to 41 cells, the contact regime): at 3 the marks overlap, at 5 a packet meets a marker directly
  after a gap (a proven rule the mark rules do not build), and from 7 on the closing set is the standard one when
  c − b ≡ 1 (mod 4) and only {2, 4} when c − b ≡ 3 (mod 4); never anything new. The same explorer started
  from a G W W W of either phase (no phase condition; 1.3 × 10⁷ comparisons, none geometry-dependent): the run makes
  **at most 8 end meetings before it breaks far from the end, closes, or arrives at a phase-0 pass start**, at most 7
  before a close, and closes only from R ∈ {2, 4, 6, 8, 16, 22, 24, 32, 48, 64, 176} (6 and 22 only from the other
  phase, which a phase-0 start reaches with R/4 or so). So every halting run has a phase-0 pass start, or at most 8
  meetings after its first loop state; the ceiling argument below uses this. A pass happens only from R ≡ 0 (mod 64), to R/16. Each closing class fixes L₁
  modulo 7·2^j:

  | R | L₁ must be | smallest \|L₁\| | 3 log₂R − 2 log₂\|L₁\| | rounds to the close |
  |---|---|---|---|---|
  | 2, 4 | 10 mod 14 | 4 | −1.00, 2.00 | 2 |
  | 8 | 24 mod 56 | 24 | −0.17 | 3 |
  | 16 | 192 mod 224 | 32 | 2.00 | 5 |
  | 24 | 416 mod 448 | 32 | 3.75 | 9 |
  | 32 | 192 mod 448 | 192 | −0.17 | 8 |
  | 48, 64 | 640 mod 896 | 256 | 0.75, 2.00 | 11, 10 |
  | 176 | 640 mod 896 | 256 | 6.38 | 13 |

  A pass itself (R ≡ 0 mod 64 and back to a phase-0 pass start) is the coset L₁ ≡ 1536 (mod 1792), i.e. **L₁ ≡ 0
  (mod 256)** on top of L₁ ≡ 3 (mod 7), independent of R (checked at R = 128 to 2048): two more trailing zeros than
  the bare L₁/64, which is why a pass costs 2⁻⁸ of the valid class and why the classes above have L₁ divisible by
  2, 8, 32, 32, 64, 128, 128, 128 for R = 2 to 176: about one trailing zero per halving in the endgame against 1.5
  inside the loop.
  The largest is 6.38, so **a run halts through the plain loop only if log₂W ≤ σ + 6.38**, 17.4 tighter than the
  bound above: closing needs both a small R (at most 176, not 2⁹) and an L₁ divisible by a power of 2 that grows
  with R, so it is never small. The R = 176 close is G B W, G M B, G M W W, G M B, G M W W, G W W W, G B W, then
  G M W, G W W, G B, G W W, G B: seven rounds of the loop and two of the G B, G W W piece. The hand-built halting tapes
  below fit the table: the 72-cell tape (R = 32, L₁ = 8704), the 16,000-cell tape (one pass to R = 32, L₁ = −9216)
  and the 17,652-cell tape (two passes to R = 32, L₁ = 640) all have L₁ ≡ 192 (mod 448) there; for the last,
  σ = 17.75 at its first pass start and log₂W = 14.11 = σ − 3.64. On the engine, 20,000
  random states at R = 176 close 83 times (0.41%, against 2⁻⁸ = 0.39%), and all 83 have L₁ ≡ 640 (mod 896).
- *The extra-wall loop has no such finite endgame* (`../conc/endsym2.py`, `endsym2_free0.txt`). The same search from
  an extra-wall pass start (G 1, W a, W b, W c, W d; R = E − d − 1 fixed; a, b, c, E free; stopping at any completed
  P or Q pass, at a drop into a plain phase-0 pass start, or at a far break) finds closes from R as large as the scan
  reaches: 39 closing values up to R = 2048 for R ≤ 2200, in no uncovered case. The large ones go through pass
  variants that are neither P nor Q (for example a 10-round detour with G M M B, G M M W W, G M W W W inserted, then a
  phase-shifted P), each again dividing R by 16, before the close. So the extra-wall family can keep dividing R through
  ever new pass words, which is the same fact as "mixtures have no lock" seen from the end; the plain loop, whose exit
  never returns, is the only loop with a finite endgame.
- **How late extra-wall pieces can make the plain entry: no ceiling, a fixed price** (October 22;
  `../csearch/gx2.c`, mode `xlead`, outputs `../csearch/xlead39*.txt`; `../stepper/xcheck.js`). From an extra-wall
  state G 1, W a, W b, W c, W d with every position free (the one parity class that is a real tape), every branch of
  the same run is followed until it reaches a phase-0 plain pass start, breaks, or hits the cut. Every end meeting
  halves the end distance, so at the plain entry R₁ = t₅/2^j + const exactly (t₅ = E − d), that is s = s_X + j, where
  s_X is the extra-wall state's own lateness and j the number of end meetings in between; σ = 3(s_X + j) + 2λ.
  The tree is the same for five geometries (s_X from 2 to 8, no geometry-dependent comparison among 1.5 × 10⁷), and to
  the 56-bit cut:

  | j at least | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 |
  |---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
  | probability | 2.4e-3 | 4.1e-4 | 1.1e-4 | 1.5e-5 | 7.8e-7 | 1.1e-7 | 1.0e-8 | 1.4e-9 | 7.4e-11 | 1.1e-11 | 9.7e-13 | 1.4e-13 | 6.7e-15 | 8.1e-16 | 1.4e-17 |

  (48-bit values agree to J = 12.) That is about 3.4 binary digits per meeting before the entry (J = 4 to 14), the
  same price as the extra-wall runs' 3.35 above, and λ at these entries is at most 6.8. The paths use completed P or Q
  passes (0 to 3 of them) and pass variants in any phase; no length is excluded, so σ has no ceiling: from the 39.17
  lead-in's own extra-wall state (s_X = 6.87) the search finds plain entries up to σ = 75.5 at 56 bits, and σ ≥ 54
  with probability 6 × 10⁻⁹. Two of the found states, rebuilt as integers and run on the stepper engine, reach their
  plain entries with σ = 63.194 and 62.160 exactly as predicted. The two-extra-wall loop gives the same picture
  (P(j ≥ 8) = 5.2 × 10⁻⁹, P(j ≥ 12) = 2.9 × 10⁻¹³, λ ≤ 6.81, 52-bit cut).
- *On the machine's own segments:* the chains from GMM states through the extra-wall loop found within 46 digits
  (`../chains46_summary.txt`) reach plain entries up to H = 18.9 halvings below the width (measure 2.8 × 10⁻¹⁴), so
  σ ≈ 66 > 53.6 does occur at that depth. All of them were run through the chain exclusion and none halts. The ordinary
  routes' entry lateness falls about 2.7 binary digits per halving (H ≥ 4: 2.0 × 10⁻⁴ of GMM states; H ≥ 8:
  2.0 × 10⁻⁷; H ≥ 11: 3.6 × 10⁻¹⁰, beyond which the 46-bit cut truncates).
- *What the lock and these prices give together (heuristic).* A halt at width 2^k through the plain loop needs
  s ≥ (k − 6.38 − 2λ)/3 at entry. Halvings before the entry cost about 3.4 binary digits each beyond the few a run
  gets for free (run start plus at most 3 meetings from the main shapes, about 9), halvings inside the plain loop
  2.5. The cheapest split puts as little as the lock allows before the entry. On the README's own count (2^b/8.97 clean
  tapes in [2^b, 2^(b+1)), 2.27 × 10⁻¹² of them at 14 halvings, 2.5 digits per halving beyond) and with this surcharge
  of 0.9 digit for each pre-entry halving beyond 9 (λ = 6.8), the expected number of halts beyond 2^59 is about 2 × 10⁻³⁰
  (without the surcharge, 3 × 10⁻²⁹; the earlier figure beyond 2^55 was 2 × 10⁻²⁷). So the lock does not close the
  gap by itself; it makes about a third of the halvings a halt needs cost 3.4 digits instead of 2.5.
- *Measured:* over 3 × 10⁸ random GMM states of width about 2^40 and 2 × 10⁸ of width about 2^52, the 1,035,751 loop
  entries have σ at most 26.9 and 27.3 (above 24 only 17 times; most are 15 to 21; the same distribution at both
  widths); over the smallest members of the 11,878 classes of the exhaustive run
  that come within 2^-12 (the machine's own deepest cycles below 2^57), the 12,352 loop entries have σ at most 27.3;
  and over the 12,382 record-adjacent cycles beyond it (members of the luckiest lines), the 19,731 loop entries have σ
  at most 32.2. For such entries the first bound forbids a halt above width 2^51.3, 2^51.3 and 2^56.2 respectively,
  and the sharp one above width 2^33.7, 2^33.7 and 2^38.6.
  The run starts later than 4.4 halvings in these samples come from two patterns only: the staircase below, and
  shapes of the extra-wall loop (G W W W W, G B W W, G M W W W, G M B W).
- *The latest entries come from a staircase.* In the 32.2 case (n = 125,135,531,668,101,955,698,597,374, a cycle at
  87 digits) a run of 7-round periods G W W W, G B W, G W W W, G B W, G M W M M M, G W W M M M, G B M M M repeats,
  each period a few short runs, and the run starts drift from 4.1 to 5.65 halvings below the width: later than the
  3.6 seen in the 29 million random run starts above, and the reason that bound is only typical. The period is an
  affine map (b, c ↦ 11b/64 + 21c/64 + 3W/8 + 867/64, 3b/64 + 9c/64 + 13W/16 + 1191/64, read off by finite
  differences on the traced state), with eigenvalues 9/32 and 1/32. Over the reals it converges: the middle wall
  to 0.154 W from the end and the last wall to 0.0084 W, 6.89 halvings, where a loop entry has s = 7.89, λ = 4.63 and
  σ = 32.93 (read off one period, the map predicts the next traced period exactly). So a staircase approaches the end only up to a
  fixed fraction, like the plain loop's b/E → 16/21. 2-adically 1/32 and 9/32 are both of size 2^5, so staying on it
  should cost about 10 binary digits per period, as a pass of the plain loop does (1/16 and 1/64), while gaining
  nothing toward the end.
- *Exits from a staircase at its limit are later than its own* (`../runs/genplat.py`, runshape F mode). States placed
  at each plateau pattern's fixed point (the census below, 118 patterns) with random low digits, 20,000 per pattern,
  then 2,000,000 each for the two latest: only two patterns ever give σ above 31. At the staircase's limit 3.1% of the
  states start a run 7.89 halvings below the width (half the last wall's distance) and reach a pass start one meeting
  later, at s = 8.89, λ = 4.88, σ = 36.45; a few rarer exits give 36.23 and 35.79. The 15-round plateau's limit gives
  33.05. The one later entry found, 39.17 (once in 2,000,000), comes from the 15-round plateau through a full
  extra-wall pass and a drop into the plain loop. So without the extra-wall loop the latest entry found is 36.45, from
  a staircase run to convergence, which takes several periods. Each costs about 12 binary digits: of 1,000,000 states
  at the staircase's limit with random low digits, 160 follow it for one full period (7 rounds) and 4 for 12 rounds.
  Since the geometry closes in on the limit by 9/32 per period, an exit at σ ≥ 36 needs about 3 periods first, so
  about 35 digits on top of everything else.
- *Exits from the plateau limits, exactly* (October 24; `../csearch/gx3.c` mode `plat`, `../runs/platexact2.py`,
  `platexact_entries40.txt`). The sampled statement above (20,000 to 2,000,000 random states per pattern) is replaced
  by the exact tree: from each of the 118 plateau limits (the fixed-point geometry, with the state's parity class
  free), every branch of the run is followed to 40 binary digits until it breaks, reaches a clean tape, or makes a
  phase-0 plain pass start, and σ is read at every pass start. 108 of the 118 trees are complete within 40 digits.
  Without any round of the extra-wall loop on the way, the latest entry from any plateau limit is the staircase's
  σ = 36.45 (s = 8.89, λ = 4.88), on exactly 1/32 of its class (the sampling's 3.1%), then the 15-round plateau's 33.05,
  also on 1/32, and the staircase's 32.93 on 2⁻¹³: nothing else above 27.15. So "36.45 without the extra-wall loop" is
  exact, not sampled. With extra-wall rounds on the way (pieces of the loop, mostly not whole passes) the plateau
  limits' exits reach σ = 47.33 (2⁻³⁹, from G B M M M M with the end marker tied) and 47.13, 46.79, 45.3: later than
  anything the sampling saw (39.17), because they sit at measures the samples could not resolve, and in line with the
  route tree, whose deep extra-wall lead-ins reach 52.86 by 62 digits. Summed over the 118 patterns, P(σ ≥ 40) is
  2.0 × 10⁻⁹ and P(σ ≥ 44) is 1.3 × 10⁻¹⁰, all of it through extra-wall rounds.
- *Consequence (revised October 22 with the sharp bound):* every loop entry seen in the machine's own runs allows a
  halt only at widths below 2^38.6. The latest entries any mechanism has produced, a staircase run to its limit
  followed by its commonest exit (36.45) and a lead-in through a full extra-wall pass (39.17), allow halts only below
  2^42.8 and 2^45.6. The exhaustive check to n < 2^59 covers widths below 2^60, so **a halt beyond it through the plain
  loop needs σ ≥ 53.6, about 14 more than anything found** (σ ≥ 51.6 already with the 2^57 check). Since |L₁| ≤ 280E,
  σ ≤ 3s + 16.3, so such a run must enter the loop at least 12.4 halvings below the width (13.9 with the measured
  |L₁| < 2^5.9·E), against 8.89 for the
  latest staircase exit and 7.89 for the latest plateau. The difference has to come from extra-wall passes (about 4
  meetings and 13 to 14 binary digits each), and the route exclusion has already removed every extra-wall chain
  decided within 46 digits. A halt that never uses the plain loop is outside this lock; the hand-built halting tapes
  at every scale are of that kind, and on generic states such runs cost about 3.35 binary digits per meeting.
- *The first version of this consequence* (σ + 24) left the staircase's 36.45 and the 39.17 lead-in inside the lock's
  reach beyond 2^57; the exact endgame removes both with 12 to 15 binary digits to spare.

**Every repeating pattern the runs use, and where each one goes** (October 21; `../csearch/runshape.c` with PAT=1,
`patmap.py`, outputs `../runs/pat_*.txt`, `../runs/patmap_all.txt`). Every run in 12,382 record-adjacent cycles, the
11,878 deepest classes of the exhaustive run, 180,000 members of random machine lines and 4 × 10⁸ random GMM states
(widths 2^40 and 2^52) was scanned for any sequence of round shapes repeated at least twice in a row (periods 1 to 16).
That gives 125 distinct patterns, of periods 2 to 15. For each, one period's affine map was read off by finite
differences on a recorded instance (the replay matched the recorded shapes in all 125), with its eigenvalues and its
fixed point over the reals, positions taken as fractions of the width as W → ∞.
- *Patterns that carry a mark onto the end:* the plain loop (8 rounds, eigenvalues 1/16 and 1/64, up to 6 passes in
  these samples) and six two-round halves of the plain and extra-wall loops (G B, G W W; G B W, G W W W; G M B, G M W W;
  G M M B, G M M W W; G M B W, G M W W W; G B W W, G W W W W), none repeated more than 3 times. The full extra-wall loop
  never ran two whole passes in these samples. The commonest piece, G B then G W W (2 × 10⁷ times in the 2^52 sample),
  would halve the end distance every two rounds if it kept going, but it cannot: of 200,000 valid G B tapes, the
  quarter with W ≡ 3 and r ≡ 2 (mod 4) all go G W W, G B and then break, and the rest never start it.
- *Everything else parks short of the end:* the other 118 patterns converge to a fixed point a fixed fraction of the
  width before the end, between 0.11 and 7.89 halvings. The latest are the staircase (9/32 and 1/32; 7.89), a
  15-round pattern built from loop pieces and a marker (7.29) and an 11-round one (5.17). The longest-running is
  G M M, G M M M, G W M M (eigenvalue 1/8), up to 11 repeats, parked at 2/7 of the width from the end.
- So in everything sampled, the only repetitions that can bring the right end toward a halt are the loops whose
  passes are locked by a never-zero countdown. Every other repetition settles at a fixed lateness. A pattern can only
  make progress if its real fixed point puts a mark on the end, and none of the 118 does; how late the run that
  follows a plateau can enter the loop is a separate question, answered above (36.45 at most without the extra-wall
  loop, in the samples).

**The C explorer, and a crack in the lock** (`../csearch/gx.c`). The free-position search is ported to C (affine
forms with 128-bit numerators, the coset kept in Hermite form, order decided on the cone with a counted fallback). It
reproduces the Python exit search exactly (356 exits, P(pass) = 2⁻¹⁰, longest 8 meetings) in 25 ms, matches the
integer model on 300 random states, and finds all 20 second-round shapes that random integer states show.
- **Exits of the one-extra-wall loop** (k = 1, real geometry, 64-bit cut, no geometry-dependent comparison among
  3.7 × 10⁷): P(pass) = 2⁻¹⁴ exactly, but unlike the plain loop the run can leave and come back. A pass whose left
  clock runs two rounds longer (an extra G M B W, G M W W W pair) acts as a detour after which the loop pattern
  resumes, and the run can also drop the extra wall and continue in the plain loop. Runs with 2, 3 and 4 loop
  stretches occur (probabilities 1.7 × 10⁻⁴, ≥ 5.7 × 10⁻¹², ≥ 8.8 × 10⁻¹⁷ to the cut).
- **Each new stretch starts with a fresh left countdown.** Along such a chain the right countdown keeps shrinking
  (log₂(R/E) = −2.6, −3.6, −7.6, −10.6, −11.6 at successive loop states), but the left countdown of the new stretch is
  again about 2^5.5·E. So the lock bounds each periodic stretch, not a run made of several. Two or three stretches
  would be enough, in principle, to carry the right end all the way.
- **They are not cheaper.** From a generic k = 1 state the exact P(run ≥ L) falls by 1028 to 1029 per 4 meetings
  for L = 10 to 18, the same 2¹⁰ as the plain loop: the long tail there is runs that drop into the plain loop.
  Runs that never use the plain loop (pure k = 1 stretches and detours) fall by 2^13.3 to 2^13.5 per 4 meetings,
  about 3.35 bits per meeting. So the mechanisms the lock does not cover are the expensive ones. In clean cycles the one-extra-wall states have density about
  4 × 10⁻⁸. Over every class settled within 40 digits (`../csearch/nrefchain.c`), 258,146 runs contain a loop
  stretch; 631 of them use the one-extra-wall loop (runs of at most 6 meetings), and **no run contains two
  stretches**.
- **Closure in C** (`gx closure 40`): with ties kept (end markers, constants, marks at a fixed offset from a neighbour)
  the set of run-start shapes still grows without end (132 shapes processed, up to 9 marks, e.g. G W M M M M M M M),
  because free positions let halving markers pile up. Across all of them: no halt, no geometry-dependent
  comparison, a loop state within at most 10 meetings or the run ends within 12 (to the 40-bit cut).

**The detour is a second pass type** (`detour.py`, outcomes read off the C explorer). For the one-extra-wall loop
there are two 8-round passes from the same state: P (standard: G B W W, G W W W W, G B W W, G M B W, G M W W W, G M B W,
G M W W W, G W W W W) and Q (G B W W, G M M W W, G M W W W, G M B W, G M W W W, G M B W, G M W W W, G W W W W). Both
divide the right countdown E − d − 1 by 16. Q's map is
a' = b/128 + 257/64, b' = 9b/128 + c/32 + d/8 + E/4 + 855/64, c' = b/16 + c/32 + 3d/16 + 11E/16 + 701/32,
d' = d/16 + 15E/16 + 369/16, E' = E + 24.
Its (b, c) block is (1/128)·[[9, 4], [8, 4]], with irrational eigenvalues (13 ± √153)/256, so Q has no dyadic left
countdown at all. Every word in P and Q tried (up to length 5) is 2-adically consistent; forced repetition fixes 16.2 to 18.5 bits per
pass (PP 16.5, QQ 18.5, PQ 17.5, PQPQ 16.2, PQQPQ 16.2), against 10 for the plain loop.
(October 27, `../lock/LOCK_NOTES.md`: Q does have a dyadic countdown, a quadratic one. The norm form D_Q of its two
eigenforms is an integer quadratic, never 0, divided by 4096 by every Q pass, so a Q stretch covers at most two thirds
of the halvings, like P. Every periodic P/Q word has such a lock, at most 4/5; aperiodic mixtures have none.)

**The general form of the lock.** For any periodic pattern whose pass map x ↦ Mx + t contracts (as real numbers) in
some directions, the fixed point x* = (I − M)⁻¹t is rational with a fixed denominator D. If x* is not an integer point,
then after m passes x_m − x* = Mᵐ(x₀ − x*) is a nonzero vector in (1/D)·Zⁿ that shrinks geometrically, so m is at most
about log(D·|x₀ − x*|)/log(1/ρ). The mod-7 statement for the plain loop is this with D's factor 7 (from 63 = 64 − 1).
A word w in several pass types has its own fixed point with its own denominator D_w, and those grow with the word, so
aperiodic mixtures of P and Q have no such bound. They exist only with extra walls, and they cost about 4 bits per
meeting.

**Tapes on which the machine does halt** (`plant_end.py`, `plant_far.py`, `buildtape.py`, `../csearch/tmrun.c`).
Planting the two countdowns by hand gives loop states that carry the right end all the way, and the real machine then
halts. The configurations are round starts (leftmost 1 at cell 0, gap at cells 1 to 3, head on cell 3 in state E,
stripes alternating, last 1 at cell E − 1); none is known to be reachable from the blank tape.
- **72 cells**: walls at 7, 30 and 39, tape `100010100101010101010101010101001010101001010101010101010101010101010101`.
  The end meetings run 30, 14, 6, 2, 0, and the machine halts after 10,302 steps (checked by two independent
  simulators): state D reads the first 1 of a 111 just left of the end.
- **16,000 cells**: walls at 2401, 6814, 15487 (R = 512, L₁ = −589,824 = −9·2¹⁶). For 17 rounds the machine matches the
  mark model exactly (every shape and width); the end meetings run 510, 254, …, 6, 2; it halts at step 759,437,834,
  again on a block next to the end. The mark model, which assumes no contacts, instead reaches a clean tape.
- **About 17,700 cells, starting mid-tape**: e.g. walls 2359, 9438, 9459 on a 17,652-cell tape, with the last wall 8192
  cells from the end. Three passes (meetings 8190, 4094, …, 2, 0) and the machine halts at step 1,258,643,838.
- **Every clean tape n < 5000, on the real machine** (`../csearch/tmclean.c`, no mark model): all 4,999 reach the next
  clean tape without halting (1.5 × 10¹¹ steps in all; largest jump 57). So the small tapes where hand-built states
  do halt are not reached from any clean tape in this range.
- **Random small configurations** (`../csearch/tmrandom.c`): 1.2 million random round starts (widths 20 to 400, one to
  four random marks where the stripes allow) on the real machine. 3,334 halt; 3,308 of them halt with the head exactly
  9 cells left of the last 1, the right-end signature above. The other 26 start with marks a few cells apart (e.g.
  M10 W18 W27 W34 on 45 cells, which halts after 1,749 steps once markers at 36 and 39 are one stripe cell apart):
  contacts of the kind the contact standard rules out on the machine's own tapes.
- **A necessary condition, checked exhaustively on small tapes** (`../csearch/haltcrit.c`): every loop-shaped round
  start G 1, W a, W b, W c with width 40 to 130 (423,775 states, valid parities, marks at least 5 apart), run on the
  real machine and in the mark model. The machine halts in 18,462 of them, and in every one the mark model's right-end
  run reaches a meeting distance d ≤ 2 (16,837) or the model meets a contact (1,625). Whenever the model's run
  stays above 2 and meets no contact, the machine reaches its next clean tape (348,924 states). Reaching d ≤ 2 is
  necessary, not sufficient: 28,919 such states still end cleanly.
- **Why only small tapes.** Reaching the end from distance R needs P = log₁₆R passes, hence |L₁| ≥ 64^P, and
  |L₁| ≤ 280E. So one loop episode can finish only from R ≲ (280E)^(2/3). On a 17,700-cell tape that is half the tape;
  from 2^17 cells on, the plain loop alone cannot start from mid-tape, and on the machine's own tapes (about 2^50 cells)
  it covers at most about two thirds of the halvings. This is the halting route the whole analysis is about,
  shown to be real.

**Halting at every scale** (`../conc/mixsolve.py`, `../conc/lattice.py`, `hybsim.py`, `hybcmp.py`, `hybval.py`).
The lock bounds one periodic stretch, and a detour starts a new one, so a hand-built state can chain two stretches.
- **Construction.** For a word in the passes P and Q of the one-extra-wall loop (state `G 1, W a, W b, W c, W d`,
  end E), the forced congruences of every round are solved as a coset of a lattice in (a, b, c, d, E), with the tape
  parities (walls odd, even, odd, even; E odd). LLL reduction and a nearest-plane search then give the integer point of
  the coset closest to a fixed geometry scaled to width 2^K. For P²⁴QP²⁴ at K = 200 the coset has index 2^694 and its
  reduced basis vectors are all shorter than 2^197, so the box of side 2^200 holds about 2^100 solutions. For P^m alone
  the longest basis vector grows by 6 bits per pass (the L₂ countdown) and passes the width at m = 36, as the lock says.
- **Checking on the machine.** `hybsim.py` runs the real machine from a round-start configuration of any width. It uses
  casesim's proven rules, with the exact pattern check before each one. Where no rule applies, it falls back to plain
  transitions accelerated by the three cycle lemmas (none of the runs below needed that). It agrees with direct
  simulation (`tmrun.c`) on 550 of 550 random small tapes (3 to 6 walls, widths 60 to 3000: same first clean tape, or
  same halting step), and reproduces the 72-cell example's 10,302 steps. `hybcmp.py` confirms that the machine and the
  mark model agree round by round until the halt.

| Width | Word | Unbroken run ending at d = 0 | Halting round | Steps to halt |
|---|---|---|---|---|
| 7.1 × 10¹⁶ (2^56) | P⁶QP⁶ | 53 meetings | 106 | 9.3 × 10³⁴ |
| 1.6 × 10⁶⁰ (2^200) | P²⁴QP²⁴ | 197 meetings | 394 | 1.8 × 10¹²² |
| 1.1 × 10³⁰¹ (2^1000) | P¹²⁴QP¹²⁴ | 997 meetings | 1994 | 4.2 × 10⁶⁰⁴ |

  (State files `mix56r.txt`, `mix200r.txt`, `mix1000r.txt`; the run's first meeting is at 0.127 of the width.)
- **Every width, and the raw machine** (`../conc/sweepK.py`, `sweepP.py`, `../csearch/tmfast.c`). With m =
  ⌊(K − 3.6)/4⌋ passes, the word P^a Q P^b (a + b + 1 = m), the end distance pinned to E − d − 1 = 2^(4m+1) exactly and
  E ≡ 3 (mod 6), the nearest coset point to the same geometry halts the machine for **every K from 16 to 400**
  (checked one by one through the proven rules; the halt comes in round 8m + 2). With the loop alone (P^m, same
  pinning) the coset's longest basis vector passes the width from K = 24 on: valid halting tapes come out at
  K = 20 to 23 and 27, and none from 28 to 48. Direct simulation of
  the bare transition table, with no rules or marks at all, on the K = 16 tape (walls 417, 3084, 32805, 59238, width
  67,431, word PQP) halts at step 15,940,135,477, and on the K = 17 tape (walls 835, 13908, 58589, 123294, width
  131,487) at step 61,437,118,279: exactly the steps the rule-level simulator gives.
- **They pass the machine's conserved count.** The number of 1s, plus 2 for state B and 1 for states C to F, never
  changes mod 3, and it is 0 on the blank tape (`../invsearch.py` checks every transition). At a round start with a
  gap and four walls the tape holds (E − 5)/2 ones and the head is in E, so a tape reached from blank needs
  E ≡ 3 (mod 6). The first versions of these tapes failed this (so they provably cannot be reached); adding E ≡ 0
  (mod 3) to the coset gives the tapes in the table, which pass it and halt the same way. A search over all counts of
  this kind that also weight a cell by its position modulo p (p ≤ 6) and the head by state and position, modulo 2, 3,
  5 and 7, finds no other conserved quantity. Widened (October 24, `../conc/invsearch3.py`): weights on every
  pattern of 3, 5 or 7 consecutive cells, position classes modulo p up to 8, head term by state and cell, modulo 2, 3,
  5, 7 and over the rationals (gauge terms removed by comparing values on padded test tapes): still **only the 1s
  count mod 3**. With head terms that also see the neighbours (`invsearch2.py`) the only additions are indicators of
  local patterns the machine never creates (D reading 1 with a 0 to its right; F on a 0 with a 1 to its left), one per
  position class, which are reachability facts, not constraints. So no conservation law of this kind can separate the
  halting configurations from the reachable ones beyond E ≡ 3 (mod 6), and for 3-wall pass starts the count gives
  W ≡ 2 (mod 6), which the closing cosets (2-adic conditions) do not conflict with.
  **At the mark level** (`../stepper/markinv.js`, October 24): conserved quantities of one round of the mark rules,
  linear in the counts of each mark type, their positions, squared positions, rank-weighted positions, the stripe
  lengths between adjacent marks of each type pair, the width and its square, modulo 3, 5, 7, 9, 11, 13, 21, 63, 2,
  4, 8, 16 and over the rationals, on 12,000 random valid round starts: the count invariant in its emergent form,
  **W + #G + #M − #W − #B ≡ 0 (mod 3)** at every round start, the width identity, the stripe parities (mod 2 and 4),
  and the trivial facts (one active gap; the last mark is never a gap). Nothing else. By hand: a position-weighted sum
  survives a swap or merge only modulo k with 3w ≡ 0 (mod k), and the gap-wall vanishing then forces w = 0, so only
  count-type invariants can exist at the round level; the modular locks of the loops are invariants of pass maps, not
  of rounds. And the clean-tape sequence is a single cycle modulo every 2^k through the residues ≡ 2 (mod 3), so no
  further residue-class invariant can exist at all; what remains of the "one free number" structure is 2-adic (the
  coherence of all marks with the width, and the small dyadic Δ at pass starts), not modular.
- **The countdown, pass by pass** (`mix200r_passes.json`, drawn on the page). Along the 2^200 run the extra-wall
  countdown L₂ = −441b + 735c − 2156d + 1652E − 179 falls from 2^205.8 by 6 binary digits per pass to 2^61.8, its
  trailing zeros running out exactly at the end of the first stretch. The detour resets it to 2^203.2, and the second
  stretch takes it down to 2^59.2 as the end distance reaches 0. Without the detour its size would hit 0 at meeting
  137, with the last wall still about 2^60 cells from the end.

  Every one ends the same way, with the same rules as the 72-cell example: the end meetings run …, 30, 14, 6, 2, 0,
  and in the last round BLOCK→wall, BLOCK→wall, BLOCK→blank leave the active gap directly after a 1 that ends the
  stripes (`…0 1 | 1 0 0 E>0 1 1`). The d = 0 meeting is a SWAP, which puts the end marker against that 1, so the
  tape reads `…0 1 1 1 0 0 0`: a block. The gap then wall-bounces to blank tape (GAP→blank end), and the packet it
  sends left is carried back to that block: PACKET→block, and the machine halts. The mark model (`conc.py`) does not
  see this contact and goes on to a clean tape.
- **What it shows.** At width 2^200 one stretch of either loop is limited to about 35 passes, while a halt needs about
  50. One detour splits the run into two stretches, each with its own countdown, which is enough at every scale.
  Gap-and-three-wall round starts cannot do this, because the plain loop's exit is exhaustive and never returns, so
  four walls is the smallest configuration of this kind. **Any proof of non-halting therefore has to use what is
  special about the tapes the machine reaches from blank.** The measured facts (mixtures absent in clean cycles to
  40 digits, gaps growing about 0.3 digits per digit) are facts about those tapes, not about the rules.
- A mixed state is also easy to get wrong: with the first wall at an even cell the tape is not a valid round start,
  and the machine then just runs on.

**The same question on the machine's own tapes** (`../conc/depthslack.py`, `deltanum.py`, `deltasize.py`). On a clean
tape every position is λN + κ with N = 2n + 6, and both λ and κ are dyadic rationals with the same denominator 2^s.
- **Depth and denominators.** At the first pass start of all 12 sampled 13-meeting runs, the binary digits of N that
  the tests have read so far number s + 1, so the denominators keep pace with the depth of the residue class.
- **The invariant is small.** Over 878 pass starts reached from 764 clean tapes (all long runs below 2^49 and 508
  mid-length ones), |Δ| ≤ 784 (the median is 12). Each gap is then a count of binary digits:
  G_R = s(λ_L) − s(Δ) and G_L = s(λ_R) − s(Δ), where s(·) is the exponent of the denominator. So **a gap is the number
  of trailing zeros Δ has when it is written with as many binary places as λ.** The trivial bound
  v2(Δ) ≤ log₂|Δ| < 10 gives G_R ≤ s + 10 and G_L ≤ s + 10.
- **The bound is at the edge.** One plain stretch, plus the at most 8 meetings of its exit, reaches the end only if
  G_R ≥ log₂R − 7 or so. Since λ_R ≈ 0.37, log₂R − s is about u, the number of binary digits of n not yet read at the
  pass start (9 to 15 in those 12 samples, 2 to 19 over all 256 long runs). So the stretch needs v2(Δ) ≥ u − 7: Δ must be a whole number, or nearly,
  with about u − 7 trailing zeros. With |Δ| < 2^10 the trivial bound allows that whenever u ≲ 16. The actual Δ's are
  far from whole: their binary expansions run to within 8 places of λ's, about 25 places past the point. (The left
  condition, G_L ≥ 6m + 1, is the binding one for long stretches: that is the lock again, which holds any single
  stretch to about a sixth of n's binary length.)
- **What each pass costs a one-parameter family** (`../conc/snfcost.py`, `snfplain.py`). The 2-adic elementary
  divisors of a word's coset lattice add up pass by pass:

  | Word (m passes) | Elementary divisors (exponents of 2) |
  |---|---|
  | plain loop | 0, 2, 4m + 1, 6m + 1 |
  | extra-wall loop, P^m | 1, 2, 4m + 1, 4m + 1, 6m + 1 |
  | detour, Q^m | 1, 2, 4m + 1, 5m + 1, 7m + 1 |
  | mixtures | sums: e.g. PQ gives 9, 10, 14; P⁴QP⁴ gives 37, 38, 56 |

  The divisors are the 2-adic sizes of the pass maps' eigenvalues: 1/16 for the end countdown (and, in P, its Jordan
  partner), 1/64 for the left countdown, and for the detour the two (b, c) eigenvalues (13 ± √153)/256, which are
  2-adic numbers (153 ≡ 1 mod 8) of size 2^7 and 2^5 (their product is 2^-12 and their sum 13/128).

  A generic line in state space follows a word only if it lines up with all but the largest divisor, and then its
  members must agree with a target modulo the largest. So on the machine's own tapes a plain pass costs 6 binary
  digits of n plus one line-up of 4 more digits (the gap condition G_R ≥ 4m + 1). A pass of the extra-wall loop costs
  6 digits and **two** line-ups of 4 each, and a detour 7 digits and line-ups of 4 and 5. The largest line-up any clean
  tape below 2^45 achieves at a plain pass start is 12 digits; if extra-wall entries line up no better, an
  extra-wall stretch on those tapes can make about one pass, which fits what is seen (all 631 such runs are short). A halting chain of about log₂n/4 passes would need about
  2·log₂n digits of line-up in all, against gaps that grow by about 0.3 digits per digit of n.
- **Checked on the machine's own lines** (`../conc/k1lineup.py`, `k1lineup2.py`, `plainlineup.py`). For each class,
  take the depth at which every test before the pass start is decided, so the class is a line in n, and ask whether
  any member of that line satisfies all of a word's congruences. For the first pass start of 20 of the long-run
  templates the answer is: exactly one plain pass (their gap G_R = 8 allows ⌊(8 − 1)/4⌋ = 1). For all 94 classes
  (to 36 digits) whose cycle reaches the extra-wall state G W W W W, **no member can complete even one pass**, of P,
  of Q, or of any of P², …, P⁵, PQ, QP, PPQ, PQP, QPP, PQPP. With about 10 binary digits of line-up needed per extra-wall
  pass, that is what 94 independent lines should give (expected 0.09).
- **The main route into the loop has a closed-form gap with a ceiling** (`../csearch/nrefgap2.c`, `nrefgap3.c`,
  `../conc/routecap.py`, `routetau.py`). Tag each pass start by the four round shapes before it. Over every settled
  class to 38 digits (229,961 pass-start lines), 90% arrive by G M M → G M M M → G M M W → G M W W → G W W W, and
  that route's gap never exceeds 8: its G_R distribution is 2: 65%, 3: 13%, 5: 12%, 6: 5.7%, 7: 2.4%, 8: 2.4%, with no 4
  and nothing above 8 (the mass at 8 equals the mass at 7, as if a geometric tail were cut off there). The reason is a
  closed form. Run the route symbolically from its first state, marker m and end E (the end marker tied to E − 2):
  R = (3E − m + 13)/8 and L = (5978E − 2401m − 7210)/16, independent as forms. On a clean-tape line m = λN + κ_m,
  E = N + κ_E this gives **G_R = v2(τ − τ*) − 3, where τ = κ_E − κ_m/λ is the line's 2-adic invariant and
  τ* = −38423/1225**. This matches every one of the 33,556 such lines to 34 digits. Over all 308,333 such lines to 39 digits, τ always
  agrees with τ* in 5 binary digits and never in 7 exactly, nor in 12 or more: (τ − τ*) mod 2^13 takes only 69 values,
  all multiples of 32, none ≡ 128 (mod 256), none ≡ 0 (mod 4096). The gaps above 8 (up to 12 by 43 digits) all come
  from rarer routes, e.g. G M B → G M M M → G M M W → G M W W (gaps 9 and 11 at 38 digits). So the slow growth of the
  largest gap is the appearance of new, rarer routes, each of which seems to have its own ceiling.
  230 of the 256 longest cascades below 2^49 enter the loop by the main route, every one of them at its ceiling,
  G_R = 8, which is why they all stop after one or two passes.
- **The main route's gap is a residue of the tape width** (`../conc/tautrace.py`, `centers.py`, `nutest.py`,
  `../csearch/nrefgap4.c`). The line invariant of any mark is τ_x = E(N₀) − x(N₀)/λ_x, and x(N₀)/λ_x is divisible by
  2^s, so every mark of a reachable configuration has τ_x ≡ E (mod 2^s), where E is the actual tape width and s ≈ the
  class depth (checked: at pass starts the three walls' τ agree to exactly min(s) binary digits). For the main route
  this gives **G_R = v2(W − τ*) − 3, where W is the tape width at the route's first round**: verified as
  W ≡ τ (mod 2^16) on the sample, with W − τ* = 11 · 2^11 for the 13-meeting template (gap 8). The reason is that
  the marker's slope dominates the line's direction 2-adically, so the combination 2401R − 2L that cancels it,
  2(1225W + 38423)/16, is left depending on W alone. In general a gap is v2 of an affine form in the positions of the
  marks whose slopes do not dominate.
- **Why the main route is special** (`../conc/route2.py`). For any route, write the countdowns as forms in the route's
  first state and the line as x = λ_x N + κ_x. Then G_R = v2(ℓ_R·L₀ − ℓ_L·R₀) − v2(ℓ_L), where L₀ and R₀ are the
  countdowns' actual integer values at the pass start and ℓ_R, ℓ_L are the line's slopes (Σ coefficient × λ). When
  the route's first state has a single free mark, its slope factors out and the gap depends only on actual integer
  values (for the main route, on W alone). The second route, G M B → G M M M → G M M W → G M W W, starts from two
  free marks (marker m, block r) with R = (4E − m − r + 15)/8 and L = (9408E − 2401m − 3430r − 4662)/16; there the
  gap also depends on the 2-adic ratio λ_r/λ_m of the two slopes, which encodes the history (the actual positions do
  not determine it: on the two record lines the position-only guess gives 2, the true gaps are 9 and 11). That
  extra freedom is where the gaps above 8 come from.
- **What the ceiling is.** Main-route entries occur at fixed stages of the cycle: round 8 with growth W − (2n + 6) =
  23, rounds 27 to 31 with growth 95, rounds 33 to 36 with growth 119 (to 32 digits). At a stage with growth g, a gap
  of G needs n to agree with the 2-adic rational ν_g = (τ* − 6 − g)/2 in about G + 2 low binary digits. The ceiling of
  8 says that the low digits a clean tape needs in order to reach that stage at all never agree with ν_g beyond 10
  or 11 places. The truncations of ν_23, ν_95 and ν_119 themselves have cycles of 7 to 14 rounds that never enter the
  main route. So a long main-route stretch would need a stage whose entry digits agree with its own ν_g, a fixed
  rational, in about log₂n digits.
  To 37 digits there are exactly three such stages (`nrefgap4`, every settled class): growth 23 (49,786 entries, all
  with n ≡ one residue mod 2^11, low-digit agreement with ν_23 of 4, gap always 2), growth 95 (62,448 entries,
  31 residues, agreement at most 8, gaps up to 6) and growth 119 (25,071 entries, 13 residues, agreement at most 10,
  gaps up to 8). So each stage's ceiling is the 2-adic distance between a fixed rational and a small set of residues,
  and the main route's overall ceiling is the best stage so far. The truncations of ν_g for every odd g below 8000
  (76,000 clean tapes of 25 to 62 digits) have right-end chains of at most 4 meetings.
  Further stages exist at greater depth. A beam over classes that keeps the 20,000 longest-lived open classes per digit
  (`../csearch/beamstage.c`, to 80 digits) finds main-route stages with growth 23, 95, 119, 191, 215, 287 and 383
  (successive differences 72, 24, 72, 24, 72, 96: multiples of a loop pass's 24). Their largest gaps are 2, 6, 8,
  6, 2, 6 and 7. So the ceiling of 8 held at every stage found, to 80 digits. (A random sample of 1.5 × 10⁹ clean tapes
  of 60 bits, `../csearch/mainroute.c`, sees the stages up to growth 287, with 1.49 million entries and the same
  largest gaps: 2, 6, 8, 6, 2, 3.)
- **What a proof would have to show.** For a chain of stretches, each stretch has its own Δ, and every one needs an
  unusually short binary expansion. The trivial bounds allow it. Ruling it out means showing that numbers below 2^10,
  whose binary digits are built from n's digits by the cycle, never end in about log₂n zeros. That is a 2-adic
  Diophantine statement about specific families, of the same kind as the open questions about Collatz-type maps,
  where heuristics are strong (here about 2 × 10⁻¹⁷ expected halts above 2^49) and no proof method is known.

**How many free numbers a halt needs** (`../conc/famtest.py`, `mixdrop.py`, `droptest.py`, `gmm2d.py`, `gmmk1.py`,
`../csearch/gmmscan2.c`, `dropfind*.c`, `gmmtail.c`, `gmmreal.py`). The halting tapes above have four free numbers
(three inner walls and the width; the first wall only needs the right parity). A halt needs a run of about log₂W
meetings, and a family of configurations with d free numbers at width W has about d·log₂W binary digits to spend. The
plain loop costs 10 conditions per 4 meetings but is locked: one stretch covers at most about two thirds of the
meetings, and it is the end of the run (proved: a run never re-enters it and leaves within 8 meetings). So at least
the first third must come from an unlocked pattern, the cheapest being the extra-wall loop at 14 per 4 meetings, then a
drop into the plain loop that keeps the progress made (a constant 12 conditions), then one plain stretch. Cheapest
total: (1/3)(14/4) + (2/3)(10/4) = **17/6 ≈ 2.83 conditions per meeting, so a halt at a large width needs d > 17/6:
at least three free numbers.** (An earlier version of this note said four, counting only extra-wall passes and
detours, at 3.5 per meeting; that is the threshold for words without a drop.)
- **Drops.** Right after a P or Q pass the simplest drop, G B W W → G M W W → G W W W, is 2-adically impossible (the
  words PD and QD have empty cosets), although it is the commonest drop from a generic extra-wall state. Over 2 million
  states that complete three forced P passes (`dropfind2.c`), 38 drop into the plain loop and complete a plain pass;
  in 33 of them the new last wall sits between a half and a seventeenth of the width from the end (the end distance
  was 2^-14.6 of the width before), so all the progress is lost. Five keep it, for example U = G B W W, G M M W M M, G M M W, G M W W, G W W W (12 conditions, end distance divided by 8),
  and V = G B W W, G M W M W W, G W W M W W, G B M W W, G W W W.
- **Three free numbers suffice.** In the four-wall family with one linear relation imposed (11c − 5E fixed; its value
  is forced mod 8 by each word, and the remaining three free numbers are b, d and one along c, E), the word P¹⁰UL¹⁸ (ten
  extra-wall passes, the drop U, eighteen plain passes) gives a tape of width 2^120 on which the real machine halts,
  through the proven rules, after 230 rounds, and P¹⁷UL³¹ gives one of width 2^200 that halts after 390 rounds. Both
  pass the mod-3 test. A sweep in the same family (`sweepdrop.py`, `../sweepdrop.log`, plain stretch two passes short
  of the lock, final distance 3) halts at the first try at every width tried: 2^24 (P¹UL²), 2^32, 2^40, 2^48, 2^64,
  2^80, 2^96, 2^128 (P⁹UL²⁰) and 2^160 (P¹²UL²⁵). The coset of P¹⁰UL¹⁸ has index 2^339 against the 2^360 a three-number box holds. In the same
  family, the extra-wall-only word of the right length, P¹⁴QP¹⁴, costs 2^416 and fails. The drop itself is real on
  the bare transition table: the word P U L² gives a 129,963-cell tape (walls 835, 15368, 57257, 64746, `droptape.py`)
  that hybsim predicts halts after 30 rounds at step 75,047,708,436, and `tmfast`, with no rules at all, halts at
  exactly that step.
- With extra-wall passes and detours only, the lattice shows the 3.5 threshold: the longest reduced basis vector of a
  word's coset grows by about 14/d binary digits per pass, and the run can reach the end only if that stays at or below
  4. Four walls: about 4.0 per pass, halting tapes at every width from 2^16 to 2^1000. Three walls entering the
  extra-wall loop the way real cycles do (G W W W → G B W → G M M W W → G M W W W → G M B W → G M W W W → G W W W W):
  about 4.7 per pass; at width 2^120 the longest word that fits is P¹¹QP¹¹ (23 passes), against about 29 needed.
- Every cycle of the machine starting from an even clean tape n begins, after one round, at a **GMM state** (gap at 1,
  a marker at m = n + 2, the end marker at W − 2, W = 2n + 11), and everything afterwards is a function of that state.
  The GMM states form a two-number family (m, W), so d = 2 even for the relaxation to all of them, and only 1 on the
  actual cycles. (Odd n reach n + 3 in two rounds.)
  - From a GMM state with m and W free, following every branch exactly to 26 binary digits (`gmmk1.py`): the
    extra-wall state is reached with total probability 2 × 10⁻⁵, and in only one branch (probability 1.5 × 10⁻⁸) can
    the two-number family then complete even one forced P pass; none can complete two. Along the two routes real
    cycles use from a GMM state into the extra-wall loop, the 2-D coset of (m, W) is already inconsistent for P on one
    route and for PP on the other (`gmm2d.py`): no GMM state of any size gets further. (Extended to 30 digits and
    explained in "The extra-wall loop needs three free numbers, exactly" above: 144 entries, at most one pass each,
    decided by each entry's position map alone.)
  - (Superseded by "The two-marker reduction" above: that scan runs only each state's own segment, includes the edge
    cases m = 4 and m = E − 7 left out here, and goes to width 262,143; the edge state (4, 13) halts.)
    Every GMM state of width up to 65,535 with 6 ≤ m ≤ E − 9 (503 million of them, mark model with contact detection, `gmmscan2_65k.log`):
    only four tiny ones, at widths 17 to 29, reach a meeting distance ≤ 2 or let marks touch, and none halts in the
    model. On the real machine none of the 176,715 GMM states up to width 1201 halts at all (run through the proven
    rules, `gmmreal_401.log`, `gmmreal_1201.log`; no contact needed plain transitions). The closest approach, as
    halvings log₂(E / distance), per width range: 9.9 (2^11–2^12), 8.5, 9.2, 11.2 (2^14–2^15), 12.0 (2^15–2^16),
    against 11 to 14.6 needed. It grows like about 0.8·log₂E, the rate a two-number family gets at 2.5 conditions per
    halving (2·log₂E / 2.5).
  - Runs per cycle (`../csearch/runstretch.c`, 3 × 10⁹ random 60-bit cycles, 5.8 × 10⁹ runs): 3.0 × 10⁶ runs contain
    a loop stretch and none contains two.
  - **Per-state odds** (`../csearch/gmmtail.c`, 10⁹ random GMM states at width about 2^48, from the whole plane and
    from the machine's own line E = 2m + 7): P(closest approach ≥ h) falls by about 2.4 to 2.5 binary digits per extra
    halving in both, the plain loop's 10 per 4 meetings (plane: 2^-8.6 at h = 4, 2^-18.0 at 8, 2^-28.3 at 12; line:
    2^-13.5, 2^-23.5, and 6 states reach h = 10). The odds do not depend on the width. On the machine's line they are
    20 to 30 times smaller at every h; other lines E = 2m + c differ among themselves by up to a factor 500 at h = 6,
    each because of a few shallow residue classes (on c = 1, 97% of the states with h ≥ 6 have m ≡ 1008 mod 1024),
    and c = 7 is among the thinnest. The marker's relative position m/E hardly matters.
    The reason is the cycle's returns to a GMM state (`gmmtail4.c`, 5 × 10⁷ states each). A cycle is a chain of
    segments, each from one GMM state to the next or to the clean tape; each segment returns to a GMM state with
    probability about 0.34 on the plane and on the line alike. Per segment, the odds of reaching h ≥ 4 given that the
    segment is reached are 1.4 to 1.8 × 10⁻³ on the plane, whatever the segment's index. On the machine's line they
    are 0 for the first segment, 3 × 10⁻⁷ for the second, then 2.7, 6.7, 6.4, 9.1, 10, 14 and 18 × 10⁻⁴ for the third
    to the ninth: the line's GMM states start out special and only become as random as plane states after six or
    seven returns, each of which happens with odds 0.34. (Earlier view of the same thing: on the line the first four
    right-end runs never reach h ≥ 4, and the closest run comes from round 21 on.) The largest h seen within segment
    r over 2 × 10⁸ line states: 1.42, 6.39, 8.59, 10.36, 8.62, 9.04 for r = 0 to 5. The reason is diversity
    (`../csearch/linetypes.c`, 10⁶ random 48-bit even n, exact symbolic forms): the r-th GMM state of a cycle lies on a
    line E = (b/a)·m + c fixed by the branch the cycle took. The first is always on E = 2m + 7; the second is on one of
    just two lines, E = 8m + 13 or 13E = 16m + 127; the third on at least 61, the fourth on at least 347, the fifth on
    at least 697 (the counts for r ≥ 2 still grow with the sample). On top of that, E's low digits are n's low digits,
    which the history pins to a few residues when r is small, while the marker's low digits are fresh digits of n each
    time. Even the whole line E = 8m + 13 has odds 2.5 × 10⁻⁴ of h ≥ 4 (`gmmtail6.c`); the machine's states on it,
    with their pinned residues, 3 × 10⁻⁷. The shares are dyadic: of the cycles from even n, 1/4 reach a second state on
    E = 8m + 13 and 1/8 on 13E = 16m + 127 (so the first segment returns with odds exactly 3/8; it is settled by n mod 16);
    third states lie on E = 64m + 25, 9E = 64m − 41 and 13E = 64m + 205 (1/32 of cycles each), 49E = 128m + 143 and
    109E = 128m + 1147 (1/64 each), 241E = 256m + 2293 (1/128), and dozens of rarer lines (`linetypes3.c`).
  - **Proved: the first segment never comes close** (`../csearch/segproof.c`). Following the symbolic cycle of every
    residue class until the first segment ends takes only 5 classes (depth at most 4), and in every member n of each
    class the end meetings of that segment stay at least 2^-1.62 of the width away. The second segment is not bounded
    this way: following it, classes are still open at depth 52 (2,886 of them) and its largest h grows slowly with
    depth (6.4 to depth 34, 7.6 to 46, 8.5 to 52). The 1,445 classes still open at depth 46 are not in the middle of
    a long run: their deepest end meeting so far is 2 to 6 halvings, and they hold 2 to 6 marks. What uses up their
    digits is markers halving away from the end, the same thing that makes the whole tree grow. The same class walk
    gives exact 2-adic shares (all n, large n) of cycles whose segment r has an end meeting at least 4 halvings in:
    0 for r = 0, 5.4 × 10⁻⁸ for r = 1 (plus at most 2 × 10⁻¹¹ undecided at depth 46), 1.9 × 10⁻⁵ for r = 2 (plus at
    most 6 × 10⁻⁹ at depth 40), matching the sampled odds (`segproof3.c`). To depth 80 (`segproof128.c`, 128-bit
    forms; the 64-bit version is only valid below depth about 58), the second segment's shares for an end meeting at
    least x halvings in are 5.4 × 10⁻⁸, 2.4 × 10⁻⁸, 3.0 × 10⁻⁹, 1.2 × 10⁻¹¹, 1.1 × 10⁻¹⁴, 1.5 × 10⁻¹⁸, 1.2 × 10⁻¹⁹,
    4.6 × 10⁻²¹ for x = 4 to 11, with 1.9 × 10⁻¹⁹ undecided (1.2 × 10⁻²¹ at depth 90, with the same shares). The
    largest h found grows slowly with depth: 8.5 to depth 52, 12.0 to 70, 13.5 to 90 (a class mod 2^90). That is
    about 6 binary digits per halving on average, and lumpy (single steps from 1 to 13 digits), against a random GMM
    state's steady 2.5.
  - The record cycle n = 391,305,139,022 (14 meetings) returns to a GMM state 8 times; its long run is the eighth
    segment, which starts at the full width and descends one halving per meeting to h = 14.
  - With these odds the expected number of halting GMM states of width 2^k is about 2^(0.24 − 0.46k) even ignoring the
    lock: about 0.9 in all widths up to 65,535 (none found; four came within 2 cells or touched, all at widths 17 to
    29) and about 0.02 above. On the machine's line it is smaller by a further factor of about 2^k: extrapolating the
    line's 2.3 digits per halving, the trajectory above 2^49 (which visits about one integer in 9) expects about
    10⁻²² halts, against the 5 × 10⁻¹⁶ of the top-running fit above, whose tail is heavier (1.8 digits per halving).
- So the machine's runs live in a family with two free numbers at most, and a halt needs more than 17/6. This is the
  structural reason behind every measured rarity above; it is still a counting argument, not a proof, because 2-adic
  coincidences inside a two-number family are not ruled out.

**Where this leaves a proof.** Within the mark model, and for separations large compared with the rules' constants:
- proved by finite exhaustive search: every run that reaches a G W W W state makes 4 meetings per pass of the loop and
  then at most 8, never re-entering it, and the meeting that starts the next run is at least (c − b)/8 from the end;
- proved by algebra: the loop makes at most log₆₄|L₁| passes, |L₁| ≤ 280E, L₁ never 0; the same holds for the loop
  with k extra walls (L never 0 checked for k ≤ 2500);
- proved by finite exhaustive search from the main run-start shapes: G W W W within 3 meetings, or the run ends
  within 6.
- proved by finite exhaustive search (October 22, "Sharpened by the exact end of the loop"): a run that halts
  through the plain loop closes from its last pass start with R ≤ 176 and L₁ in a fixed residue class mod 7·2^j, and
  with σ = 3s + 2λ unchanged by a pass this gives **log₂W ≤ σ + 6.38** at the first pass start. Since λ ≤ log₂280,
  that is log₂W ≤ 3s + 22.64.
**The target this leaves (October 22).** With the exhaustive check covering widths below 2^60, a halt through the
plain loop needs a plain-loop entry with σ ≥ 53.6, hence s ≥ 12.45: the run must reach its first plain pass start at
least 12.45 halvings below the width. Under the measured run structure that never happens: run starts are at most
5.65 halvings below the width (staircases included), and from the main run-start shapes G W W W comes within 3
meetings (exact), so with one more meeting to reach the phase-0 pass start s ≤ about 9.7 (each meeting at most halves
D) and log₂W ≤ about 51.6, inside the exhaustive range; the old window 2^55 < n < 2^76 below is empty under the same
assumptions. The latest entries actually found in sampled runs are σ = 36.45 (s = 8.89, a staircase at its limit)
and σ = 39.17 (s = 9.87, through an extra-wall pass); the largest s seen at any sampled entry is 11.89, with λ near 0.
But the assumptions are not laws: extra-wall pieces can add any number of meetings before the entry, at about 3.4
binary digits each (exact tree under "How late extra-wall pieces can make the plain entry"), and GMM-born chains
within 46 digits already reach H = 18.9 (all excluded). What a proof would still need: (i) that runs never use the extra-wall family to reach a plain entry with σ ≥ log₂W − 6.38,
(ii) that runs without a plain stretch cannot halt (the extra-wall family has no finite endgame, and hand-built tapes
halt that way), and (iii) the separation and contact conditions.

**The shape of what is proved, and of what is not (October 23, night).** Everything exact now fits in one statement.
*Theorem (mark model, marks far apart).* Let a round start have shape G W W W with walls a < b < c and width E, followed
by G B W and G M B, and put R = E − c − 1 and L₁ = 147b + 280E − 392c − 578. If the right-end run through this state ever
brings the gap within 2 cells of the end marker, then for some p ≥ 0: R = 16^p·r with r ∈ {2, 4, 8, 16, 24, 32, 48, 64,
176}, r ≡ 0 (mod 4) if p ≥ 1, and L₁ ≡ 64^p·c_r (mod 64^p·M_r) with (c_r, M_r) = (10, 14), (10, 14), (24, 56),
(192, 224), (416, 448), (192, 448), (640, 896), (640, 896), (640, 896). Hence 3 log₂(E/R) + 2 log₂(|L₁|/E) ≥
log₂E − 6.38. (Proof: the two exhaustive searches with R fixed, every even R to 4096, one of them with every order
comparison decided on the cone of large gaps; at most 8 meetings follow a loop state without a new pass, so larger R
cannot close; a pass maps (R, L₁) to (R/16, L₁/64) exactly and lands on a state of the same kind; passes happen only
from R ≡ 0 mod 64.) *Corollary.* For a GMM state (m, E) whose segment reaches such a state along a fixed route, R and
L₁ are affine in (m, E); so the route has a ceiling for 3 log₂(E/R) + 2 log₂(|L₁|/E) as E → ∞, no member halts through
that stretch above width 2^(ceiling + 6.38), and below it the halting members lie on explicit lines, enumerable. Every
route decided within 62 digits has ceiling ≤ 52.86; every route decided within 46 digits has no halting member at any
width ≥ 2^17; every GMM state below width 2^18 was run directly.
*What remains is three statements of the same kind, each about an infinite family of coincidences:*
(a) for the machine's own lines, the routes not decided within 62 digits (measure 8 × 10⁻¹⁰ of GMM states, falling
0.71 per digit; by the route tail the machine should meet of order one lock-permitted entry in its whole future);
(b) halts with no plain stretch, which need the extra-wall family (no finite endgame; three countdowns, so on the
machine's two-number families each way in has a hard cap, observed 0 to 4 passes, and a halt would need about
log₂W/4 of them);
(c) two marks coming within the rules' constants of each other (every such event is one N per class, like the
pinning; none below 2^59).
None of the three can be finished by enumeration, because the families are infinite; each is a 2-adic coincidence
question of Collatz type. What the exact theory does is make the coincidence explicit: a halt at width 2^k needs a
route about 1.2k digits deep (more digits than n has) and, on top of it, about 2.5(k − s) further binary digits of
agreement, where s is the lateness the route supplies.

**Certificates and independent checkers (October 24; `../cert/`).** The exact end of the loop rested on two programs
(`endsym.py` on the stepper engine, `gx2 endgame` in C) agreeing. It now rests on something that can be audited
without trusting either: each explorer writes out its result as a *certificate*, a list of leaves, and a separate
program re-derives every leaf from the mark rules alone. The pieces:

- `endgame_leaves.txt` (40,991 leaves, every even R from 2 to 4096): the phase-0 pass starts G 1, W a, W b,
  W c = E − R − 1, M E − 2 (a odd, b even, E even), partitioned into 2-adic classes of (a, b, E), each leaf with its
  claimed outcome: `close` (an end meeting at distance d ≤ 2, the only configuration from which the machine can halt),
  `pass` (the rounds G W W W, G B W, G M B appear again), `break` (an end meeting at a non-constant distance that is not
  the continuation of the previous one), `notphase0` (the first two rounds are not G B W, G M B, so the start was not
  in the loop); and the round shapes along the way.
- `endgame_anyphase_leaves.txt` (83,699 leaves): the same from every G W W W start of that class, phase or no phase.
- `exit_leaves.txt` (358 leaves): the G W W W tape with a, b, c, E all free (the loop state in either phase), followed
  until a break, a clean tape, or a full loop cycle (`pass`).
- `check_endgame.py`, `check_exit.py`: the checkers. Each has its own implementation of the round recurrence (the
  table under "How the rules give the round recurrence") on symbolic positions, affine forms with exact rational
  coefficients. A digit test (d mod 2, d mod 4, the parity of a packet's target) is decided by the leaf's class, and the
  checker refuses if the class does not decide it. An order comparison (which mark comes first; do two marks overlap;
  is a meeting at distance at least 4, so that the swap and merge rules apply and the meeting is not a close) is decided
  by the signs of the gap coefficients alone, with no geometry, and the checker refuses if the signs are mixed. Every
  configuration the rules do not cover (a packet reaching a block, marks touching, a shift meeting a sleeping gap, …)
  is a refusal too. For each R the checker also verifies that the leaves are a partition of the start class: every
  lattice has index 8·2^bits, the measures sum to 1, and the cosets are pairwise disjoint (Hermite normal form). It
  then reads the closing table, the L₁ classes, the pass condition and the bound off the verified leaves.
- Results: all three certificates **valid**, with no failure, no undecided test and no uncovered configuration. The
  endgame checker reproduces the closing set {2, 4, 8, 16, 24, 32, 48, 64, 176}, the nine L₁ classes, the pass condition
  R ≡ 0 (mod 64), L₁ ≡ 1536 (mod 1792) and the bound 3 log₂R − 2 log₂|L₁|min ≤ 6.38; the any-phase checker the closing
  set {2, 4, 6, 8, 16, 22, 24, 32, 48, 64, 176} (6 and 22 are 48 and 176 seen from the phase-6 state, three end
  meetings and three halvings later); the exit checker a longest chain of 8 end meetings, no close, and a
  full loop cycle on measure exactly 1/1024 (the 10 bits per pass).

*Where the cone rule is exact.* A sign decided from the gap coefficients is the true sign when the gap part outweighs
the constant: Σ gᵢtᵢ > |c|, which holds for every gap tᵢ > Γ with Γ = |c| / Σ|gᵢ|. The checkers record the largest Γ
over every decision they make (and over the decisions that involve each set of gaps):

| certificate | every decision exact once every gap exceeds | by the gaps a decision involves |
|---|---|---|
| endgame (phase 0) | 447 cells | a alone 1; a, b−a 447; a, b−a, c−b 8.0; c−b alone 10 |
| endgame (any phase) | 447 cells | a alone 1; a, b−a 447; a, b−a, c−b 19.4; c−b alone 10 |
| exit (R free) | 447 cells | a alone 1; a, b−a 447; a, b−a, c−b 355; all four 22.1; c−b alone 10; c−b, R+1 10.7; R+1 alone 241 |

So the theorem under "The shape of what is proved" is certified in this form: *for every phase-0 pass start whose three
stripes a, b − a, c − b exceed 447 cells, and any R*: if R ≤ 4096 the endgame certificate applies with R exact; if
R ≥ 242 the exit certificate applies (its decisions that involve the end distance alone are exact from R + 1 > 241),
and it allows no close at all, at most 8 end meetings, and a continuation of the loop only on 1/1024 of the class. The
two overlap on 242 ≤ R ≤ 4096. The stripe hypothesis is exactly the "marks far apart" of the theorem, now with a
number; a pass start with a stripe shorter than 447 cells is a tape on which two marks are within a few hundred cells
of each other, which is family (c) of the three that remain (none occurs below 2^59, where the class tree logs the
least separation of every settled class; on the machine's own tapes it is one affine form in n and E landing in a window of width 447, a
coincidence of the same kind and rarity as the ones a halt needs).

*The route tree, certified the same way* (`../cert/check_tree.py`, `tree36_leaves.txt`; the explorer `../csearch/rtree3e.c`
is `rtree3d.c` with a leaf printer). The route tree over two-marker states is the computation behind the ceilings, and
it can be audited the same way as the endgame. With `LEAFPRINT=1` the explorer writes every leaf of the tree: the kind
of ending (the next clean tape, or a cut at the depth limit), the list of meeting outcomes along the way (d mod 4 at
every meeting of the gap with a marker, in order) and the round shapes. Nothing else is needed: the checker replays
each leaf from the start state G 1, M m, M E − 2 (m even, E odd, all valid two-marker states) with its own
implementation of the rules on affine forms in (m, E). At each meeting it decides d mod 4 from the current class if it
can, and then the recorded outcome must agree; if the class does not decide it, the recorded outcome is imposed and
counted as a split. Comparisons of positions are decided on the cone of large gaps (m and E − m) — the explorer
decides them at an asymptotic ratio, so this is a stronger rule, and it never had to refuse — and every configuration
outside the rules is a refusal. The split sequences of all leaves must then form a complete prefix code (no sequence
a prefix of another, measures 2^−depth summing to 1), which is the partition of the start class; the recorded cosets
are not used at all. Along each path the checker also notes every phase-0 pass start (the rounds G W W W, G B W,
G M B) with its own forms of b, c and E, and recomputes the σ ceiling, so the tree's summary (entry measure by
ceiling, largest ceiling, undecided measure) is reproduced from the leaves alone.

Result at 36 binary digits: **valid**: 946,207 leaves (539,120 next clean tapes, 407,087 cuts at the
depth limit), no replay failure, no undecided test or comparison, no uncovered configuration; the split paths form a
complete prefix code (measure exactly 1); the pass starts met along the paths have total measure 2.072622 × 10⁻³,
largest ceiling 35.906, and their measure in every one of the 29 ceiling buckets agrees with the explorer's own
summary to all printed digits; the undecided measure is 5.92 × 10⁻⁶, as the explorer reports. Every comparison was
decided on the cone (the explorer's asymptotic-ratio decisions never differed from a cone decision). The cone decisions
are exact once m exceeds 7,340,032 = 7·2²⁰ cells (decisions involving E − m alone: 2 cells). The 40-digit tree
(3,949,190 leaves: 2,266,244 next clean tapes and 1,682,946 cuts, checked in two halves with the split paths of both
written out and the partition verified over their union by `kraft.py`): **valid** the same way — no refusal, measure
exactly 1, largest ceiling 38.965 as the explorer reports, all 32 ceiling buckets equal to the explorer's figures to
their five printed digits, undecided 1.53 × 10⁻⁶; exact once m exceeds 7·2²² cells.

Why the exactness threshold is large here: a leaf whose run makes j end meetings has a meeting at distance
(t + k)/2^j, and deciding that this is at least 4 needs t ≳ 2^(j+2). So the threshold grows with the depth of the
run, as it must: it is the statement that the gaps are wide enough for j halvings to happen at all. On the machine's
own tapes beyond 2^59 every gap is of order 2^58, far above the thresholds of any route in the tree.

The 46-, 62- and 64-digit trees are the same explorer run deeper (`rtree3d.c`, which differs from `rtree3e.c` only
by the printer); they are not certified leaf by leaf, since the leaf count grows about 1.43-fold per digit (946,207
at 36 digits, about 4 million at 40, of order 10^10 at 62).

**Formalization, first layer (October 25, night; `../lean/`, copied to `lean/` here).** The mark rules are now
machine-checked in Lean 4 (v4.34, core library only, no Mathlib). `BB6/Basic.lean` defines the machine — states,
the transition table of 1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LD1RE, tapes as two streams `Nat → Bool` with the head
on the first cell of the right one, `step`, `steps n`, and the chaining lemma `steps_seq`; a pattern with unknown
surroundings is a configuration whose streams are variables `L R`, so a theorem quantified over them holds for any
surrounding tape, and a `rfl` proof of `steps n c = some c'` can only go through if the n steps never read `L` or
`R` — the Lean form of the Python prover's "the simulator raises if it would read a context". Repeats `(10)^m` are
`rep m [1,0] s`; unrolling one copy is definitional, crossing a whole repeat is one of the three cycle lemmas
(`BB6/Cycles.lean`: `pass`, `shift`, `carry`, by induction on the count), and the only other facts about repeats
are two re-bracketing lemmas, `x (y x)^n = (x y)^n x` and "a repeat absorbs a copy behind it", also by induction.
`BB6/Rules.lean` is *generated* from `proofs.py` by `gen_rules.py`: it runs the Python prover on each rule, and emits
one Lean theorem per rule whose proof follows the prover's own trace — stretches of single steps by `rfl`, the cycle
lemmas where the prover used them, the re-bracketing rewrites in between, and `omega` for the step count. All 21
rules (BOUNCE, SWAP, MERGE, WALLBOUNCE, the five MEET rules, GAP→blank end, the four BLOCK rules, the six PACKET
rules and PACKET→block halting) check, each with its exact step count for every m, j and every L, R; `BB6/Iter.lean`
adds BOUNCE^k and WALLBOUNCE^k by induction on k with their counts 6km + 6k² + 24k and 6km + 3k² + 9k, and
`BB6/Rows.lean`, `Rows2.lean` every row of the round recurrence table as a composite theorem with its count (gap
meets marker: k bounces then a swap or a merge; gap meets wall: k wall bounces then the MEET rule for what the shift
finds; gap with nothing to its right). `BB6/Marks.lean` starts the position level: marks with positions, the tape
built from a mark list and a width, and the first two rows as statements about positions (a marker at 4k + 4 ends
at 2k with the gap at 2k + 2 and the marks beyond untouched; a marker at 4k + 6 leaves a packet at 2k and a wall at
2k + 5), 66 theorems in all. `BB6/Model.lean` then defines **the mark model itself as a Lean function**:
`Model.round` computes the marks and width after one round from those before it, row by row as the certificate
checkers' simulator does (ported from `check_endgame.py`), with outcomes next / halt / uncovered; it is executable,
and `Test.lean` runs it side by side with the machine's own `steps` from the first round start (the tape after 17
steps from blank, `G 1` and width 5) and compares the two tapes cell by cell at every round start: 200 rounds, 8,546,966
machine steps, width 728 at the end, no mismatch (the port's one slip, dropping the sleeping gap when a pass reaches a block, showed up at
round 12 and was fixed from the Python). This function is the specification for the faithfulness theorem, and `BB6/Mid.lean`, `Pkt.lean` prove its first
events in general form: with `midCfg msL g msR W` (head on the gap at g, marks on both sides, width W) and `pktCfg`
(a packet at x), the swap and merge events hold for every such configuration (`ev_swap`, `ev_merge`: the only
hypotheses are a stripe cell before the gap and one after the marker, or the end marker), and the packet crosses a
marker (`ev_pkt_marker`) and wakes a sleeping gap (`ev_pkt_gap`) as the model says. Every theorem of this
layer depends only on the axioms `propext` and `Quot.sound`; there is no `sorry`. Lean was built from
source in the container (release binaries are not reachable from it), which is why the first compile came hours
after the files were written; the generator needed one fix after it (a re-bracketing rewrite applied to both sides
of a hypothesis instead of one) and the hand-written files two one-line fixes.

**Formalization, second layer: the round theorem (October 25–26; `BB6/Mid` … `BB6/Round`).** Every event of a round
is now a theorem about positions, for arbitrary marks on both sides: the gap meets a marker (swap, merge), a wall
followed by a marker, a wall, a block, blank tape or the end marker, a block followed by any of those, or nothing;
the packet crosses a marker or stops at a gap, a wall, a block (the machine halts: `steps … = none`) or the left
end. The contact conditions are stated as the values of single cells (`oneBefore g`: the cell before the gap reads
1, so a marker or block may touch it), which is exactly what the rules read. Two well-formedness predicates,
`leftOK` and `rightOK`, record the order of the marks and the parity of every stripe between them — and of the last
stripe: **the width W is the first cell of the all-zero tail, so the cell W − 1 is a 1**. On top of these, the mark
model is written a second time in zipper form (`pktBack`, `gapEvent`, `roundZ`: the active gap or packet with the
marks to its left, nearest first, and to its right), and proved: from the tape any well-formed round start denotes,
the machine reaches the round start `roundZ` computes, or halts exactly when `roundZ` says halt (`round_run`); by
induction, for any number of rounds (`rounds_run`); and with the first 17 steps from blank (`first_round_start`,
stated with the exact tape), **from blank tape the machine follows the model for as many rounds as the model covers**
(`blank_rounds`). The model's third outcome, `uncovered`, is a configuration no proven rule covers (a meeting at odd
distance, marks touching where a rule needs a stripe cell, a packet meeting a marker right after a wall); it makes no
claim, and a proof of non-halting along these lines needs every round the argument uses to be covered. 17 files,
under a minute to check, no `sorry`, Lean's three standard axioms.

The zipper model agrees with the list-based port of the checkers' simulator (`Model.round`) on all 200 rounds from
the first round start, and on 20,000 random well-formed round starts no outcome differs where both make a claim. The
comparison found one place where the simulator is wrong, described next.

**The trailing wall (October 26).** When a shift reaches a block that ends the tape (the block in the last three
cells, so no stripe after it), the simulator — `check_endgame.py`, `check_exit.py`, `check_tree.py`, every C explorer,
and its Lean port — writes the resulting wall in the last two cells, one of them past the width. That is the same
tape as no wall and width W − 1 (`build_trailing_wall`), but the simulator keeps the wall as a mark, and a later shift
that reaches it turns it into a block running past the width, where the machine finds blank tape and forms an end
marker (two cells, not three). The sequence needs a wall with exactly one stripe cell after it at the end of the
tape, a shift that makes it a block, a second shift that reaches the block, and a third that reaches the wall. On
random well-formed starts run for 8 rounds against the machine, the simulator gave a wrong tape in 2 of 1,500 (both
this sequence); the zipper model writes the canonical form and is never wrong. **Audit of the computations that use
the simulator:** instrumented copies record every shift that reaches the last mark, and how far that mark is from
the end of the tape. Every run reproduces its original output exactly (same totals, same
certificate verdicts and margins), and in none of them does a shift reach a block ending the tape or a trailing
wall:

| computation | shifts reaching the last mark | of them at or past the tape end |
|---|---|---|
| exit certificate (358 leaves) | 916, every one at a distance > 4 decided on the cone | 0 |
| endgame certificate (40,991 leaves) | 78,290; closest fixed distances: wall 3, block 5 | 0 |
| any-phase certificate (83,699 leaves) | 140,343; closest: wall 3, block 5 | 0 |
| exhaustive DFS to 36, 42, 46 digits | 3.5 million, 43 million, 239 million | 0 |
| route tree (C explorer) to 36 and 44 digits | 0.34 million, 5.9 million, all at distances growing with the class | 0 |
| exact plateau exits (118 limits, 40 digits) | 117,627, all growing with the class | 0 |
| certified 36-digit route tree (946,207 leaves; Python, distances decided on the cone) | 3,354,989, every one at a distance > 4 decided on the cone | 0 |

The endgame runs come closest: shifts do reach a wall one stripe cell from the end (distance 3, which makes a block
ending the tape), but no shift ever reaches such a block afterwards (the closest block is 5 cells from the end), so
the trailing wall never forms. **No result recorded in these notes depends on the slip.** The deeper exhaustive runs
(48 to 60 digits) were made with the uninstrumented program and are covered by this audit only as far as 46 digits;
the slip needs three shifts in a row to reach the last few cells of the tape, which the runs to 46 digits never
produce even once in 239 million shifts that reach the last mark. The programs in `audit/` are the instrumented
copies.

**The trailing wall, fixed (October 27).** The simulators now write what `roundZ` writes: when a shift reaches a block
that ends the tape (nothing after it, W = position + 3), the block becomes blank tape, with no wall and width W − 1; a
block that would run past the width is refused. Changed: `../cert/check_endgame.py`, `check_exit.py`, `check_tree.py`
(a distance to the tape end that is not constant must be ≥ 4 on the cone, or the leaf is undecided), the C engines
`../csearch/nrefdfs2.c`, `lined.c`, `rtree3d.c`, `rtree3e.c`, `gx3.c` (each prints `trailing-wall canonical forms
written: N` to stderr), and the stepper engine with its copy in the stepper page. The other programs in `../csearch/`
are left as they were run.
- *Differential test* (`../simtest/`, `check.sh`). Every one of these programs, and the bare transition table, runs
  the same random well-formed round starts as the proved model (`Oracle.lean`, which runs `roundZ`); wherever both
  make a claim (next round start or halt) they must agree. Fixed programs, 20,000 starts × 12 rounds: no disagreement
  (161,390 rounds compared for the C engines and the machine, 149,478 for the endgame and exit checkers and the
  stepper, 56,073 for the tree checker, which refuses more). The original programs, on 3,000 starts × 8 rounds and
  after reducing their output to canonical form, give a different tape in 24 starts each (9 for the tree checker).
  With the bare machine as the reference instead, the C engines also differ on configurations the proved model calls
  uncovered (marks touching: a block or wall directly after the gap, …), where they apply a rule outside its
  conditions; the Python checkers refuse those. This is the known contact question, not the slip, and the exhaustive
  engine's separation probes are what exclude it there.
- *Certificates.* With the fixed checkers the exit, endgame and any-phase certificates and the 36-digit route tree
  (946,207 leaves, 27 minutes) are VALID, with output identical to the unfixed checkers'. (The committed `../cert/check_exit.out` is older than the checker: the current
  checker, fixed or not, prints the per-gap margins and an overall cone threshold of 447 rather than 255.)
- *Exhaustive check.* The fixed `nrefdfs2` to 54 digits (48 parts at split level 26, about 4.3 CPU hours,
  `../dfs/merged54_fixed.txt`) reproduces `merged54.txt` line for line (the levels 1 to 54 of the 56-, 58- and 60-digit
  runs also agree, up to the known tie at level 35), and the corrected case occurs 0 times in all 48 parts. To 56
  digits (96 parts at split level 28, about 11.3 CPU hours, `../dfs/merged56_fixed.txt`) the fixed engine reproduces
  `merged56.txt` line for line, again with the corrected case 0 times in every part. So the audit, which reached 46
  digits, now reaches 56. Finally the whole 60-digit run was repeated with the fixed engine (384 parts at split level
  31, as `../dfs/K60/`, run in four ranges on four machines, about 70 CPU hours, `../dfs/merged60_fixed.txt`): it
  reproduces `merged60.txt` line for line, totals included, and the corrected case occurs 0 times in all 384 parts.
  **The 60-digit result stands with the fixed engine**: no clean tape below 2^61 reaches a halt in the mark model.

**Formalization, third layer: the certificates through the proved model (October 26; `BB6/SymForm`, `BB6/SymRound`,
`CheckEndgame.lean`, `CheckExit.lean`).** A certificate leaf is a coset x = x0 + B·y; substituted into the start
state, every position becomes an integer affine form in y, so halving and digit tests are exact integer facts (halve
only when every coefficient is even; a residue is decided when every y-coefficient is divisible by the modulus). An
order test is decided on the cone of large gaps by an explicit certificate D·p = Σ μⱼ·tⱼ + c with μⱼ ≥ 0, checked
coefficient by coefficient, which gives p > 0 whenever every gap tⱼ ≥ Γ (how μ is found, by exact elimination, is not
trusted; only the identity is). On these positions the zipper model is written once more, branch for branch, and
proved sound against it: at every point of the cone, a concrete state that agrees with the symbolic one has a
concrete outcome that agrees with the symbolic outcome (`symRoundsZ_sound`). With the well-formedness of the start
decided the same way, `leaf_run` turns a checked leaf into a statement about the machine: **for every member of the
leaf with all gaps ≥ Γ, the machine runs from the leaf's start to the computed round start without halting.** Two
small programs read the certificate files and run every leaf through this model:

| certificate | leaves | checked in Lean | Γ needed (Lean / Python) |
|---|---|---|---|
| endgame (phase-0 starts, R ≤ 4096) | 40,991 | all: 32,710 break, 8,184 not phase 0, 63 pass with every round covered and every shape as claimed; the 34 close leaves agree up to the close | 448 / 447 |
| any-phase starts | 83,699 | all: 83,087 break, 574 pass with every round covered and every shape as claimed; the 38 close leaves agree up to the close | 448 / 447 |
| exit (loop state, R free) | 358 | all 358 (356 exits, 2 passes) | 390 / 255 |

The exit certificate needs a larger margin in Lean because the proved model makes a few decisions the Python
simulator does not (at the end of the tape, and the guards of its natural-number subtractions); 390 still overlaps
the endgame range (R ≤ 4096) with room to spare. These runs check the certificates' leaves; what they do not check is the
partition (that the leaves' cosets cover the start class, which the Python checkers verify with lattice indices and
pairwise disjointness).

**Coverage by construction (`BB6/SymSplit`, `Explore.lean`, `ExploreExit.lean`).** Instead of proving the partition
of the Python leaves, the classes are split again in Lean, by coordinates: splitting on coordinate i substitutes
yᵢ = 2zᵢ + ε in every form, so the two children contain every point of the parent (`cover_split`). A tree of such
splits whose leaves all pass the proved check `Tree.ok` therefore covers its whole start class, and `Tree.sound` says:
at every point of the start class with all gaps ≥ Γ, the machine runs the leaf's rounds without halting. The trees are
built by an untrusted program (it picks each split from the first residue a round leaves undecided and stops a leaf
where the Python classification stops), compiled to native code, and every tree is then checked by `Tree.ok`:

| start class | leaves (coordinate splits) | trees accepted by `Tree.ok` | classification |
|---|---|---|---|
| phase-0 pass starts, every even R ≤ 4096 (a odd, b even, E even) | 99,665 over 2,048 values of R | all at Γ = 448 outside R = 2 (whose d = 0 close is an uncovered round); no leaf undecided | 90,171 breaks, 9,207 leaving phase 0, 252 completed passes, 35 closes |
| loop states, either phase (a odd, b even, c odd, E even) | 22,230 | all, at Γ = 390; no leaf undecided | 19,796 breaks, 2,394 clean tapes, 40 completed passes; no close |

The coordinate splits are finer than the certificates' (which split on arbitrary residue forms), hence the larger leaf
counts; the classification labels come from the untrusted builder and are not part of the theorem.

**The closing set inside the theorem (`BB6/Meets`).** An end meeting is the gap meeting the end marker; the run
closes when one is at distance d ≤ 2. `meetsZ` lists the distances of a round's end meetings, following `roundZ`
event by event, and its symbolic mirror is proved to agree with it (`symMeetsZ_sound`). `Tree.okNC` checks, besides
`Tree.ok`, that every end meeting in each leaf's rounds is at distance ≥ 3 on the cone, and `Tree.soundNC` turns that
into a statement about the machine: no halt **and no close**. A close at d = 0 happens in a round the rules do not
cover (the swap puts the end marker against a 1: a contact), so a leaf that closes that way includes the uncovered
round and fails the check, as it should; a close at d = 2 happens inside a covered round and fails the d ≥ 3 test.
Over every even R ≤ 4096, the trees that fail `Tree.okNC` are exactly those for **R ∈ {2, 4, 8, 16, 24, 32, 48, 64,
176}**: the closing set of the endgame theorem, re-derived through the proved model with coverage by construction
and with "close" decided by proved code rather than by the builder's labels. The trees are then
embedded as data and checked inside a proof (`thm/ExitTheorem.lean`, `thm/EndgameTheorem.lean`, by `native_decide`,
which trusts Lean's compiler in addition to its kernel). **`exit_no_halt` is a Lean theorem:** for all naturals
a, b, c, E with a odd, b even, c odd, E even and every gap at least 390, the machine started from the round start with
walls at a, b, c and width E reaches another round start after some number of rounds (the round at which this
state's run breaks off, cleans the tape or completes a pass) without halting. Its axioms are Lean's three standard
ones and the `native_decide` axiom for the tree check (13 minutes to evaluate over 22,230 leaves). **`endgame_no_close` is a Lean theorem:** for every even
R with 2 ≤ R ≤ 4096 outside {2, 4, 8, 16, 24, 32, 48, 64, 176}, and every phase-0 pass start (walls at a, b and
E − R − 1, width E, a odd, b even, E even, every gap at least 448), the machine reaches a round start without
halting and every end meeting on the way is at distance at least 3 (40 minutes to evaluate over 99,630 leaves; axioms:
the standard three and the `native_decide` axioms). Two limits of the statement, both deliberate: the number of rounds
is existential (it is the round at which the start's pass completes, its chain breaks or it leaves phase 0, chosen per
class by the untrusted builder), and the theorem says nothing about R in the closing set — that those R do close is
shown by the runs above, not by the theorem. A "close" in the Python sense (an end
meeting at d ≤ 2, from which a halt can begin in later rounds) is not the same as `uncovered`: at d = 2 the rules
still cover the round, so the proved model carries on there, and close leaves make no non-halting claim either way.


**End to end (October 27; `../lean/END_TO_END.md`, `../lean/thm/EndToEnd.lean`).** The Lean results now combine into
one statement about the machine on blank tape, `blank_halt_structure`: if it halts, then (1) it first reaches a clean
tape of even width W ≥ 2³² with W/2 in one of the cut classes of a 36-digit clean-tape tree (1,660,016 residue
classes, measure 2.4 × 10⁻⁵) and halts from there; (2) the mark model, run from that clean tape, reaches a stuck
configuration (a close at the right end or an interior contact); (3) every phase-0 pass start it passes with R outside
the closing set is followed by the loop's close-free stretch, and the halt needs a stuck configuration after it, for
every R (`loop_halt_needs_contact`, extending the endgame version beyond R ≤ 4096). (The same holds after every loop
state with the exit stretch, `exit_halt_needs_contact`, but `ExitTheorem` and `EndgameTheorem` both define a top-level
`decodeTree` and cannot be imported together yet.) Read backwards (`never_halts_of_cut_classes`): the machine never halts if no clean tape of width
≥ 2³² in a cut class halts. Three new pieces carry it. *The prefix:* the mark model runs 1,204,297,272 rounds from the
first round start to the clean tape of width exactly 2³² (`native_decide`, 4 minutes as native code). *The clean-tape
tree:* `RTree.okW` checks a route tree over the one number W whose leaves are one-marker clean tapes decided to be
wider than the start; it is the exhaustive check's class tree, proved, and its cut classes grow 1.52-fold per digit
like the exhaustive check's open classes. *The chain:* strong induction on the halting time, since a run to a wider
clean tape takes at least one step (clean tapes of different widths differ in cell W − 1). The two-marker route tree
could not be chained this way: the machine's own run reaches two-marker states with a tiny gap (m = 56 at width
34,478,025), outside any cone of large gaps. Also found: `thm/LoopTheorem.lean` no longer compiled once
`endgame_no_close` gained its `roundsZ` conjunct (the two pull requests merged in that order); fixed, and
`BB6.Sym.sameForm` moved to `SymSplit` so that `Loop` and `RouteTree` can be imported together.


**The exit and loop trees checked by the kernel (October 27; `../lean/thm/ExitPieces*.lean`, `LoopPieces*.lean`).**
`exit_no_halt` and `loop_pass` no longer use `native_decide`: their trees are evaluated by Lean's kernel
(`decide +kernel`), so both rest on the kernel alone (`#print axioms`: `propext`, `Classical.choice`, `Quot.sound`).
Three changes made that affordable. *Skews:* a residue test on a form with several odd coefficients used to be decided
by splitting every coordinate with an odd coefficient; a skew yᵢ = zᵢ + yⱼ (a unimodular change of coordinates,
`cover_skew`) first makes the other odd coefficients even, so one split decides the test. The exit tree goes from
22,230 leaves to 358, the loop tree from 1,327 to 143, the endgame trees from 99,630 to 40,843. *Advances:* `adv n`
runs the n rounds before a split once for the whole class instead of once per leaf (a flag records that the state is
known to be well formed). *Signs from a checked inverse:* `sgn` used to compute and check a Cramer certificate for
every comparison; now an inverse of the gap forms' matrix is checked once per cone (`invCheck`), and a sign needs only
μ = Σ pᵢ uᵢ. One kernel evaluation of a whole tree's check keeps every intermediate term (the exit tree ran out of
16 GB), so the check is cut into subtrees of at most 40 rounds with a theorem each (57 for the exit tree, 25 for the
loop tree), assembled by `Tree.ok_node` and `Tree.ok_skew`; the subtree theorems sit in four modules per tree, which
compile in parallel: 45 s for both trees on 4 cores, about 1 GB each. The endgame trees, still `native_decide`, now
take 14 s instead of 4 minutes. In the kernel they would take about 1.8 hours on one core (117,947 rounds of checks
at 0.054 s each). The trees for the 2,048 values of R are only 57 different trees, repeating with R mod 32 to 256, so a
tree with R as a coordinate (in a residue class and a range) would share that work; it needs order decisions on cones
with more forms than coordinates (the range has two ends). With no decoder left in `ExitTheorem`, it and
`EndgameTheorem` can now be imported together.


**What `loop_no_close` does and does not say: a half pass, and a close after the stretch (October 27).** One of the
1,327 leaves of the loop tree (`thm/loop_tree.txt`) is not a full pass: from a phase-0 pass start with b ≡ 0, E ≡ 2
and R ≡ 0 (mod 4), two rounds (G B W, then G W W W) reach another phase-0 pass start with walls b/2 + 5, (b + E − R)/2
+ 5, E − R/2 + 5 and width E + 6: R′ = R/2, and the left countdown is not divided but replaced, L₁′ = L₁/2 + 35E/2 −
147R/2 − 30. The notes' theorem of October 23 ("R = 16^p·r with r in the closing set, L₁ in fixed classes") assumes
the pass start is followed by G B W and G M B, which excludes this step, so it does not contradict it; but the σ bound
cannot be carried through a half pass, and the Lean statement covers these states too. An example run (`lean --run
../lean/RunWalls.lean 601 11016 20010 5632 23`, model rounds): from the pass start a = 601, b = 11,016, c = 14,377, E
= 20,010 (R = 5,632 = 2·16·176, outside the closing chain) the run makes the half pass to R = 2,816, a pass, a second
half pass to R = 176 (round 10), a pass to a phase-0 pass start with a = 469, b = 10,474, E = 20,058 and R = 22 (round
16; every gap ≥ 448, R outside the closing set), and closes six rounds later (an end meeting at distance 2). That is
consistent with `endgame_no_close` and `loop_no_close`, whose stretch from R = 22 stops before the close (the number
of rounds is existential, chosen by the tree), but it shows what the theorems do not say: a run that leaves a
certified stretch can come back to phase-0 pass starts and close later. The reading "a run through the loop can close
only from a pass start whose R is in the closing set" holds only for the end chain inside each certified stretch.
`thm/EndToEnd.lean` states the loop part accordingly: a halt comes only after the stretch.

**The endgame checked by the kernel, with one tree for every R ≥ 178 (October 27; `../lean/thm/EndgamePieces*.lean`,
`EndgameTheorem.lean`).** `endgame_no_close` no longer uses `native_decide`, and it no longer needs R ≤ 4096: it holds
for every even R ≥ 2 outside the closing set. A tree with R as a coordinate (R = 2y₃, with the cone form R ≥ 178) had
been stopped by a single class, R = 48 + 256z with z ≥ 1, whose round 13 stayed undecided. The open test was a landing
packet's y < m + 3, where m + 3 − y = 2 − 2z is at most 0 on the cone but equal to 0 at z = 1; `sgn` decides only
strict signs, so `ltDec` had no answer. The forms take integer values, so a < b fails exactly when b − a − 1 < 0, and
`ltDec` now tries that second sign when the first is undecided (`ltDec_sound` covers both). The change only turns
undecided comparisons into `some false` and never changes a decided one, so every existing check still passes (trees
with `cut` leaves, like the clean-tape tree, may cut less when they are rebuilt). With it, the tree for all R ≥ 178
(`thm/endgame_sym.txt`, built by `ExploreNC sym 178 448`) is complete with 200 leaves. Two other ideas tried on the
way turned out not to be needed: tightening each cone bound to the next value its form takes at integer points (by
the gcd of its coefficients), and a second inverse for cones with an upper bound on R. The 79 even R < 178 outside
the closing set keep one tree each (`thm/endgame_small.txt`, 1,543 leaves). Together they need 4,948 rounds of
checks instead of 117,947: 306 subtree theorems in four modules, 95 s on 4 cores (about 0.06 s per round, under 1 GB
per module), where `native_decide` took 14 s. `loop_no_close` still goes through `loop_pass` for R ≥ 4097, so its stretch runs through every pass of the
loop. `blank_halt_structure` now rests on `native_decide` only for `prefix_ok` and `clean_tree_ok`.

**Trees built by a proved explorer; the end-to-end statement at every depth (October 27;
`../lean/BB6/RouteExplore.lean`).** The route-tree and clean-tape theorems no longer check a tree that an untrusted
program wrote out. `RTree.explore` and `RTree.exploreW` build the trees inside Lean the way `ExploreRT` and `ExploreCT`
did (rounds one at a time, a split on the first undecided digit with a shear when both coordinates enter it, a stop
at a clean tape, a cut after d splits), and `explore_ok` / `exploreW_okW` prove by induction on the exploration that
every tree they build passes `RTree.ok` / `RTree.okW`. So `route_tree_clean` (for every depth and every cone constant)
and `clean_tree_step` (for every depth) hold with the standard axioms only; no tree is evaluated in a proof, and the
generators, the tree files and the decoders are gone. What the depth changes is only how many classes are cut, and
that is evaluated on its own (`exploreMass`, the same exploration without building the tree, by `native_decide`). It
reproduces the earlier trees: the 36-digit route tree has 407,087 cut and 539,120 clean leaves and the 40-digit one
1,682,946 and 2,266,244, the Python certificate's numbers; the 36-digit clean-tape tree has 1,660,017 cut and
1,507,364 closed leaves (with the integer-aware `ltDec`; 1,660,016 before), and the 40-digit one 9,188,787 and 8,107,467
(measure 9,190,118 / 2⁴⁰ ≈ 8.4 × 10⁻⁶). The end-to-end theorem now reads at every depth: a halt from blank tape needs a clean tape of
width ≥ 2³² that is in a cut class of the clean-tape tree at every depth d (`clean_chain` asks at each clean tape
whether some depth decides it), and with the kernel-checked endgame, `blank_halt_structure` rests on `native_decide`
only for the prefix. The exit stretch is now part of it (`blank_halt_exit`), since `decodeTree` no longer clashes.
(Its loop and exit items, as stated, also hold with zero rounds, since they do not say where the stretch ends; those
statements are being changed to name the end of the stretch. The clean-tape items do not use them.) The
cut classes are the exhaustive check's open classes to within a few (1,930 at 20 digits, 10,722 at 24, 57,934 at 28,
303,560 at 32, 1,660,017 against 1,660,024 at 36). One difference matters for "every depth": a class with a
comparison that comes out differently for its smallest member is cut whatever the depth (7 classes at depth 31 to 35
for the 36-digit tree, measure 76 / 2³⁶ ≈ 1.1 × 10⁻⁹), where the exhaustive check decides the class above a threshold
and runs the members below it directly. At depth 31, for example, the class W = 2 + 2³²z (z ≥ 1) has after 30 rounds
its first marker at 4z, and the round asks whether it is exactly 3 cells from the gap: 4z = 4, true only for
W = 2³² + 2.

**Clean tapes below 2⁴¹ run one by one in Lean; the end-to-end bound raised to 2⁴¹ (October 27;
`../lean/BB6/CleanRange.lean`, `../lean/thm/CleanDirect.lean`, `../lean/thm/EndToEndDirect.lean`).** The same remedy
as the exhaustive check's, proved. `directOK W` runs the mark model from the clean tape of width W (at most 10,000
rounds) until a one-marker clean tape wider than W, `RTree.cuts1` lists the cut classes of a clean-tape tree as
residues of W/2, and `rangeOK_sound`: every clean tape in a range of widths that the tree leaves open passes
`directOK`. Evaluated on the 36-digit tree for [2³², 2⁴¹) (`native_decide`, 26,509,316 clean tapes, about 7 minutes of
native code after the 4.5 minutes of the tree; the longest needs 127 rounds), it gives `clean_step_direct`: every
clean tape of width in [2³², 2⁴¹) reaches a wider one, with no exception. Above 2⁴¹ the chain uses the tree with the
cone W ≥ 2⁴¹, where the comparisons above are decided: `cleanTreeG 2⁴¹ d` has no cut above full depth through 36
digits, and its cut classes are the exhaustive check's open classes (1,930, 10,722, 57,934, 303,560 and
1,660,024 at 20, 24, 28, 32 and 36 digits; at 36 compared class by class). At 40 digits it has 9,188,899 against
9,188,898: the edge moves with the cone. Two leaves at depth 40 have an undecided comparison: in the class
W = 2 + 2⁴¹z the first marker is at 4z after 39 rounds and the test 4z = 4 holds only for W = 2⁴¹ + 2 (the depth-31
example one level below the cone's exponent), and in the class W = 2⁴⁰ + 2 + 2⁴¹z it is at 2 + 4z, where 2 + 4z = 4
is false for every member but true at z = 1/2, inside the cone over the rationals. The exhaustive check, with exact
integer thresholds and direct runs below them, leaves the first open too and settles the second. So `blank_halt_clean_direct`: a halt from blank tape needs
a clean tape of width ≥ 2⁴¹ in the cut classes of that tree at every depth, then a stuck configuration; it adds the
direct runs to what `blank_halt_clean` trusts. "Cut at every depth" is still just the conjunction of its finite-depth
instances, and what carries information is the measure at each evaluated depth.

**The stretches must say where they end (October 27; `../lean/BB6/Ends.lean`, `../lean/thm/EndgameTheorem.lean`,
`LoopTheorem.lean`, `ExitTheorem.lean`).** `exit_no_halt`, `endgame_no_close`, `loop_no_close` and item 3 of
`blank_halt_structure` all had the form "there are n rounds the model covers from the start, without a halt and with
every end meeting at distance ≥ 3". With n = 0 that holds for every start, with no tree at all: `roundsZ fuel 0 ms W =
.newRound ms W`, `steps 0 c = some c` and `meetsRounds fuel 0 ms W = []`; the whole proof of the conclusion of
`endgame_no_close`, with no hypothesis used, is `⟨0, 0, _, _, rfl, rfl, fun _ h => by simp [meetsRounds] at h⟩`.
`loop_pass` had the same problem one round later: its end "not a phase-0 pass start" holds after the first round from
every pass start (the round start is G B W). The trees did certify long close-free stretches, but the theorems did
not say so. The fix is to name where a stretch ends, as facts about the model's run that never hold after zero
rounds (`not_endEvent_zero`, `not_exitEvent_zero`):

- from a phase-0 pass start (`EndEvent`): the run leaves phase 0 (round 1 not G B W, or round 2 not G M B), two
  consecutive end meetings leave the halving chain (d′ ≠ d/2 + 4 for d ≡ 0 mod 4, d′ ≠ (d − 2)/2 for d ≡ 2 mod 4, or
  d odd: `ChainBreak`), or the run is at a phase-0 pass start with a smaller even right end 2 ≤ R′ < R whose next two
  rounds are G B W and G M B (`PassStart`; the lookahead makes it a pass start in fact, not just three walls with the
  right parities);
- from a loop state (`ExitEvent`): a clean tape (only the end marker, at W′ − 2), a chain break, or three walls with
  the loop's parities again after exactly 8 rounds (a full pass).

`Tree.okEnd` checks these at every leaf with proved symbolic tests (`brkDec` decides a break from a decided residue
of d and a nonzero, ordered or odd difference of d′ from the chain's prediction); the chain is read off the proved
end meetings (`meetsRounds`), and the builder (`ExploreNC.lean`, which now also builds the exit tree) classifies
breaks with the same meetings. Results, all evaluated by the kernel with the standard axioms only:

- `endgame_stretch`: the tree for every R ≥ 178 (200 leaves) and one tree for each even R < 178, now including the
  closing set (1,677 leaves; 342 subtree theorems, 143 s on 4 cores). For R in the closing set a leaf may instead be
  a close leaf, and every close leaf shows L₁ in R's class: L₁ ≡ 0 mod 2 (R = 2, 4), 0 mod 8 (8), 0 mod 32 (16),
  32 mod 64 (24), 0 mod 64 (32), 0 mod 128 (48, 64, 176); with `loopL1_mod7` (L₁ ≡ 3 mod 7 for every b, c, E) these
  are the classes 10 mod 14, 24 mod 56, 192 mod 224, 416 mod 448, 192 mod 448 and 640 mod 896 of the October 22
  table. So the table's "L₁ must be" column is now a Lean theorem: from a pass start with gaps ≥ 448, a close before
  the run leaves phase 0, breaks the chain or reaches the next pass start needs R in the closing set and L₁ in R's
  class. The 2-adic parts were all decided by the trees' splits; no close leaf needed a separate argument.
- `loop_stretch`: strong induction on R through the pass starts with every gap ≥ 448 at which the stretches end,
  using only `endgame_stretch` (the loop tree for R ≥ 4097 is no longer needed: the R ≥ 178 tree covers every width).
  Within the loop a close comes only from a pass start whose R is in the closing set and whose L₁ is in that R's
  class; otherwise the run ends at `LoopEnd`, an end event at which it is not at a pass start with every gap ≥ 448.
  The induction goes on from such a pass start whichever end event the tree reports there: a half pass leaves phase 0
  at its second round (G B W, then G W W W), where the run is at a pass start again. A pass start with a gap below
  448 does occur: from the pass start a = 449, b = 926, E = 1504, R = 128 (L₁ = 17,664 ≡ 0 mod 256, the pass class)
  the pass ends after 8 rounds at the phase-0 pass start with walls 393, 1,146, 1,519, width 1,528, R′ = 8 and
  L₁′ = 276 = L₁/64, whose first gap is 393 (`RunWalls.lean 449 926 1504 128 9`). So a pass cannot promise gaps
  ≥ 448, and the induction continues only where they hold. The half-pass example above (`RunWalls.lean 601 11016
  20010 5632 23`) now reads differently: `loop_stretch` follows it through the half pass (round 2, R = 2,816: the run
  left phase 0, but it is at three walls followed by G B W and G M B, a `PassStart`; L₁ = 729,088 = L₁/2 + 35E/2 −
  147R/2 − 30) and the pass to R = 176 (round 10), where L₁ = 11,392 ≡ 640 mod 896 is in 176's class; the close at
  round 23 is the close that class allows. The G W W W with R = 22 at round 16 is not a pass start in this sense (it
  is followed by G B W and G M W), and the end meetings stay on the halving chain from 5,630 down to 2.
- `exit_stretch`: the exit tree is unchanged (358 leaves, the certificate's classes), and every leaf now ends at an
  exit event: 298 chain breaks, 58 clean tapes, 2 full passes.
- `loop_pass` and its tree are retired (`LoopPass.lean`, `LoopPieces*.lean`, `gen_loop.py`, `ExploreLoop.lean`). The
  pass map it stated (R′ = R/16, L₁′ = L₁/64, or R′ = R/2) held only at the leaves where its tree chose to stop at a
  pass start, so it never said that a pass happens. Putting the pass map back as a check on the `PassStart` end is
  what the σ bound needs next, with a way across half passes.

Items 3 and 4 of `blank_halt_structure` (`blank_halt_loop`, `blank_halt_exit`) now read: from every pass start with
gaps ≥ 448 that the run from blank tape reaches, the model covers the close-free stretch through the pass starts with
gaps ≥ 448 to the last of them, and a halt needs a stuck configuration either there, with R₁ in the closing set and
L₁ in its class, or after the run leaves the loop; and from every loop state with gaps ≥ 390 it reaches, the model
covers the exit stretch to an exit event, and a halt needs a stuck configuration after it. (This replaces the
weaker statements of the entry above, which held with zero rounds.)

**The prefix in the kernel, to 2²⁰ (October 27; `../lean/thm/PrefixKernel.lean`, `../lean/thm/gen_prefix.py`).**
The last `native_decide` that is not a tree is `prefix_ok`, 1,204,297,272 rounds from the first round start to the
clean tape of width 2³². Lean's kernel evaluates `roundsZ` at about 600 rounds a second (1.6 to 2 ms a round and
about 200 kB of memory per round inside one theorem, whatever the fuel; a copy of the round with Boolean tests in
place of decidable propositions was only 1.35 times faster), so the full prefix would take weeks. The run to 2²⁰ is
294,033 rounds: `blank_prefix_kernel` checks it in 59 stretches of 5,000 rounds (`(roundsZ 1000 5000 ms W).isRound
ms' W' = true` by `decide +kernel`, 8 modules, 2 minutes on 4 cores) chained by `roundsZ_chain`, with the standard
axioms only. Every power of two from 2¹⁶ to 2³² is itself a clean tape of the run (2¹⁶ after 18,368 rounds, 2²²
after 1,176,058, 2²⁴ after 4,704,284; the rounds grow as 0.28 W), so the prefix can stop at any of them. What a
lower prefix costs elsewhere is the clean-tape tree's cone: at depth 36 the tree leaves cut mass 1,660,086 / 2³⁶ =
2.42 × 10⁻⁵ at cone 2³², 2.45 × 10⁻⁵ at 2²⁴ (174 cuts before depth 36), 2.54 × 10⁻⁵ at 2²² (465) and 2.94 × 10⁻⁵ at
2²⁰ (1,074; measured with `ExploreCT`, and at 2²⁰ again with the proved explorer, below). At depth 20 the trees for
cones 2²⁴ and 2³² are identical; a cone 2^k starts failing near depth k − 1. The early cuts are edge effects: in the
class W = 2 + 2²⁰z (z ≥ 1) a comparison reads 4z = 4, true only at the class's smallest member, and in W = 2¹⁹ + 2 +
2²⁰z it reads 2 + 4z = 4, true only at the rational point z = 1/2. Two of these, at depth 19, carry most of the extra
mass at cone 2²⁰. Dropping a class's smallest member by a direct run (and adding W ≥ W* + 2 to the cone) would remove
both kinds. With the tree's soundness proved for every cone, this prefix is all that an end-to-end theorem without
`native_decide` still needed (next entry).

**End to end in the kernel alone (October 27; `../lean/thm/EndToEnd.lean`, `../lean/thm/CleanKernelMass.lean`).**
`blank_halt_clean_from` now takes the prefix as hypotheses (a clean tape of even width W₀ that the run from blank tape
reaches) and a lower end A for the clean tapes covered in between (`StepsBelow A B`: every clean tape of width in
[A, B) reaches a wider one). With the kernel's prefix to 2²⁰ and A = B = 2²⁰, so that nothing is run in between, the
chain uses the clean-tape tree over the widths ≥ 2²⁰ from the first clean tape on: `blank_halt_clean_kernel`,
`blank_halt_structure_kernel` and `never_halts_of_cut_classes_kernel` hold with `propext`, `Classical.choice` and
`Quot.sound` alone. Every tree in them is either checked by `decide +kernel` (exit, endgame) or built by the proved
explorer (clean tapes), and the prefix is checked by `decide +kernel` in stretches; no compiled code is trusted. They
say what `blank_halt_structure` says, except that the clean tape a halt needs is only known to be at least 2²⁰ wide,
in the cut classes of the tree over the widths ≥ 2²⁰ at every depth. At 36 digits those are 1,653,905 classes of
measure 2,018,149 / 2³⁶ ≈ 2.9 × 10⁻⁵, against 1,660,017 of measure 1,660,086 / 2³⁶ ≈ 2.4 × 10⁻⁵ from 2³²: fewer
classes, but 1,074 of them cut above full depth (7 from 2³²), 2 at depth 19 (measure 262,144 / 2³⁶) and the others
from depth 22 to 35 (103,174 / 2³⁶; 1, 4, 3, 3, 13, 14, 14, 23, 30, 53, 106, 179, 290 and 339 at depths 22 to
35). So the edge of the cone W ≥ 2²⁰ is not one pair of classes, as it is at depth 31 for 2³² and at depth 40 for
2⁴¹, but a band of classes near the cone's bound. The direct run of a class's smallest member would remove it, and
should bring the kernel-only theorems' measure down to about that from 2³² (with `ExploreCT`, 1,660,100 / 2³⁶ at cone
2²⁰ and 1,660,557 / 2³⁶ at 2¹⁶ when every early cut drops its smallest member and goes on).

**The σ bound in Lean (October 27; `../lean/BB6/Ends.lean`, `../lean/thm/LoopTheorem.lean`, `LoopHalt.lean`,
`EndToEnd.lean`).** First a native test of the endgame trees as they were: of their 1,877 leaves (200 for R ≥ 178,
1,677 for R < 178), only three end at a pass start by `passStartCheck`, all at round 8: one in the tree for R ≥ 178,
one for R = 128, and one for R = 64 inside R = 64's closing class (the pass coset L₁ ≡ 0 mod 256 lies in 0 mod 128).
All three satisfy the pass map as identities of forms, 16 R′ = R and 64 L₁′ = L₁. Every other leaf ends at
`LeftPhase0` (round 1 or 2) or at a chain break, or shows L₁ in the closing class of its R. So the pass map became
part of the end event: `PassStart fuel R L ms W` now requires 16 R′ = R and 64 L₁′ = L (R′ < R follows), and
`passStartCheck` checks both with `sameForm`. The tree for R ≥ 178 now carries its real L₁ form (`symStartE`; it
carried 0, since no closing class needs it there). The 342 endgame subtree checks pass unchanged in the kernel
(2 min 17 s for them and the exit pieces on 4 cores), and the builder `ExploreNC` (which now stops a leaf only at a
full pass) rebuilds the three tree files byte for byte.

`loop_stretch` now follows the run through full passes only: it goes on from an end state that is a `PassStart` (with
the map) with gaps ≥ 448, and returns the number p of passes, with R = 16^p R₁ and L₁ = 64^p L₁′ (`passL1` is the left
countdown of a three-wall round start). Two other kinds of leaf come back to three walls with the phase-0 parities
(a survey of all leaves; each map below is an identity of forms at its leaves):
- 44 half passes (the tree for R ≥ 178 and R = 8, 12, …, 176): from a pass start of the other phase, followed by
  G B W and G W W W, the leaf is `LeftPhase0` at round 2, with R′ = R/2, W′ = E + 6, 2 L₁′ = L₁ + 35E − 147R − 60 and
  a ≥ 448;
- 12 chain breaks at round 7 (the tree for R ≥ 178 and R = 12, 28, …, 172): W′ = E + 24,
  R′ = (4E + 4R − b + 110)/32 and 96 L₁′ = L₁ + 1120E + 1666R + 50328. In the small trees R′ ≥ R: the right end is
  set again by the width, not divided. Whether a ≥ 448 is not decided there.

The loop's run ends at both (`LoopEnd`). Where the run lands on a pass start with gaps ≥ 448, that is a start of its
own in `blank_halt_loop`, and σ is measured there, at the first pass start of a stretch of full passes. Then:
- `sigma_close`: at a pass start in a closing class, R³/L₁² ≤ 176³/256² (with L₁ ≡ 3 mod 7 the classes give
  |L₁| ≥ 4, 4, 24, 32, 32, 192, 256, 256, 256 for R = 2, 4, 8, 16, 24, 32, 48, 64, 176);
- `sigma_passes`: a pass multiplies R³ and L₁² by the same 4096 (as a statement, R → 16R and L₁ → 64L₁ keep
  `SigmaOK`);
- `sigma_through_passes`: a close through the loop needs R³/L₁² ≤ 176³/256² at the first pass start, which is
  log₂W ≤ σ + 6.38 (log₂W = σ + 3 log₂R − 2 log₂|L₁|);
- `loop_halt_sigma`, `blank_halt_sigma`: from a pass start with gaps ≥ 448 beyond the bound, a halt comes only after
  the loop's end, and needs a stuck configuration there. Standard axioms only.

The bound is attained: from walls 601, 1,630, 9,323 and width 12,140 (R = 2,816, L₁ = −16,384, so R³/L₁² = 83.1875 =
176³/256² exactly) the run makes the full pass G B W, G M B, G M W W, G M B, G M W W, G W W W, G B W, G W W W to
walls 2,895, 8,798, 11,987, width 12,164 (R = 176, L₁ = −256), and closes 13 rounds later, at round 21 (`lean --run
../lean/RunWalls.lean 601 1630 12140 2816 24`). What the theorem does not say: it bounds where a close through the
loop can start, not σ itself. How late a run can enter the loop is what the σ ceilings of the route tree measure, and
they are evaluated, not proved; a run that leaves the loop can also come back to a pass start later (above).

**The edge of the cone: the smallest member run directly (October 27; `../lean/BB6/CleanTree.lean`,
`../lean/BB6/RouteExplore.lean`).** The edge classes of the clean-tape entries above come from the cone being a
condition over the rationals: a class of W/2 modulo 2^k is compared at the cone's corner, which can lie between two of
its members, so a comparison that comes out differently only for the smallest member, or only below it, is undecided
on the class, and no residue split separates that member from the rest. The clean-tape trees now do there what the
exhaustive check does: run the member. A new node, `drop z`, runs the member y₀ = z with the mark model to a wider
one-marker clean tape (`toWider`, at most 10,000 rounds; moved from `CleanRange`) and goes on with the rest of the
class under the cone y₀ ≥ z + 1, whose corner is a member. `RTree.okW` checks it (`dropOK`: a cone form excludes the
members below z, the forms do not depend on the unused coordinate, and the direct run gets there), `RTree.soundW`
covers it, and `cutMem` counts the dropped member as not cut, so every theorem keeps its statement; `RTree.ok`, for
the two-marker route tree, rejects the node. `RTree.exploreW` drops where a round is undecided and no residue split
decides it, at most 4 members in a class, the children of a split starting afresh: a budget of 4 per path left one
class cut at depth 35, because the clean tapes W = 2ʲ + 2 need a drop at every level. With the drops the trees with
the cones W ≥ 2²⁰, 2³² and 2⁴¹ are the same at every depth evaluated (1,930, 10,722, 57,934, 303,560, 1,660,024 and
9,188,898 cut classes at 20, 24, 28, 32, 36 and 40 digits), every cut leaf is at full depth with a residue split still
to make, and the cut classes are the exhaustive check's open classes, compared class by class at 36 and 40 digits
(with the cone 2²⁰ at 36). The members dropped: 20 at 36 digits from 2³² (W = 2ʲ + 2 for j = 32 to 37, W = 3·2ʲ + 2
for j = 31 to 36, the classes that held 2ʲ⁺¹ + 2 dropping both, and 8 others from W = 15,858,340,778 up), 72 at 40
digits; 2 at 40 digits from 2⁴¹ (W = 2⁴¹ + 2, after which its class stays open at depth 40 as in the exhaustive check,
and 3·2⁴⁰ + 2, after which its class closes); 1,599 at 36 digits from 2²⁰, in 1,597 classes, from W = 2²⁰ + 2 up. No
class needs more than two. So the kernel-only theorems lose nothing to their lower cone, and "open at every depth" no
longer contains classes that are open for a reason of method. The direct runs below 2⁴¹ (`clean_step_direct`) now take
the 26,508,327 members of the 1,660,024 classes, at most 127 rounds each (more than half take 45 to 51).

**The loop's chain in Lean (October 27; `../lean/BB6/Ends.lean`, `../lean/thm/LoopTheorem.lean`, `LoopHalt.lean`,
`EndToEnd.lean`).** The half passes and round-7 breaks above ended the loop's run. Now the end event states all three
steps with their exact maps, and the run is followed through every landing:
- From a pass start of width E with right end R and left countdown L₁ the end event (`EndEvent`) is: the run left
  phase 0 or the halving chain, at a round start that is not three walls (`NotWWW`); or it is at a landing
  (`Landing`): three walls with a odd, b even, W′ ≡ 0 (mod 4) and R′ even, at least 2, with one of three maps
  (`StepMap`): a full pass (8 rounds; 16 R′ = R, 64 L₁′ = L₁, W′ = E + 24), a half pass (2 rounds, from
  E ≡ 2 mod 4; 2 R′ = R, 2 L₁′ = L₁ + 35E − 147R − 60, W′ = E + 6) or a chain break at round 7 (4704 R′ =
  476E + 980R − L₁ + 15984, 96 L₁′ = L₁ + 1120E + 1666R + 50328, W′ = E + 24). The two lookahead rounds of the old
  `PassStart` are gone, and the tree checks carry the start's width as a third form (`SForms`). The 342 endgame and
  57 exit subtree checks pass in the kernel with it (154 s on 4 cores; the trees are unchanged), so the two mod-4
  facts (a half pass starts from E ≡ 2 mod 4, every landing has W′ ≡ 0 mod 4) are checked now, not only observed.
- `LoopChain` lists the steps from pass start to pass start, each landing with gaps ≥ 448. `loop_chain_halt`: if
  the machine halts from a pass start with gaps ≥ 448, its run follows the chain to its last pass start, where it is
  in a closing class or goes on close-free to the chain's end (`LoopEnd`: a round start that is not three walls, or
  a landing with a gap below 448), and the halt needs a stuck configuration after that. A round-7 break can raise R,
  so the induction is on the halting time; a step takes at least one machine step because the width grows and
  three-wall round starts of different widths differ at cell W′ − 1 (`passStart_ne`).
- A half pass is only ever the first step (`LoopChain.half_first`): every landing has W′ ≡ 0 mod 4.
- σ: a chain that ends in a closing class has R³/L₁² ≤ 176³/256² at the start of its last run of full passes
  (`LoopChain.sigma`). At a round-7 landing 32 R′ = 4E + 4R − b + 110 ≥ 3E + 5R + 559 and
  96 L₁′ = 147b + 1008E + 2058R + 50142 ≤ 1155E + 1911R − 15861 (b ≤ E − R − 449), so with S = 3E + 5R,
  32 R′ ≥ S and 96 L₁′ ≤ 385 S, and the bound there needs 18432 S ≤ 176³ · 385², that is S ≤ 43,841,661 and
  E ≤ 14,613,887 < 2²⁴ (`break7_sigma`; the worst case is R small and b near E − R, where R′ ≈ 3E/32 and
  L₁′ ≈ 12E). Widths only grow along the chain, so from a pass start of width ≥ 2²⁴ a chain that ends in a closing
  class has no round-7
  break: it is p full passes (R = 16^p R₁, L₁ = 64^p L₁′), or one half pass from W ≡ 2 mod 4 and then p full passes
  (R = 2 · 16^p R₁, 2 · 64^p L₁′ = L₁ + 35W − 147R − 60) (`LoopChain.close_wide`, `loop_halt_wide`,
  `blank_halt_wide`). From a pass start beyond the bound, a close through the loop needs a half pass or a round-7
  break on the way (`loop_halt_sigma`, `blank_halt_sigma`). Standard axioms only.

**Wide landings keep their gaps (October 27; `../lean/BB6/Ends.lean`, `../lean/thm/LoopTheorem.lean`, `LoopHalt.lean`).**
The chain ended (`LoopEnd`) either where the run leaves three walls or at a landing with a gap below 448, from which
the trees do not follow it. The second kind is an end of the formal chain, not of the loop. The landing's first wall
was not part of the end event, so nothing said when it happens. It is now (`StepWall`), read off random landings
through the proved model (`roundZ`) and then checked by the kernel at every landing leaf of the endgame trees. With
c = E − R − 1:
- full pass: 64a′ = b + 4c + 12E + 678, and from L₁′ the middle wall 64b′ = b + 8c + 40E + 1258;
- half pass: 2a′ = b + 10, 2b′ = b + c + 11;
- round-7 break: 16a′ = b + c + E + 135, 32b′ = 3b + 6c + 10E + 452.
The fit was exact on 60,000 landings at widths 2¹¹ to 2²¹ (three-wall round starts with the phase-0 parities at
rounds 2, 7 and 8 that satisfy none of the three step maps were set aside; they are not landings of the chain, whose
landing leaves all satisfy a step map). So from a pass start
of width E ≥ 2¹³ with every gap ≥ 448, every landing is again such a pass start (`landing_wide`). A full pass needs
E ≥ 2,334 for a′ ≥ 448, a round-7 break E ≥ 6,138. The exception is a half pass from a start whose middle wall is
within 896 of the end: its landing's last gap is (E − b)/2, and E − b ≤ 895 needs R ≤ 446. A half pass is only ever
the first step, so from a pass start of width ≥ 2¹³ (with b + 896 ≤ E when E ≡ 2 mod 4) the chain ends only where the
run leaves phase 0 or the halving chain at a round start that is not three walls (`loopEnd_wide`). `loop_halt_leaves`
puts this together with `loop_halt_wide`: from a width ≥ 2²⁴, a halt through the loop closes from a closing class
reached by p full passes after at most one half pass, or the run leaves three walls and the halt comes after that.
Below 2¹³ the exception is real: from walls 449, 926, 1,375 and width 1,504 a full pass lands at 393, 1,146, 1,519.

*After the loop* (untrusted, `roundZ` through `lean --run`). From 100,000 random pass starts of width about 2²⁰, the
run reached a one-marker clean tape every time, without a close: in 3 to 58 rounds, median 6, with a tail falling
about 0.8-fold per round (through repeating shapes such as G M M M, G W M M, G M M). About 14% of the runs pass a
three-wall round start on the way.

**Past the chain's end: pass-start trees (October 27; `../lean/BB6/PassTree.lean`, `../lean/thm/PassHalt.lean`,
`../lean/PassStats.lean`).** The endgame trees stop where the loop's chain ends. A pass-start tree follows the run on
from the pass start, one round at a time, to the next checkpoint: a landing of the chain reached with every end meeting
on the way at distance ≥ 3 (a step of `LoopChain`), or a one-marker clean tape decidedly wider than the start. The
rounds past the chain need more digits of the start, so the trees have cut leaves, and like the clean-tape trees they
are built by an explorer proved to build only trees that pass their check (`PTree.explore_ok`): `pass_next` holds at
every depth with nothing evaluated. `pass_halt_chain` chains the checkpoints by induction on the halting time: a halt
from a pass start of width ≥ 2¹³ (with b + 896 ≤ W when W ≡ 2 mod 4) follows the chain through every landing
(`landing_wide`) to a last pass start that is in a closing class (and a stuck configuration follows), or in a cut leaf
of its tree at every depth, or from which the run reaches a wider clean tape of even width and halts from it in fewer
steps. That is the shape the clean-tape trees' induction needs at a loop entry.

*Distance 2 is not a close.* The first version cut a path at every end meeting below distance 3, as the endgame trees
do. But in the closing classes the endgame trees' close is an end meeting at distance 2 after which the round model
goes on to a new round start (R = 4 in round 2, 8 in round 3, 16 in round 5, 32 in round 8, 24 in round 9, 48 in round
11), and so is R = 6's in round 5. The trees now run on through such rounds with a flag for whether the path so far is
close-free; only a close-free landing is a `land` leaf, and past any other landing the tree runs on to a clean tape. A
path ends at a decided round only where the model decides the round as something other than a new round start: a
halt, or the close at distance 0, which the model leaves uncovered. That took R = 22's cut measure at 16 splits from
17% to 5%.

*Some pass starts halt.* Those decided ends are real. 1/8 of the pass starts with R = 6 (outside the closing set) leave
phase 0 at round 2 (G M W), meet the end at distance 2 in round 5 and at distance 0 in round 7, at every width (in
the model, 5 of 48 random ones of width about 2²⁰). Run on the machine itself, every such start tried halts: from walls
743, 1,802, 3,319 and width 3,326 after 11,362,209 steps, and all 49 of the class among 400 random R = 6 starts of
width below 8,400 (a C and a Python simulator from `roundStart` as defined in `BB6/Marks.lean`). Of 40 random pass
starts of width below 4,300 for each R, 14 halt with R = 4, 3 with R = 6, 7 with R = 8, none with R = 10, 22 or 64.
The closing set describes closes within the chain; after the run leaves it a small R can still close. (The 100,000
starts above drew R uniformly up to W/2, where R = 6 practically never comes up.) So the pass-start trees' cut classes
do not shrink to nothing, and what `pass_halt_chain` says is that a halt through a pass start needs one of them, a
closing class, or a clean tape after it.

*Measures* (`PassStats.lean`, fractions of a start class). At 16 splits the cut leaves hold 4.8% of a class R < 178 on
average: 4.2% where the depth ran out, 0.5% at a round left undecided with no undecided residue found (a marker at 2 +
4(y₁ + y₂), next to the gap, where the rational cone does not know that a well-formed round start has its first mark at
4 or beyond), and 0.1% at a decided halt (R = 6's eighth). Landings take 12%, clean tapes 81% and close leaves 1.6%. For
R ≥ 178 the cut leaves hold 8.8%. At 20 splits they hold 2.4% for R < 178 (1.6% at the depth, 0.7% at an undecided
round, 0.1% at the decided halt) and 4.1% for R ≥ 178: the depth cuts shrink, and the undecided rounds, which are final
leaves, grow slowly.

**Route exclusion: the loop entries of the route tree cannot close (October 27; `../lean/BB6/RouteEntry.lean`,
`../lean/BB6/EntryTree.lean`, `../lean/thm/RouteEntryHalt.lean`, `../lean/ROUTE_TREE.md`).** The route tree in Lean
followed the loop's passes like any other rounds, splitting on R's digits until its depth ran out, so most of its cut
classes were runs inside the loop. A second tree stops a path at the first round start from which no member of its
class closes through the loop, decided on the class:
- The entry check (`entryOK`): a phase-0 pass start (three walls, a odd, b even, W even, R = W − c − 1 even and at
  least 2) with every gap ≥ 448 and width ≥ 2²⁴, so that by `loop_halt_wide` a close through the loop is p full passes
  after at most one half pass. After p full passes a close needs R = 16^p·r with r in the closing set {2, 4, 8, 16,
  24, 32, 48, 64, 176} and L₁ = 64^p·ℓ with ℓ in r's class and ≡ 3 (mod 7) (`loopL1_mod7`). R and L₁ are affine on the
  class; the check bounds L₁ between two affine functions of R on the cone (slopes and offsets computed from the ratio
  L₁/R along the cone's edges and at its corner, then only checked), so at a close ℓ lies in a window of width about
  (β − α)·r/4^p. Beyond a computed P only ℓ = 0 fits, and 0 is not ≡ 3 (mod 7); below it each candidate (p, r, ℓ)
  fixes the point by Cramer's rule, and the check shows that it is not an integer point of the cone. From W ≡ 2
  (mod 4) the same check runs on the forms after a half pass (2R′ = R, 2L₁′ = L₁ + 35W − 147R − 60).
- A seventh kind of node, `entry`, checked by a given test (`RTree.okE`, sound by `RTree.soundE`); the explorer
  `RTree.exploreE` is proved (`exploreE_okE`), so `route_tree_entry` holds at every depth and cone constant with
  nothing evaluated: from every two-marker state with both gaps ≥ Γ, a halt-free run to a clean tape or to an entry
  that cannot close, unless the start is in a cut class. With `loop_halt_wide`: `entry_halt`, `route_halt` and
  `blank_halt_route`, a halt from such an entry needs the loop's chain to end without a close (`LoopEnd`) and a stuck
  configuration after it. Standard axioms only.
- At Γ = 2²⁶: 101,855 cut classes at 36 digits instead of 407,087 (measure 1.48 × 10⁻⁶), 357,237 at 40 instead of
  1,682,946 (3.25 × 10⁻⁷); 5,981 and 21,123 entries, 0.84 % of the start class at both depths. Every pass start the
  tree meets passes the check except 94 at 36 digits (measure 401 / 2³⁶), where a gap of 448 is not decided on the
  whole class; the other cut classes' runs meet no three-wall round start within the depth: they are the deep routes
  outside the loop. So the σ ceilings ("Route ceilings", October 23) are not needed for the entries the tree reaches:
  from them the loop cannot close at any width. The tree with entries is also faster to build (66 s at 36 digits and
  230 s at 40, against 233 s and 16 min).

**The clean tapes' loop entries (October 27; `../lean/BB6/CleanEntryTree.lean`, `../lean/thm/CleanEntryHalt.lean`,
`../lean/END_TO_END.md`).** The clean-tape tree (the class tree over W/2 of the exhaustive check, in Lean) now stops a
path at the same loop entries as the route tree:
- The entry check on the clean-tape tree's classes, which have one coordinate: R = 16^p·r fixes the class's point
  directly (`solveOut1`), where the route tree's two coordinates need Cramer's rule. Both trees' entries now also ask,
  when W ≡ 2 (mod 4), for the middle wall at least 896 below the width: then a half pass at the start lands on a pass
  start with every gap ≥ 448 again (`landing_wide`), so from the entry the loop's chain reaches no closing class
  (`EntryNoClose.no_close`) and ends where the run leaves phase 0 or the halving chain at a round start that is not
  three walls (`entry_halt`, now from `loop_halt_leaves`). The test never fails at the trees' entries at 32 and 36
  digits.
- `clean_tree_entry_step` (every depth, nothing evaluated): from every clean tape of width W ≥ Γ, a halt-free run to a
  wider clean tape or to a wider loop entry that cannot close, unless W/2 is in a cut class. `clean_entry_chain` chains
  these steps by induction on the halting time, with the step and what a halt from an entry needs as hypotheses (a
  property of the entry, or a wider clean tape reached from it, from which the chain goes on), so a theorem that
  follows the run past the loop's end plugs in directly. `blank_halt_clean_entry`: a halt from blank tape needs a clean
  tape of width ≥ 2⁴¹ cut at every depth, or such an entry from which the loop's chain ends without a close where the
  run leaves three walls; `blank_halt_clean_entry_kernel` is the same from 2²⁰ with the kernel alone (the plain tree
  below 2²⁴, where the entries' width test is decided on few classes, and the tree with entries above).
- Over the widths ≥ 2⁴¹ the cut classes at 36 digits fall from 1,660,024 to 1,255,963 (measure 1.83 × 10⁻⁵); 28,660
  entries carry 0.13 % of the clean tapes, nearly all of it met within 32 splits (5,423 entries, the same measure, at
  32 digits). The cut classes still grow about 1.52-fold per digit, and none of their runs meets a three-wall round
  start within the depth (`EntryStats.lean`): the loop's entries are settled, and what is left are runs that stay
  outside the loop for 36 digits.

**From blank tape past the loop's end (October 27; `../lean/thm/PassEntryHalt.lean`).** `pass_halt_chain` is what a
halt from a loop entry needs in `clean_entry_chain`. A loop entry that cannot close (`EntryNoClose`) is a pass start of
width ≥ 2²⁴ with every gap ≥ 448 and, when W ≡ 2 (mod 4), the middle wall ≥ 896 below the width, which is what
`pass_halt_chain` asks for. Of its three ends, the closing class is out there (`EntryNoClose.no_close`), which leaves a
last pass start of the chain cut at every depth of its pass-start tree, or a wider clean tape that the run reaches and
halts from (`entry_pass_halt`). So `blank_halt_pass` follows the whole run from blank tape: a halt needs a clean tape
of width ≥ 2⁴¹ in a cut class of the clean-tape tree with loop entries at every depth, or a pass start wider than 2⁴¹
in a cut class of its pass-start tree at every depth, reached along the loop's chain from such an entry, and it halts
from there; `blank_halt_pass_kernel` is the same from 2²⁰ with the kernel alone. Unlike the clean-tape tree's cut
classes, the pass-start trees' do not shrink to nothing (1/8 of the pass starts with R = 6 halt), so what is open is
which pass starts the run reaches: the last pass starts of loop chains from the clean-tape tree's entries. At every
one of those entries R is affine in the class's coordinate with a nonzero coefficient (28,660 entries at 36 digits,
`EntryStats.lean`), so the chains end at R₁ < 178 only at isolated members, and otherwise in the tree for R ≥ 178.

**Cleaving the cone's edge (October 27; `../lean/BB6/PassTree.lean`, `../lean/PassStats.lean`).** The pass-start
trees' cuts at a round left undecided, with no undecided residue to split on, were the one kind of cut that more depth
did not shrink (0.5% of a class at 16 splits, 0.7% at 20). Traced at 14 splits for R = 10, 22, 42, 74 and 158
(untrusted, a copy of the symbolic round that reports where it stops), all 189 such leaves stop at the round's first
event, where the first mark's position p is compared with the gap at 1: p − 4 = 2, p − 4 = 0 or p < 4. Asked of z3 on
the integer points of each leaf's cone, 146 of them (77%) are genuine: the members with the smallest p take the other
branch, and no residue separates them from the rest. In the other 43 no integer point of the cone does (15 equalities,
which `eqDec` decides only over the rationals, and 28 order tests that `ltDec`'s rounding to integers decides in one
direction only).

A new node, `cleave i c σ j0 j1`, splits such a class at the bound of a coordinate on the cone's integer points. The
check asks that σ(yᵢ − c) ≥ 0 be decided on the class (by `ltDec`, which rounds to integers), then goes on with the
slice yᵢ = c, where coordinate i is fixed and cone form j0 is dropped (one coordinate less), and with the rest, where
cone form j1 is replaced by σ(yᵢ − c) ≥ 1. The soundness proof needs only that every point of the class lies in one of
the two (`inCone_pin`, `inCone_set`), and `cutMem` sends a point to the slice when yᵢ = c, so `PassCut` keeps its
shape. The explorer brings p onto the class's last live coordinate by Euclid steps (skews with any multiplier), finds
its bound by bisection, gives up the cone forms whose loss still leaves the next round decided where one does, and
makes at most 8 cleaves on a path (`passCleaves`). It is proved like the rest (`explore_ok`), so `pass_next` and
`pass_halt_chain` hold as before, at every depth with nothing evaluated.

Measures (`PassStats.lean`, fractions of a start class; the slices have measure 0, and their leaves are counted apart):
at 20 splits the cut leaves hold 2.0% of a class R < 178 on average (1.8% where the depth ran out, 0.14% at R = 6's
decided halt, 4 × 10⁻⁶ at rounds that no cleave decides), against 2.4% before, and 3.8% for R ≥ 178, all of it where the
depth ran out, against 4.1%; at 16 splits 4.6% and 8.8%; at 24 splits 1.6% for R ≥ 178 (5 × 10⁻⁶ undecided): the depth
cuts fall about 0.8-fold per split. The 175,107 cleaves at 20 splits in the trees for R < 178 have 391,807 leaves in
their slices, half of them cut (a slice goes on to the same depth as its class). A budget of 16 or 32 cleaves on a path
leaves the undecided rounds where they are: those few classes are ones where no cleave applies, not ones that ran out of
cleaves.

**The open cases do not run through the extra-wall loop (October 27, evening; `../lock/ShapeStats.lean`,
`../lock/PassShapes.lean`, `../lock/LOCK_NOTES.md` section 6).** The lock for the extra-wall loops was meant to settle
what `blank_halt_pass` leaves open. Two untrusted drivers walk the clean-tape tree with loop entries and the pass-start
trees (with their cleaves) step by step as the proved explorers build them, and record the round shapes on every cut
path. Of the 1,255,963 cut classes of the clean-tape tree at 36 digits (Γ = 2⁴¹), 1,098 (0.09%) meet the extra-wall
pass start `G W W W W` anywhere on their path, and 1,061,623 (85%) never hold more than two walls in a round start.
Nearly all the paths have 32 to 63 rounds, about one per digit, and they stop at two- and three-mark rounds (`G M M`
41%, `G B` 15%, `G W M M` 13%, then `G M W M`, `G W M M M`, `G M B`, ...). In the pass-start trees at 20 splits, four
walls carry 0.95% of the cut measure for R ≥ 178 and 0.82% for R < 178 (apart from R = 6's decided halt, which never
meets them). So no lock for those loops can settle either case, and with the hand-built mixed halts no lock covers
the loop's mixtures anyway. What keeps the classes open is long runs of two- and three-mark rounds: the class tree's
own growth (about 1.52-fold per digit, 101,837 cut classes at 30 digits and 1,255,963 at 36), which "Summary of the
right-end theory" (item 4, "Why verification is expensive") puts down to returns to a GMM state, each costing about
3.5 digits, not to closeness to the end.

**No small right end past the loop (October 27; `../lean/BB6/SmallEnd.lean`, `../lean/thm/SmallEndHalt.lean`).** The
pass starts that `blank_halt_pass` leaves open include real halts, all with small right ends (1/8 of R = 6; in a sample,
uncovered rounds only for R in {4, 6, 8, 16, 32, 48, 64}). The run from blank tape reaches no pass start with R < 178
past a loop entry. A run of full passes ends at r < 178 only if R = 16^p·r and L₁ = 64^p·ℓ with ℓ ≡ 3 (mod 7), so
|ℓ| ≥ 3; full passes keep R³/L₁² (16³ = 64²), which there is r³/ℓ² ≤ 177³/9 ≈ 2¹⁹·²⁰. So R³/L₁² above that keeps the
small ends out for good, and a round-7 break supplies it: from a width E ≥ 2³⁷ it lands with 32R′ ≥ S = 3E + 5R and
0 < 96L₁′ ≤ 385S, so R′³/L₁′² ≥ S/527,023 > 177³/9 (with E ≥ 2³⁶ the margin is gone). A half pass is only the first
step. So the chain from a pass start of width ≥ 2³⁷ from which no run of full passes ends small, nor one after a half
pass, ends at R ≥ 178 (`LoopChain.small_end`).

At the clean-tape tree's loop entries R and L₁ are affine in the class's coordinate z, so R³/L₁² grows like z. At 36
digits over the widths ≥ 2⁴¹ (untrusted, from a dump of the entries' forms): R³/L₁² > 177³/9 at every member of 28,516
of the 28,660 entries; the other 144 (0.11% of the entries' measure) fall short only below widths of 2⁴³·⁵, at 933,158
members in all. Checked exactly instead (for each p and each r < 178, R = 16^p·r fixes z; is it an integer point of the
cone with 64^p dividing L₁ there?), no member of any entry ends small, with or without a half pass. The check is
`smallOK` in Lean, with the linear bounds of `exclCert` for the passes beyond P, and it goes into the clean-tape tree's
entry test (`cleanSmallOK`, `cleanTreeGS`), so `clean_tree_small_step` holds at every depth with nothing evaluated; at
36 digits the tree has the same counts as `cleanTreeGE` (1,255,963 cut classes, 28,660 entries;
`../lean/thm/CleanSmallMass.lean`). `blank_halt_small`: a halt from blank tape needs a clean tape of width ≥ 2⁴¹ cut at
every depth, or a pass start wider than 2⁴¹ with R ≥ 178 cut at every depth of `passTreeSym`, whose cuts at the depths
measured are all depth cuts, none at a round decided as a halt, falling with depth (8.8%, 3.8% and 1.6% at 16, 20 and 24
splits); `blank_halt_small_kernel` is the same from 2²⁰ with the kernel alone (the plain tree below 2³⁷). What stays
open past the loop is that tree's depth cuts, on the lines of pass starts that the clean tapes' classes lead to.

*What the checkers trust.* The mark rules (each proved from the transition table in `proofs.py`, with the contact
conditions under which they hold); exact rational arithmetic; and nothing from the explorers except the leaf lists,
which they treat as claims. The one thing a reader has to accept beyond the rules is the 2-adic bookkeeping itself:
that a residue class of (a, b, E) on which every digit test is decided and every comparison has a fixed sign follows
one sequence of rules, so one symbolic run settles the whole class. That is the content of the checkers' loop.

*Found on the way.* The first version of the exit checker (and the C explorer in `exit` mode) never asked whether an
end meeting at a non-constant distance d = (R + k)/2^j could already be a close; both apply the swap or merge rule and
go on, which is right only for d ≥ 4. The checker now decides d ≥ 4 on the cone like every other comparison and
records its margin: that is where the exit certificate's threshold on R + 1 (241 cells) comes from, and it is exactly
what keeps the exit certificate from contradicting the closes at R = 64 and 176 that the endgame certificate finds.
Without that test the threshold read 49, which would have been a false proof that R = 176 cannot close.

The older summary, kept for the record:
Not provable from the rules alone: runs that pass through the extended loops can chain several loop stretches, each
with a fresh left countdown, and hand-built tapes of width 2^1000 do halt this way; so do three-number tapes of width
2^120 and 2^200 that end with a drop into the plain loop. Also open: positions near the left end and contacts.
With those, a run is at most about (2/3)·log₂E + 20 meetings, which rules out a halt above roughly n = 2^68; the
exhaustive check covers n < 2^55. Counted with the measured constants (a run's first meeting at most about 5 halvings
below the width, at most 6 lead-in meetings from the main run-start shapes, 4p ≤ (2/3)(log₂E + 8.1) from the lock, at
most 8 exit meetings), a run makes at most (2/3)·log₂E + 24 halvings against the log₂E − 1 a halt needs, so the
window a halt could hide in, if the run structure holds, is 2^55 < n < 2^76. The record runs use far less of this
allowance: 24.1 halvings at 84 digits, where the bound is about 80.
The cleanest form of what remains (October 20): every halt starts from a GMM state whose own segment halts, so it
would suffice to show that the set H of such states contains no state the machine reaches. The stronger universal
statement H = {(4, 13)} is a property of a fixed two-number family; it is checked for every GMM state up to width
262,143 and has heuristic odds of about 99%.

**What this changes.** Long runs are not a random walk over many patterns; they are one loop, and its cost is exact.
A halt needs about log2(n) meetings, which through this loop needs a b-digit n to meet 2.5 conditions per meeting. A
proof that runs are bounded would need to show that every entry line stays a bounded 2-adic distance (relative to its
depth) from the target. That is not proved.
