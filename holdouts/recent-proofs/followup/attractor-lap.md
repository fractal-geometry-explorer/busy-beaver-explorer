# attractor-lap: the PR 78/79 lap technique on three G01/G10 holdouts

Technique (techniques/attractors.md): run an exact accelerated simulation until the run locks into a regime where
one lap of macro steps maps a configuration family C(x) to C(f(x)) with f affine (in counts and in ghost
geometric sums such as 2^L), every branch the lap takes (positivity, parity) being the same for all x in a band
that f maps into itself; then check the lap symbolically and prove it.

Evidence levels used below: **computed** = exact accelerated run (Python, tested against direct simulation),
**fitted** = the list map of the repo (checked against the machine, not proved), **observed** = a pattern read off
computed data. Nothing here is proved; no lap closed, so no Coq/Lean file was written.

## Tools (all in this directory)

| file | what it does |
|---|---|
| `wordsim.py` | exact simulator on run-length coded words. Jumps found automatically: a wall `WL q> WR` (up to 6 cells, on both sides of the head) crossing a run `w^n` in either direction, found by simulating only the window `WL WR w^k` (k = 1..4 copies, so parity-2/4 crossings work: n = k*m + r), after re-bracketing the run so that it starts at the wall (`u (v u)^n = (u v)^n u`). Exact, step count included; `python3 wordsim.py MACHINE WORDS STEPS` compares with a direct run at every macro step (passes on all three machines, 3*10^5 steps). Visit step counts agree with the repo's `evw.c` at every visit up to 2.75*10^10 (m2) and 1.5*10^10 (m3). |
| `visits.py` | the tape (as runs) each time the head reaches one end of the tape in a given state. |
| `laptool.py` | the symbolic layer: `Sym` integers carry a concrete value and an affine form over hub variables; any step function written with ordinary integer code (wordsim, a list map) can be replayed with them; every comparison / residue is answered by the concrete run and recorded as a linear constraint (`>=`, `==`, `mod`). After a hub-to-hub replay you get the lap f (affine) and the exact set of parameters that take the same branches; `iterate_constraints` / `holds` check the constraints along f^k. |
| `m1_laps.py` | for 1RB1LE_...: hub-to-hub branch words (hubs `[1, M, n]`), and the symbolic replay of the current lap with M, n as variables. |
| `m1_highways.py`, `m1_entries.py`, `m1_eras.py` | statistics of the highways, of the era hubs, and the era branch words. |
| `m3_symvisit.py` | laptool through wordsim: the visit map of 1RB0LD_... derived from the machine with the long counts as variables (output in `data/m3_symbolic_visit.txt`). |
| `m1_check.py` | checks the repo's fitted map of 1RB1LE_... against `wordsim` (marker configurations of the exact run). |
| `data/` | the outputs quoted below. |

Not done: a level-2 accelerator (jumping a cycle that itself contains wordsim jumps, as `rleaccel_rec.py` does).
wordsim is fast where the run is sweeps over long runs (one macro step per run), but slow on inner counters (the
doubling zig-zag of m1, the right-end odometer of m3), so the exact TM-level runs here stop around 10^12 steps.

## 1RB1LE_1LC0RA_0RF0LD_1LE1LA_1RC0LB_---1RC: no closed lap; an attractor *hierarchy* instead

Level: fitted map, iterated exactly 3*10^8 times (blocks of ~1000 bits); the map itself was rechecked against
the exact wordsim run at 1,756 consecutive marker configurations up to step 2,749,187,185,626 (`m1_check.py 1800`,
`data/m1_check.txt`; the repo had checked 214 configurations to 3.7*10^7 steps).

1. **Highway lap (closes symbolically, finite).** laptool on hub `[1, M, n]` in an era of level L (M ~ 2^L):
   `[1, M, n] -> [1, C - n, 2n + c]` (C, c constants of the era), constraints: n odd, 2^(L-1) <= M <= C, n <= C.
   It repeats about L/2 times (e.g. 162 times from the hub at L = 213), then n is too big: like PR 79's highway, a
   finite lap with a ratio invariant. `python3 m1_laps.py 3e6`.
2. **Era map (exact on a line, but not a fixed branch word).** At odd L the hub
   `C(L) = [1, 2^L - (3 n0 + 1)/4, n0]` with `n0 = K - 4L` recurs: C(L) -> C(L+2) for long stretches
   (`data/m1_regimes.txt`): K = 261 (L 41..55), 517 (57..119), 1029 (127..245), 2053 (247..501),
   4101 (503..999 and still running at 3*10^8 iterations), i.e. **K = 2^(8+r) + 5**, each regime ends when n0 is
   about 41..49, and the next starts with K doubled (2K - 5). Inside a regime the line is sometimes left for a few
   eras (other hubs, e.g. even L with n + 4L = 1529, 3065, 6137) and then rejoined.
   But the branch word of an era is **not** the same from one era to the next: after the highway comes a
   T-phase `[jT][L-1 e]...` whose doubling counts j vary (e.g. L = 386..500: the tail of the word runs through
   multisets like {L-4, L-4, L-5, L-5, L-5, L-5}, {L-4, L-4, L-4, L-7}, ... an enumeration that changes every era;
   for L = 277..383 the T-phase reads ~200-bit numbers bit by bit). Among the 113 consecutive odd-L eras of the
   K = 2053 regime there are 30 different words even with repetition counts and absolute doubling counts
   abstracted. So the PR 78 condition "one fixed sequence of macro rules, branches fixed by a band invariant" fails
   at the era level; the era map is a theorem only if the T-phase is proved as a lemma uniform over its digit
   pattern (a counter inside the era), and the regime change K -> 2K - 5 is proved symbolically in K.
3. Verdict: **non-halting is very plausible** (the orbit is not Collatz-random: it is a three-level deterministic
   hierarchy, highway < era < regime, all affine where it was measured), but the PR 78 lap does not close;
   a proof needs PR 80-style era induction with a digit/counter lemma for the T-phase, plus the regime step.
   This hierarchy is new relative to the repo README (which calls the run Collatz-like).

## 1RB0LC_1LC0RE_1LD1LB_1LA1LD_1RF0RA_---1RE: technique does not apply as is

Level: computed (wordsim, 104 right-end B visits, 6.8*10^11 steps; `data/m2_visits_wordsim.txt`).
The list `(100)^x 1011 [(010)^a 11]* (010)^n 01` keeps growing: the number of blocks of length >= 20 at the B
visits goes 0, 1, 3, 6, 9, 11, 15, 19 (visits 0..99), the front counter x behaves like a binary counter
(doubling / -5 / rebirth of blocks), the inner blocks lose 4, 4, 12, 20, ... per visit and new blocks are born
behind the counter. A PR 78 hub needs a fixed shape (a bounded number of blocks) recurring with affine counts;
there is no such hub in the computed range, and the growing block list with counter-like digits means a hub, if
any, must be a geometric family of blocks (as PR 78's `(001)^(c 4^m)`), which the digit values (e.g. 188717,
61532, 32835, 29739, 996, 4093, ...) do not show. Next: a list-level model with a counter lemma (PR 80/86 style).

## 1RB0LD_1RC0RF_0LD0LE_1RF1LC_0LB1LE_0RA---: technique does not apply as is

Level: computed (wordsim, 67 left-end C visits to 1.2*10^12 steps; repo's msim run reproduced to 1.2*10^16 steps).
The left-visit list is a base-4 counter whose digits are whole blocks (block i loses 3*4^(i-1) per visit, a
block that empties merges its two walls, the blocks behind it slow down by 4; a new tail block every 4 visits).
laptool through wordsim gives the visit rule symbolically, from the machine (`python3 m3_symvisit.py 45`): from
`C> 0 10^3 010^18 10^4 010^x4 10^8 010^x3 10^4 010^x2 10^6 010^x1 1 010^x0` the next left-end C visit is
`C> 1^2 0 010^15 10^4 010^(x4-12) 10^8 010^(x3-48) 10^4 010^(x2-192) 10^6 010^(x1-768) 1 010^(x0+3073)` in
`16395 x0 + 4107 x1 + 1035 x2 + 267 x3 + 75 x4 + 23524901` steps, for all x1..x4 even, x0 odd, x4 >= 15,
x3 >= 51, x2 >= 195, x1 >= 771, x0 >= 4 (computed: a symbolic replay, every branch recorded; not a proof).
This is the README's main phase, now with exact conditions; it is not a lap because the front and the tail
change shape from visit to visit.
The number of long blocks grows (0 -> 9 by visit 66, 12 at 1.2*10^16 steps) and the digits (visits-to-empty
a_i/rate_i, e.g. 66, 50, 114, 24, 2, 1) are arbitrary counter digits, not a geometric family. Each era (a1 run
down by 4 per visit, then reloaded from a2 - 3 s1 - 7) lasts a1/4 visits while the tail grows by a factor 4 every
4 visits, so era lengths grow at least exponentially in the previous era length: no fixed-length lap can map
C(N, m) to C(aN + ..., m + k). The halting question is about residues (a reload is 1 mod 4 only for walls s1 = 0
mod 4; walls of 5 and 6 occur), which an odometer-level model (PR 86 token engine, or PR 80 era invariant with
the wall sizes as residue cases) would have to carry.

## What would come next

- m1: prove the era map C(L) -> C(L+2) on the fitted map as a Lean theorem with a lemma for the T-phase (induction
  on the multiset of doubling counts), then the regime step K -> 2K - 5; then the machine-level map
  (the repo's README lists the zig-zag induction and overflow cases needed). laptool can already replay any
  candidate stretch symbolically and give the constraints for each case.
- wordsim: add level-2 cycle jumps (replay a cycle with `Sym` counts through wordsim itself, which laptool
  supports: Syms pass through wordsim's code unchanged), so that the inner counters of m1/m3 are jumped.
