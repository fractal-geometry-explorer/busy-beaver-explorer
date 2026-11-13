# 1RB0LE_1RC---_1RD1RE_1LA0RF_0RC0LA_0LC0RB

Group G08 (two-sided square-root growth). It **never halts** from blank tape: Lean proves `nonhalting :
¬ HaltsFromBlank` (`lean/Closed.lean`, kernel only; axioms `propext`, `Classical.choice`, `Quot.sound`).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LE |
| B | 1RC | --- |
| C | 1RD | 1RE |
| D | 1LA | 0RF |
| E | 0RC | 0LA |
| F | 0LC | 0RB |

## What it does

Two kinds of phase alternate (`py/shape.py`, the tape compressed into repeated words at the visits to an end):

*Round-trip phase.* At the left-end visits the tape is `0... (1000)^a (10)^b w^c` with short joints, where
`w = 00000010000010` (in some rotation). c falls and a, b grow: (a, b, c) = (80, 219, 59) at step 824,136,
(136, 446, 23) at 1,426,658, (165, 555, 3) at 1,896,095.

*Right phase.* Then the head stays away from the left end (steps 1,966,457 to 6,370,604). At the right-end visits
the tape is `(1110)^170 (1111110)^k 111 001 (10)^m 1 E> 0` and every visit moves one copy from m to k
(k + m = 578). Afterwards the tape is `0^8 (1000)^170 (00100000001000)^289 ...`: pairs of `1111110` have become
copies of w, and the next round-trip phase starts.

Inside a round-trip phase the left-end visits run through an exact cycle of four shapes, after which (a, b, c)
becomes (a + 3, b + 12, c − 2): at step 824,136 `0^7 (1000)^80 0000 1 00000 1 000 (10)^219 (00100000100000)^59 ...`,
at 847,516 the same with 83, 231, 57. The same cycle is still running at step 1.044·10¹¹ with
(a, b, c) = (30424, 87941, 19564) (`c/phases.c`). After each right phase there are sub-phases in which a run of
`0010` (the old `1000`-run) is used up while a new `1000`-run grows.

Phase boundaries (`c/boundaries.c 3e10`, the steps where the run switches from extending one end to the other):

| step | phase starts | form |
|---|---|---|
| 29,301 | odd round trip | `O 14 37 11` |
| 191,775 | even round trip | `EF 30 47` |
| 808,896 | odd round trip | `O 79 219 61` |
| 6,370,604 | even round trip | `EF 170 288` |
| 27,629,379 | odd round trip | `O 467 1283 361` |
| 223,234,215 | even round trip | `EF 1008 1720` |
| 735,331,316 | right phase with three runs of `10` | `RG3` |
| 976,078,402 | two-run round trip (the end of `RG3`, then `T2`) | `T2` |
| 3,043,404,308 | odd round trip | `O 6008 13753 3392` (c even) |
| 7,125,828,416 | right phase after the 4-visit cycle ran out of words | `RF` |
| 22,249,365,380 | even round trip | `EF 11097 17051` |

with the forms (J0 = `0000 1 00000 1 000`, J = `001 00000 1 000 101`)

    O a b c        0^inf A> 0^7 (1000)^a (10)^b (00001000001000)^c 101           odd round trip
    S1 a b c       0^inf A> 0^7 (1000)^a J0 (10)^b (00100000100000)^c J          its 4-visit cycle
    RF a k m       0^inf (1110)^a (1111110)^k 111 001 (10)^m 1 E> 0^inf          right phase after it
    EF a q         0^inf E> 00000 (0001)^a (00000100000001)^q 00000 1 0^7 1 00000 1 000 101   even round trip
    T3 a x d y z c 0^inf A> 0^7 (1000)^a (10)^x (0010)^d (10)^y J0 (10)^z (00100000100000)^c J   its 5-visit cycle
    T2 a x y c     0^inf A> 0^7 (1000)^a J0 (10)^x 0 (01)^y (00000001000001)^c 000 101   two runs, 3-visit cycle
    U3 a x y z c   0^inf A> 0^7 (1000)^a J0 (10)^x 0 (01)^y 0 J0 (10)^z (00100000100000)^c J   three runs, y frozen
    RG a x n m     0^inf (1110)^a 0110101010101001 (10)^x (1111011)^n 1001 (10)^m 1 E> 0^inf      after T2
    RG3 a x y n m  0^inf (1110)^a 11111101111110111001 (10)^x 111001 (10)^y (1111011)^n 1001 (10)^m 1 E> 0^inf

An *odd* round-trip phase `O a b c` runs the 4-visit cycle. An *even* one `EF a q` first runs a 5-visit cycle on
`T3`, where the old `1000`-run, now `(0010)^d`, loses 5 copies a turn. With d < 5 left it exits. For d = 0, 3, 4 the
first two runs of `10` merge into `T2`. For d = 1, 2 a third run stays, frozen at its length, giving `U3`. The round
trips end when the 14-cell words run out (c = 0 or 1), and right phases follow: `RF` after `S1`, `RG` after `T2` and
`RG3` after `U3`. Each turns one `10` into one `1111110` or `1111011` per visit. A right phase ends when one `10`
is left. If the new run has the right parity it folds pairwise into 14-cell words and the next round trip starts:
`RF` to `EF` (odd k), `RG` to `O` (even n), `RG3` to `T2` (even n). With the other parity the leftover copy
starts a round trip of the 5-visit kind directly: `RG`, `RG3` (odd n) to `T3`, the old `1000`-run becoming the
`0010`-run, and `RF` (even k) to `O a 0 c`, which has no `10` and is an `S1` after one pass.

## The branch table

Every move below is a Lean theorem for all values of its variables (kernel; `lean/Branch.lean`, `lean/Ends.lean`,
`lean/Cycle.lean`, `lean/Phase.lean`), with its exact step count:

| from | condition | rule | to |
|---|---|---|---|
| `O a b c` | b ≥ 6, c ≥ 2 | `oentry` | `S1 (a+1) b (c-2)` |
| `S1` | c ≥ 2 | `cycle_iter` | `S1`, (a, b, c) → (a+3, b+12, c−2) per turn |
| `S1 a b 1` / `S1 a b 0` | b ≥ 6 / b ≥ 3 | `oexit` / `sexit0` | `RF (a+3) 5 (b+6)` / `RF (a+3) 4 (b+7)` |
| `RF a k m` | m ≥ 2 | `rcyc_iter` | `RF a (k+1) (m−1)` per turn |
| `RF a k 1` | k odd | `rend'` | `EF a ((k−1)/2)` |
| `EF a q` | a ≥ 7, q ≥ 5 | `eentry` | `T3 5 14 (a−7) 8 7 (q−3)` |
| `T3` | d ≥ 5, c ≥ 2 | `cycle3_iter` | d − 5, c − 2 per turn |
| `T3 a x d y z c` | d = 0, 3, 4 | `texit0/3/4` | `T2` |
| `T3 a x d y z c` | d = 1, 2 | `texit1/2` | `U3` |
| `T2` / `U3` | c ≥ 2 | `cycle2_iter` / `ucyc_iter` | c − 2 per turn |
| `T2 a x y c` / `U3` | c = 0, 1 | `t2exit0/1` / `uexit0/1` | `RG a' x' (4 or 5) m` / `RG3` |
| `RG` / `RG3` | m ≥ 2 | `gcyc_iter` / `g3cyc_iter` | n + 1, m − 1 per turn |
| `RG a x n 1` | n even, a ≥ 2 | `gend'` | `O (a−1) (x+9) (n/2+1)` |
| `RG3 a x y n 1` | n even, y ≥ 4, n ≥ 4 | `g3end'` | `T2 (a+3) (x+9) (y+6) (n/2−1)` |
| `RG a x n 1` | n odd, a ≥ 3, x ≥ 6, n ≥ 7 | `gendo'` | `T3 1 6 (a−3) 11 (x+8) ((n−7)/2+1)` |
| `RG3 a x y n 1` | n odd, a ≥ 7, x ≥ 10, y ≥ 2, n ≥ 7 | `g3endo'` | `T3 5 14 (a−7) 15 (x+y+5) ((n−7)/2+1)` |
| `RF a k 1` | k even | `rende'` | `O a 0 (k/2+1)` |
| `O a 0 c` | c ≥ 3 | `ozero`, `t3_s1` | `S1 (a+2) 7 (c−3)` |

(Exact offsets are in the theorem statements; the last four are in `lean/Ends.lean`.) What the table alone does
not exclude is a phase reaching a branch with parameters below the offsets, or `T3` running out of 14-cell words
while d ≥ 5. The invariant below excludes both.

*The replay* (`py/macro.py`) runs the table on numbers from `O 14 37 11` at step 29,301. Each cycle is applied k
times at once, with the step count summed in closed form. Its 49 macro states before 3·10¹⁰ steps are all on the
simulated tape at exactly the predicted step, state and cell for cell (`c/checkpoints.c`). Every phase boundary
above is one of them. So the table covers every branch the run takes in 3·10¹⁰ steps. The replay goes on without
a gap through 10³⁰⁰ steps (2,281 macro states; it no longer stops at 1.08·10¹⁵, where the first odd end of `RG`,
`RG 3564802 8141369 4104765 1`, now goes by `gendo'`). Lean checks its first 196 moves from blank tape, to
`T2 34158019330534 128092572489511 160237983842729 41908435347077` at step 5.7·10²⁹ (`table_from_blank` in
`lean/Table.lean`; `py/table.py 1e300` gives the 2,280 moves to 10³⁰⁰, which compile in about 90 s).

## Why it never halts

Seen from one phase start to the next, the run is a map on ten forms (`O a b c` with b large, `O a 0 c`, `S1`,
`RF`, `EF`, `T3`, `T2`, `U3`, `RG`, `RG3`): one cycle iterate and one exit rule, 20 cases in all according to the
residue of the count the cycle uses up (c mod 2, d mod 5) or the parity of the right-phase run (`mv_*` in
`lean/Closed.lean`). Every case is affine in the counts once that residue is fixed. `Good` is a conjunction of
linear inequalities for each form (3 to 16 per form, integer coefficients up to 1,321):

- the growing counts keep their ratios in a polyhedral cone, and every case maps each form's cone strictly inside
  the next form's cone;
- the bounded counts stay in range (`RF` k, `RG`/`RG3` n in {4, 5}; `T3` x = 2a + 4 ≤ 14, 8 ≤ y ≤ 15), and `U3`, `RG3`
  keep their exact relations (x − 2a ∈ [0, 2], 4y − 7a ∈ [−13, 27]; 4y + 21x − 49a ∈ [−63, 19]);
- a positive linear size `σ ≥ N`, where every case multiplies σ by at least 1.1, so the margin of the cones beats
  the constant parts of the moves.

These imply every offset the rules need, and that `T3` has c ≥ 2⌊d/5⌋ + 3, so its words never run out first.
`good_step` proves that from a `Good` configuration the machine makes at least one step and reaches a `Good`
configuration again: per case, one `mv_*` lemma and `omega`. The end of `table_from_blank` is `Good`
(`decide`), so the run from blank tape is defined for every length (`nonhalting`). The inequalities were found by
linear programming over the replay's states (scratch scripts using scipy, not part of the proof). Along the replay
every form entry from the 39th on is `Good`.

Passes (proved for any n): `pass_10_right` (C crosses `(10)^n`), `pass_10_left` (A crosses `(01)^n` leftwards),
`fill_F` (`F> (1000)^n` to `(1110)^n F>`), `fill_B` (`0 B> (0001)^n` to `(1110)^n 0 B>`), `clear_A`
(`(0111)^n A> 1` to `A> 1 (0010)^n`).

The only halt is B reading a 1; B is entered from A reading a 0 and from F reading a 1, so `A> 0 1` and `F> 1 1`
halt (`halt_A`, `halt_F`).

## What is proved, and where

- `lean/Blank.lean` (generated): the halting configurations; no halt in 10⁴ steps (kernel) and 10⁷ (`native_decide`).
- `lean/Rules.lean` (kernel, written by `py/rules.py`): the five passes; `halt_A`, `halt_F`.
- `lean/Route.lean` (kernel, written by `py/route.py`): `halt_route`, every configuration two steps before a
  halt is `0 D> x 1 1`, `D> 1 1 1` or `0 D> 0`.
- `lean/Cycle.lean` (kernel, written by `py/cycle.py`): the three cycles of the round-trip phases, for all sizes:
  `cycle` S1 a (b+2) (c+2) → S1 (a+3) (b+14) c (80a + 72b + 1356 steps), `cycle2` T2 a (x+6) (y+6) (c+2) →
  T2 (a+3) (x+13) (y+11) c, `cycle3` T3 a (x+6) (d+5) (y+6) (z+6) (c+2) → T3 (a+4) (x+14) d (y+13) (z+11) c, and
  their k-fold iterates `cycle_iter`, `cycle2_iter`, `cycle3_iter` (induction on k).
- `lean/Phase.lean` (kernel, written by `py/phase.py`): `odd_phase`, a whole odd round-trip phase and the right
  phase after it: from `O a (2p+7) (2j+3)` the machine reaches `EF (a+4+3j) (p+6j+8)`, for all a, p, j. It is
  chained from `oentry` (into the 4-visit cycle), `cycle_iter`, `oexit` (the last turn, with one copy of the 14-cell
  word left, into a right phase), `rcyc_iter` (the right-phase cycle `RF a k (m+2)` → `RF a (k+1) (m+1)`, one copy
  of `10` becomes one copy of `1111110`) and `rend` (the run of `1111110` has odd length 2q+1: the start of an even
  phase). The three odd phases at steps 29,301, 808,896 and 27,629,379 satisfy its hypotheses (b odd, c odd) and
  end where the simulation says (`EF 30 47`, `EF 170 288`, `EF 1008 1720`).
- `lean/Branch.lean` (kernel, written by `py/branch.py`): the branch table above. It has 16 new rules
  (`eentry`, `texit0`..`texit4`, `ucyc`, `t2exit0/1`, `gcyc`, `gend`, `uexit0/1`, `g3cyc`, `g3end`, `sexit0`) and
  the iterates and re-pairings `ucyc_iter`, `gcyc_iter`, `g3cyc_iter`, `gend'`, `g3end'`.
- `lean/Ends.lean` (kernel, written by `py/ends.py`): the ends that `Branch.lean` left open, `gendo`, `g3endo`,
  `rende`, `ozero`, with the re-pairings `rg_odd`, `rg3_odd`, `rf_even`, `t3_s1` and `gendo'`, `g3endo'`, `rende'`.
- `lean/Table.lean` (kernel, written by `py/table.py`): `blank_O`, the first 29,301 steps from blank tape, reach
  `O 14 37 11`. `table_run` chains the first 196 moves of the replay, to step 5.7·10²⁹, and `table_from_blank`
  combines the two.
- `lean/Closed.lean` (kernel, written by `py/closed.py`): the 20 moves `mv_*`, the invariant `Good`, `good_step`
  and `nonhalting`.
- `py/macro.py` with `c/checkpoints.c` (trusted): the replay against the plain simulation, 49 of 49 checkpoints
  up to 3·10¹⁰ steps.
- `c/boundaries.c` (heuristic): the phase boundaries; `c/phases.c` (heuristic): compressed tapes at long-gap
  left-end visits, fast enough for 10¹¹ steps.
- `py/shape.py`, `py/near_halt.py` (heuristic): compressed tapes at the end visits; neighbourhoods of A, B, F.

## What is open

Nothing about halting: `nonhalting` settles it. The proof does not explain the growth rate; the replay suggests
each pair of phases multiplies the counts by a factor that depends on the residues taken.

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LE_1RC---_1RD1RE_1LA0RF_0RC0LA_0LC0RB/lean/check.sh
python3 holdouts/1RB0LE_1RC---_1RD1RE_1LA0RF_0RC0LA_0LC0RB/py/route.py        # rewrites lean/Route.lean
python3 holdouts/1RB0LE_1RC---_1RD1RE_1LA0RF_0RC0LA_0LC0RB/py/rules.py          # rewrites lean/Rules.lean
python3 holdouts/1RB0LE_1RC---_1RD1RE_1LA0RF_0RC0LA_0LC0RB/py/cycle.py          # rewrites lean/Cycle.lean
python3 holdouts/1RB0LE_1RC---_1RD1RE_1LA0RF_0RC0LA_0LC0RB/py/phase.py          # rewrites lean/Phase.lean (after Cycle)
python3 holdouts/1RB0LE_1RC---_1RD1RE_1LA0RF_0RC0LA_0LC0RB/py/branch.py         # rewrites lean/Branch.lean
python3 holdouts/1RB0LE_1RC---_1RD1RE_1LA0RF_0RC0LA_0LC0RB/py/ends.py           # rewrites lean/Ends.lean
python3 holdouts/1RB0LE_1RC---_1RD1RE_1LA0RF_0RC0LA_0LC0RB/py/table.py          # rewrites lean/Table.lean
python3 holdouts/1RB0LE_1RC---_1RD1RE_1LA0RF_0RC0LA_0LC0RB/py/closed.py         # rewrites lean/Closed.lean
python3 holdouts/1RB0LE_1RC---_1RD1RE_1LA0RF_0RC0LA_0LC0RB/py/macro.py          # the replay, to 1e300 steps
python3 holdouts/1RB0LE_1RC---_1RD1RE_1LA0RF_0RC0LA_0LC0RB/py/macro.py --checkpoints checks.txt 3e10
gcc -O2 -o checkpoints holdouts/1RB0LE_1RC---_1RD1RE_1LA0RF_0RC0LA_0LC0RB/c/checkpoints.c && ./checkpoints checks.txt
python3 holdouts/1RB0LE_1RC---_1RD1RE_1LA0RF_0RC0LA_0LC0RB/py/shape.py 1e7 L 25   # round-trip phases
python3 holdouts/1RB0LE_1RC---_1RD1RE_1LA0RF_0RC0LA_0LC0RB/py/shape.py 6.5e6 R 60 # a right phase
gcc -O2 -o boundaries holdouts/1RB0LE_1RC---_1RD1RE_1LA0RF_0RC0LA_0LC0RB/c/boundaries.c && ./boundaries 3e10
gcc -O2 -o phases holdouts/1RB0LE_1RC---_1RD1RE_1LA0RF_0RC0LA_0LC0RB/c/phases.c && ./phases 1RB0LE_1RC---_1RD1RE_1LA0RF_0RC0LA_0LC0RB 1e9 1000
```
