# 1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC

bbchallenge id 8084. Its tape is an alternating block followed by a solid block; at the left end the alternating block about doubles again and again, eating into the solid block, until the solid block is used up and a new round starts.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LC |
| B | 1LC | 1RD |
| C | 1LA | 0LB |
| D | 0RB | 1RE |
| E | 1RF | 0RA |
| F | --- | 0RC |

## What it does

Stop the run when the head reaches a new cell on the left (`a = 10`):

    98,543,810  B>0^2 a^85 1^1663
    98,605,493  B>0^2 a^173 1^1490
    98,852,768  B>0^2 a^349 1^1141
    99,842,939  B>0^2 a^701 1^440

The alternating block goes x -> 2x + 3 and the solid block loses as many cells. Each doubling costs about x^2 steps;
width ~ t^(1/3). Same doubling as the three `1RB1RD_0LC1RA_..._1RF0LD_---0RE` machines.

## Halting

F0 halts; F is entered only from E0 (`1RF`), so a halt needs `E>0 0`. In the first 10^8 steps F was entered
30,382 times, always on a 1 (`c/sstat.c`). Open.

## The frame map in Lean

Frames (blank outside; `X` the head in state X on the next cell; `u^v` v copies of u, so
`11^L` is 2L ones; a frame counts only where the head turns round):

- `b`: `1^L B 10 10^j 1^R`
- `a`: `1^L 10^j 110 A 1^R`
- `c`: `1^L 0 C 0 10^j 1^R`
- `d`: `1^L A 01 10^j 1^R`
- `e`: `1^L 10^j B`
- `f`: `1^L 10^j 1101 B`

The map, as `next` in `lean/Phases.lean`:

```lean
def next : Ph → Option Ph
  | .b l j 0 => some (.e (l) (j + 1))
  | .b l j 1 => some (.e (l) (j + 2))
  | .b l j 2 => none
  | .b l j 3 => some (.f (l) (j + 1))
  | .b l j (r + 4) => some (.a (l) (j + 1) (r + 1))
  | .a l j 0 => some (.f (l) (j))
  | .a 0 j (r + 1) => some (.d (0) (j + 1) (r + 3))
  | .a (l + 1) j (r + 1) => some (.b (l) (j) (r + 3))
  | .c l 0 r => some (.d (l) (0) (r))
  | .c l (j + 1) 0 => some (.d (l) (j) (1))
  | .c l (j + 1) (r + 1) => some (.d (l) (j + 1) (r + 1))
  | .d l 0 0 => some (.e (l + 1) (1))
  | .d l 0 1 => none
  | .d l 0 2 => some (.f (l + 1) (0))
  | .d l 0 (r + 3) => some (.a (l + 1) (0) (r + 1))
  | .d l 1 0 => none
  | .d l 1 1 => some (.c (l + 4) (0) (0))
  | .d l 1 2 => some (.b (l + 2) (0) (1))
  | .d l 1 (r + 3) => some (.b (l + 2) (1) (r + 1))
  | .d l 2 r => some (.c (l + 4) (0) (r))
  | .d l (j + 3) 0 => some (.c (l + 4) (j) (1))
  | .d l (j + 3) (r + 1) => some (.c (l + 4) (j + 1) (r + 1))
  | .e 0 0 => some (.d (0) (0) (1))
  | .e 0 (j + 1) => some (.d (0) (0) (2 * j + 3))
  | .e 1 0 => some (.d (0) (1) (1))
  | .e 1 (j + 1) => some (.d (0) (1) (2 * j + 3))
  | .e (l + 2) 0 => some (.b (l) (0) (1))
  | .e (l + 2) (j + 1) => some (.b (l) (0) (2 * j + 3))
  | .f l 0 => some (.b (l) (1) (1))
  | .f l (j + 1) => some (.e (l) (j + 4))
```

`lean/Phases.lean` proves every case for all sizes (`next_sound`, from the symbolic runs in `lean/Pieces.lean`),
that the undefined cases `.b l j 2`, `.d l 0 1`, `.d l 1 0` halt (`none_halts`), `halts_iff` (the machine halts from blank tape
iff the orbit of `Ph.e 1 0` reaches one of them), and by `native_decide` that the first 10^8 frames do
not (`no_halt_phases`; about 5.95*10^11 steps).

`py/pieces.py` regenerates both Lean files from the machine: it fits the map (`py/fitlib.py`, frames in `py/spec.py`),
collapses it into cases (`py/tree.py`) and proves each case with `tools/py/bbtools/symtm.py`. `py/framemap.py` is the
fitted map in Python: `verify R`, `real N`, `run K` (checked: `verify 20` with 31,259
frames and `real 5000000` with 41,118 frames, no mismatch).

## The recursion in rule form

The bbchallenge wiki page of this machine (analysis by Racheline) gives its recursion as Antihydra's is given; here
with the exact number of steps of each rule. A visit is any moment the tape is

    A(a, b) := 0^∞ 1^a 0 C> 1^b 0^∞          (a >= 1)

    0^∞ A> 0^∞     --52-->                 A(2, 9)
    A(a, b)        --2a² + 12a - 1-->      A(2a + 4, b - a - 1)     a even, b >= a + 3
    A(a, b)        --2a² + 12a + 13-->     A(2a + 3, b - a)         a odd, b >= a + 4
    A(a, a + 3)    --2a² + 12a + 39-->     A(2a + 1, 9)             a odd
    A(a, a + 2)    --2a² + 9a + 23-->      A(1, 2a + 7)             a >= 2
    A(a, a + 1)    --2a² + 5a + 7-->       A(4, 2a + 4)             a >= 3
    A(a, b)        --2b² + b + 5-->        A(a - b + 1, 2b + 3)     a >= b >= 4
    A(a, 2)        --25-->                 A(a - 3, 7)              a >= 4
    A(a, 3)        --11-->                 HALT                     a >= 2

The rules are the wiki's; the step counts and the bounds on a are added here. A(1, 2), A(1, 3), A(2, 2), A(3, 2) are
outside every rule and no rule leads to them. The Lean map is finer: A(a, b) is the frame b(a - 2, 1, b - 1) three
steps earlier (a = 1: d(0, 2, b - 1), five steps earlier), and each rule is the run of Lean cases from one such frame
to the next.

## The rules in Lean

`lean/Rules.lean` proves the rules (their targets, not their step counts) for all sizes from the frame map: each is a
zigzag of `b`/`a` frames (`loop_ba`), for the growing rules a sweep of `d`/`c` frames (`loop_cd`), and a few single
cases of `next` (`r_de`, `r_do`, `r_do1`, `r_p3`, `r_p3_1`, `r_p2`, `r_p1`, `r_ge`, `r_b2`, gathered in `op_step`;
`dom` is kept by every rule). Then:

- `halts_iff_rules`: **the machine halts from blank tape iff the orbit of (2, 9) under `op` reaches some (a, 3).**
- `no_b3` (`native_decide`, about a minute): not in the first 10^8 visits, about 6.8*10^23 machine steps by the
  step counts above.

## Looking for an invariant that excludes b = 3

The only way to b = 3 is the growing rule from A(a, a + 4) with a even (giving A(2a + 4, 3)); every other rule
gives b >= 4, except the same rule from A(a, a + 3), a even, which gives b = 2. So the question is whether the orbit ever visits A(a, a + 4) with a even.

- The orbit is cheap to follow and its sizes grow only about linearly in the number N of visits; the machine steps
  grow like 0.68 N^3. `tools/collatz/c/amap.c` found no halt in the first 10^12 visits (a, b near 3.5*10^12, about
  6.8*10^35 machine steps). `c/abrun.c` does the same in 128-bit integers with exact step counts (about 1.3*10^8
  visits a second) and logs every visit with 1 <= b - a <= 8; it agrees, and goes on to 3*10^12 visits with no
  halt (a, b near 10^13, 1.84*10^37 machine steps; about 7 hours, resumed from its logged states). Its log has 41
  visits with 1 <= b - a <= 8 in all, none with a even and b - a = 4.
- Almost every visit is a swap (half of them) or a growing rule; the restarts (b - a = 1, 2, or 3 with a odd) are
  rare: 8 restarts and 2 short rules (b = 2) in the first 10^7 visits.
- No congruence excludes it. `c/abres.c` tabulates (a mod M, (b - a) mod M) over the visits with b > a and
  b - a <= 10^6 among the first 3*10^9: the table is far from uniform (many classes are empty; for example a = 2 or
  3 mod 4 forces b odd), but for every M tried (2^k up to 256, and 48, 90, 120, 210, 252) the classes with a even and
  b - a = 4 mod M together get the same share as any other even residue of b - a. The exact search over residues
  mod every even M up to 128 (the rules applied to residues, each branch allowed whenever its congruence allows it)
  also reaches a even, b - a = 4 mod M.
- Visits with b - a small behave like a Poisson process in the logarithm of the visit index. `c/abstat.c`: over the
  visits with b > a, a even, b - a even and b - a <= 10^5, about 5,500 fall in each decade of visit index (10^5 to
  10^6, ..., 10^9 to 10^10), flat in b - a down to b - a <= 100. That is about 0.11 per decade for each single even
  value of b - a, b - a = 4 included. In the 12 decades run the expected number of halting visits is about 1.3, so
  seeing none is unremarkable (probability about 0.27).
- The halting rule is reached from other starts. `c/abrand.c`: of 9,000 orbits from random A(a, b) with a, b below
  10^9, run 10^6 visits each, 5 halt (for example A(264421744, 92483937) reaches A(358606020, 3) after 485,721
  visits), and visits with a even and b - a = 4 are as frequent as those with b - a = 2, 6 or 8.

- Why it looks random: **the rules are a doubling map in disguise.** Every rule adds a fixed amount to s = a + b
  (3 for a growing rule, 4 for the swap, 6 or 7 for a restart, 2 for the short rule; `op_sum`, `orbit_sum` in
  `lean/Rules.lean`), so s is a clock: after N visits s = 3.5 N + O(sqrt N) (3,500,001,904 after 10^9). In terms of
  x = a / s the swap (a >= b, x >= 1/2) is a -> 2a - s + 1 and the growing rules a -> 2a + 4 or 2a + 3, that is
  x -> 2x mod 1 up to O(1/s). The swap/grow sequence is the binary expansion of x, refreshed by the small constants;
  `c/abdig.c` finds its blocks of 12 digits equidistributed over the first 10^9 visits (chi-square 3,956 on 4,095
  degrees of freedom). The halt asks for one exact point, a = (s - 4)/2 with a even, of a doubling map whose low
  digits are fed by +3/+4 carries: the same kind of question as whether a Collatz-like orbit hits one value.

So no invariant of this kind exists, and the evidence is that the orbit behaves like a random one: under that model it
halts with probability 1 (0.11 per decade summed over all decades diverges), but only after many more decades of
visits (median about 2*10^18 visits, about 10^55 machine steps). Neither a proof of halting nor of non-halting is in
sight: the first needs the orbit followed to the halt, the second an argument that the visits avoid one exact
diagonal.
`py/rules.py` checks the rules and step counts against direct simulation (3,418 tapes A(a, b) with a, b < 60, and the
238 visits of the first 10^7 steps from blank tape) and against the Lean cases (the same tapes, the same run, and the
Lean map for 5*10^5 frames, 685 visits). Example: A(1, 7) halts after 27 + 82 + 79 + 176 + 79 + 431 + 11 = 885 steps
(A(5, 6), A(4, 14), A(12, 9), A(4, 21), A(12, 16), A(28, 3), halt), as direct simulation gives.

## Many visits at once

Away from the resets each visit is one of two affine maps, picked by one digit: grow (b > a) A(a, b) -> A(2a + 4,
b - a - 1) or A(2a + 3, b - a), swap (b <= a) A(a, b) -> A(a - b + 1, 2b + 3). In d = b - a, s = a + b they are
d -> 2d - s + c and d -> 2d + s + 2, a doubling map on d / s: the digits are the binary expansion of b / (a + b), up
to carries from the constants that reach only about log2(s) places down. So `c/abfast.c` reads the next K digits at
once as the top bits of 2^K b / (a + b) (K a multiple of 4, the largest with 32 * 2^K <= s / 64, at most 48; 32 once
s passes 2^43), applies them formally with tables of 8 and 4 digits in 128-bit integers, and keeps the block only if
both coordinates end at least 16 * 2^K; otherwise it redoes the block one visit at a time with the full rules
(resets, halt, the near log of `c/abrun.c`). About 1 block in 100 is redone.

`lean/Block.lean` proves the check sound for any guessed digits, with no `native_decide`: `drun` applies the two maps
formally on integers, and `block_ok` says that if the formal run of a digit list L from a visit (a, b) ends with both
coordinates at least 16 * 2^|L|, then `opIter |L| (a, b)` is that formal run. The proof: one formal step at most
doubles min(a, b) plus 4 (`dstep_min`), so every step of such a block ends with both coordinates at least 28
(`drun_back`), and a formal step that ends there is the step of `op` (`dstep_op`). `block_far` adds that no visit
inside the block has 1 <= b - a <= 27, so no halt, reset or near visit is skipped.

Checks: the same states as `c/abrun.c` after 10^9 visits, after 10^11 (A(185614072747, 164385956473)) and after
3*10^12 (A(6583418669566, 3916580488195)), with the same near visits (36 and 41). It runs at about 1.7*10^9 visits a
second on one core, 13 times `c/abrun.c`. It does not count machine steps; those follow T ~ 0.68 N^3 closely
(0.6806 N^3 at N = 10^11 and at 3*10^12 by `c/abrun.c`).

<!-- abfast-progress -->
| visits | end state A(a, b) | near visits (1 <= b - a <= 8) | about steps |
|---|---|---|---|
| 10^12 | A(2371048047986, 1128951743257) | 38 | 6.8e+35 |
| 3*10^12 | A(6583418669566, 3916580488195) | 41 | 1.8e+37 |
| 6.6*10^12 | A(8096170023751, 15003829348773) | 41 | 2.0e+38 |
<!-- /abfast-progress -->

`c/abfast_log.txt` keeps every near visit and reset, and the state every 10^12 visits (any `prog` line resumes the
run: `./abfast N 100000000000 i a b`). None of the near visits has a even and b - a = 4.

## Status

Open. Lean (`lean/Blank.lean`): the halting configurations (`step_none_iff`), no halt in 10,000 steps by the kernel, in 10,000,000 by `native_decide`. C: no halt in 10^9 steps (`tools/c/triage.c`) and in 10^15 steps (`c/mrun.c`, exact macro simulation). Lean (`lean/Phases.lean`, on `lean/Pieces.lean` generated by `py/pieces.py`): the whole frame map, 30 cases over 6 tape shapes, for all sizes (`next_sound`); the undefined cases halt (`none_halts`); the machine halts iff the orbit of `Ph.e 1 0` reaches one (`halts_iff`); not in the first 10^8 frames (`no_halt_phases`, `native_decide`; about 5.95*10^11 steps). Open: whether the orbit ever gets there. Lean (`lean/Rules.lean`): the wiki's rules for all sizes, the machine halts iff their orbit from (2, 9) reaches b = 3 (`halts_iff_rules`), not in the first 10^8 visits (`no_b3`, `native_decide`; about 6.8*10^23 steps). C (`c/abfast.c`, blocks proved sound by `block_ok` in `lean/Block.lean`): not in the first 6.6*10^12 visits (about 2.0*10^38 steps). C (`c/abrun.c`): not in the first 3*10^12 visits (about 1.84*10^37 steps); no congruence invariant excludes b = 3 (see above).

## First look

Growth class **power/power** (left: power, exponent 0.333; right: power,
exponent 0.326). After 1,000,000,000 steps: 3,959 cells visited (1,403 left of the
start, 1,816 right), 2,754 ones.

- left, step 964,817,707: `B>0 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 `
- left, step 980,630,090: `B>0 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 `
- right, step 964,431,851: `1^437 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 `
- right, step 989,291,133: `1^390 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 `






## Pages

- [`pages/holdouts/1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC/explainer.html`](../../pages/holdouts/1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC/explainer.html)
- [`pages/holdouts/1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC/proof-status.html`](../../pages/holdouts/1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC/proof-status.html)






## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC/lean/check.sh
gcc -O2 -o mrun holdouts/1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC/c/mrun.c && ./mrun 1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC 2 1000000000000000
gcc -O2 -I tools/c -o sstat holdouts/1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC/c/sstat.c && ./sstat 1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC 100000000
python3 holdouts/1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC/py/pieces.py && git diff --exit-code holdouts/1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC/lean
python3 holdouts/1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC/py/framemap.py verify 20
python3 holdouts/1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC/py/rules.py                # the wiki's rules and their step counts against the machine and the Lean map
gcc -O2 -o abrun holdouts/1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC/c/abrun.c && ./abrun 140000000000 10000000000   # about 18 minutes
gcc -O2 -o abstat holdouts/1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC/c/abstat.c && ./abstat 10000000000 100000
gcc -O2 -o abres holdouts/1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC/c/abres.c && ./abres 3000000000 1000000 64
gcc -O2 -o abrand holdouts/1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC/c/abrand.c && ./abrand 1 3000 1000000 1000000000 v
gcc -O3 -march=native -o abfast holdouts/1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC/c/abfast.c && ./abfast 3000000000000 100000000000   # about 35 minutes; ends at A(6583418669566, 3916580488195)
gcc -O2 -o abdig holdouts/1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC/c/abdig.c -lm && ./abdig 1000000000 12
```

## Later

- Find the higher-level rule (one sweep or round to the next) and which sizes lead to an undefined case, as was
  done for the all-ones lengths of `1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_---0RE`.
