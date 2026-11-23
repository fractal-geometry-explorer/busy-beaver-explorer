# 1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE

bbchallenge id 151878. Its tape switches between two solid blocks and an alternating-then-solid pair; at the left end the alternating block about doubles at the expense of the solid one.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RF |
| B | 0LC | 0RF |
| C | 1RD | 1LC |
| D | --- | 0LE |
| E | 0RC | 1LF |
| F | 1RA | 0LE |

## What it does

Stop the run when the head reaches a new cell (`a = 10`):

    98,030,020  1^1171 a 1^832 B>0          (right end)
    98,032,028  F>0 a^587 1^830 a           (left end)
    98,668,985  1^1659 a 1^347 A>0          (right end)
    98,670,998  F>0 a^831 1^346 a           (left end)
    99,190,279  1^691 a 1^1319 A>0          (right end)
    99,192,296  F>0 a^347 1^1318 a          (left end)
    99,440,086  E>0^2 a^698 1^617 a         (left end)

A solid block 1^p is rewritten as about p/2 copies of `10` on the way left; at the left end the alternating block
doubles at the expense of the solid one. Same doubling as the three `1RB1RD_0LC1RA_..._1RF0LD_---0RE`; width ~ t^(1/3).

## Halting

D0 halts; D is entered only from C0 (`1RD`), so a halt needs `C>0 0`. In the first 10^8 steps D was entered
111,425 times, always on a 1 (`c/sstat.c`). Open.

## The frame map in Lean

Frames (blank outside; `X` the head in state X on the next cell; `u^v` v copies of u, so
`11^L` is 2L ones; a frame counts only where the head turns round):

- `e`: `11^L E 00 10^j 1^R`
- `E`: `1 11^L E 00 10^j 1^R`
- `f`: `11^L F 1^R`
- `F`: `1 11^L F 1^R`
- `g`: `F 0 10^j 1^R`
- `h`: `11^L 0 11^M F 1^R`
- `H`: `11^L 0 1 11^M F 1^R`
- `i`: `1 11^L 0 11^M F 1^R`
- `I`: `1 11^L 0 1 11^M F 1^R`
- `k`: `11^L 0 1^M B`
- `K`: `1 11^L 0 1^M B`

The map, as `next` in `lean/Phases.lean`:

```lean
def next : Ph → Option Ph
  | .e l 0 0 => none
  | .e 0 0 1 => some (.g (0) (1))
  | .e 0 0 (r + 2) => some (.g (1) (r + 1))
  | .e (l + 1) 0 1 => some (.g (1) (2 * l + 5))
  | .e (l + 1) 0 2 => some (.g (1) (2 * l + 7))
  | .e (l + 1) 0 (r + 3) => some (.f (l + 3) (r + 1))
  | .e 0 1 0 => some (.g (0) (1))
  | .e (l + 1) 1 0 => some (.g (1) (2 * l + 5))
  | .e l (j + 2) 0 => some (.k (l + 2) (2 * j + 2))
  | .e l 1 1 => some (.k (l + 2) (2))
  | .e l (j + 2) 1 => some (.k (l + 2) (2 * j + 4))
  | .e l 1 (r + 2) => some (.h (l + 2) (0) (r + 1))
  | .e l (j + 2) (r + 2) => some (.h (l + 2) (j + 1) (r + 1))
  | .E l 0 0 => none
  | .E l 0 1 => some (.g (1) (2 * l + 4))
  | .E l 0 2 => some (.g (1) (2 * l + 6))
  | .E l 0 (r + 3) => some (.F (l + 2) (r + 1))
  | .E l 1 0 => some (.g (1) (2 * l + 4))
  | .E l (j + 2) 0 => some (.K (l + 2) (2 * j + 2))
  | .E l 1 1 => some (.K (l + 2) (2))
  | .E l (j + 2) 1 => some (.K (l + 2) (2 * j + 4))
  | .E l 1 (r + 2) => some (.i (l + 2) (0) (r + 1))
  | .E l (j + 2) (r + 2) => some (.i (l + 2) (j + 1) (r + 1))
  | .f l 0 => some (.g (1) (2 * l + 1))
  | .f 0 1 => none
  | .f (l + 1) 1 => some (.e (0) (l) (1))
  | .f 0 (r + 2) => some (.e (0) (0) (r + 1))
  | .f (l + 1) (r + 2) => some (.e (0) (l + 1) (r + 1))
  | .F l 0 => some (.g (1) (2 * l + 2))
  | .F l 1 => some (.g (l) (1))
  | .F 0 (r + 2) => some (.g (1) (r + 1))
  | .F (l + 1) (r + 2) => some (.g (l + 2) (r + 1))
  | .g j 0 => some (.g (1) (2 * j + 1))
  | .g j 1 => some (.g (1) (2 * j + 3))
  | .g j (r + 2) => some (.f (j + 1) (r + 1))
  | .h 0 m 0 => some (.g (1) (2 * m + 1))
  | .h (l + 1) m 0 => some (.k (l + 1) (2 * m + 2))
  | .h l 0 1 => none
  | .h l (m + 1) 1 => some (.e (l) (m) (1))
  | .h l 0 (r + 2) => some (.e (l) (0) (r + 1))
  | .h l (m + 1) (r + 2) => some (.e (l) (m + 1) (r + 1))
  | .H 0 m 0 => some (.g (1) (2 * m + 2))
  | .H 0 m 1 => some (.g (m) (1))
  | .H 0 0 (r + 2) => some (.g (1) (r + 1))
  | .H 0 (m + 1) (r + 2) => some (.g (m + 2) (r + 1))
  | .H (l + 1) m 0 => some (.k (l + 1) (2 * m + 3))
  | .H (l + 1) m 1 => some (.g (1) (2 * l + 2 * m + 5))
  | .H (l + 1) m 2 => some (.g (1) (2 * l + 2 * m + 7))
  | .H (l + 1) 0 (r + 3) => some (.f (l + 3) (r + 1))
  | .H (l + 1) (m + 1) (r + 3) => some (.f (l + m + 4) (r + 1))
  | .i l m 0 => some (.K (l) (2 * m + 2))
  | .i l 0 1 => none
  | .i l (m + 1) 1 => some (.E (l) (m) (1))
  | .i l 0 (r + 2) => some (.E (l) (0) (r + 1))
  | .i l (m + 1) (r + 2) => some (.E (l) (m + 1) (r + 1))
  | .I l m 0 => some (.K (l) (2 * m + 3))
  | .I l m 1 => some (.g (1) (2 * l + 2 * m + 4))
  | .I l m 2 => some (.g (1) (2 * l + 2 * m + 6))
  | .I l 0 (r + 3) => some (.F (l + 2) (r + 1))
  | .I l (m + 1) (r + 3) => some (.F (l + m + 3) (r + 1))
  | .k l 0 => none
  | .k l 1 => some (.g (l) (1))
  | .k l (m + 2) => some (.g (l + 1) (m + 1))
  | .K l 0 => none
  | .K l 1 => some (.e (0) (l) (1))
  | .K l (m + 2) => some (.e (0) (l + 1) (m + 1))
```

`lean/Phases.lean` proves every case for all sizes (`next_sound`, from the symbolic runs in `lean/Pieces.lean`),
that the undefined cases `.e l 0 0`, `.E l 0 0`, `.f 0 1`, `.h l 0 1`, `.i l 0 1`, `.k l 0`, `.K l 0` halt (`none_halts`), `halts_iff` (the machine halts from blank tape
iff the orbit of `Ph.g 0 1` reaches one of them), and by `native_decide` that the first 10^8 frames do
not (`no_halt_phases`; about 9.7*10^11 steps).

`py/pieces.py` regenerates both Lean files from the machine: it fits the map (`py/fitlib.py`, frames in `py/spec.py`),
collapses it into cases (`py/tree.py`) and proves each case with `tools/py/bbtools/symtm.py`. `py/framemap.py` is the
fitted map in Python: `verify R`, `real N`, `run K` (checked: `verify 14` with 16,632
frames and `real 5000000` with 28,350 frames, no mismatch).

## The frame map run far, and the tent map

`c/framemap.c` iterates the Lean map `next` exactly, from `Ph.g 0 1`: its 66 cases are generated from
`lean/Phases.lean`, with each case's step count from `lean/Pieces.lean`, by `py/gen_c.py` (into
`c/framemap_cases.h`). Nearly every frame is one of two cases, `e l (j + 2) (r + 2)` and `h l (m + 1) (r + 2)`, which
together send `e L J R` to `e (L + 2) (J - 1) (R - 2)`; `lean/Sweep.lean` proves the k-fold version (`sweep`), and the
C program jumps whole sweeps with it. Checks: the dump agrees frame by frame with the Python reading of the Lean map
(`rules.lean_next`) for 300,000 frames, and the run with and without jumps (`NOACCEL=1`) lands on the same frame and
step count at 10^10 frames. Steps are counted exactly in 128 bits (enough to about 10^38; the variables, uint64, stop
the run at 2^60), so GMP was not needed this far.

Result (`c/framemap_run.txt`, 62 minutes on one core): 2,916,662,715,542,862,488,166 frames, of which 10^11 frames f
(one per round of the rule form below), to machine step 151,234,372,263,249,191,290,395,350,829,563 (1.5*10^32), with
no halting case. Variables reached 2.3*10^11.

What the rounds do. With u = 2x/(2x + y), the rules below are, up to O(1/(2x + y)), the tent map: u -> 2u for
x < y/2, u -> 2 - 2u otherwise, while 2x + y grows by 1 to 4 per round. The only halting tape B(x, 2x + 1) is the
exact middle. Only tapes with y odd can halt, and y odd is produced only by the rule B(x, 2y) -> B(2x + 2, 2y - 2x - 3);
a third of the 10^11 rounds had y odd. With d = y - (2x + 1), at x >= 16:

| d | -16..-1 | 0 | 1..16 |
|---|---|---|---|
| frames f | 1 5 4 6 2 7 1 3 2 3 3 4 0 5 3 6 | 0 | 9 6 7 2 6 5 7 2 3 1 2 4 7 5 8 1 |

The 16 even values 0 < |d| <= 16 got 42 hits together, 2.6 each, so no hit at d = 0 is unremarkable (about 7% for a
random orbit). The hits near the middle grow by about 0.26 per tenfold growth of x: a random orbit would hit
eventually, about once per 10^4-fold growth of x (10^12-fold in steps). The closest tapes that could have halted were
2 away (B(278826, 557655), B(31690290, 63380583)); the record tapes with d = +-1 (y even, so no halt) are listed in
the log, the last B(47350001284, 94700002570) at step 8.1*10^31.

## Reading the rounds off the binary digits of u (a dead end), and the rules run further

In the coordinates n = 2x + y and d = 2x - y the rules are exactly a tent map with drift (`lean/Tent.lean`, `tent`
and `op_none_iff`, by the kernel, for the rule map `op` transcribed from `py/rules.py`):

| when | n' | d' |
|---|---|---|
| d >= 0, y even (fold) | n + 4 | n - 2d + 4 |
| d >= 3, y odd (fold) | n + 3 | n - 2d + 9 |
| d <= -3 (double) | n + 1 | n + 2d + 7 |

plus d = -2 -> B(2x + 1, 0), d = 1 -> B(2, 4x - 2), and the halt at d = -1 and nowhere else. So d/n = 2u - 1 goes to
1 - 2|d/n| plus c/n, and each later rule doubles that term.

The tent map T (u -> 2u below 1/2, 2 - 2u above) is the shift on the binary digits of u read with flips: with
u = 0.b1 b2 b3 ..., the k-th step of T doubles iff b_k = b_(k-1) (b_0 = 0). If the rounds were T, the digits of one
tape's u would give the fold/double word of all later rounds. `py/tent.py` tests it on 1,003 tapes from the first
10^6 rounds (exact rationals): the digit word agrees with the real rounds for floor(log2 n) - 2 rounds at the median,
never more than floor(log2 n) + 6. That is what the drift predicts (c/n doubled k times is of order 1 after about
log2 n rules), so the digits say nothing about the rounds beyond about log2 n of them, and cannot test the
exact-middle landing any further than applying the rules does. (Some real number has the true word as its tent
orbit, but finding it needs the run itself.)

`c/rounds.c` applies the rules one at a time, with the exact step counts of `py/rules.py` in 256 bits, from B(1, 0) at
step 8: 7.9 ns per rule, 4.7 times faster than `c/framemap.c` per round. It reproduces `c/framemap.c`'s near-middle
tapes with their exact step counts (B(278826, 557655) at step 16,544,574,460,503,077, B(31690290, 63380583) at step
24,250,600,205,318,179,964,670). Run (`c/rounds_run.txt`, 81 minutes for the last 7*10^11 rules on one core): 8*10^11 rules to machine step 77,432,109,507,548,253,034,910,418,036,526,858 (7.7*10^34, 500 times further than `c/framemap.c`), no halt; x reached 7.5*10^11. New tapes 2 from the middle: B(12459332366, 24918664731) (d = -2, y = 2x - 1, which cannot halt) and B(144615683250, 289231366503) (d = +2) at step 2.3*10^33. Of the rules landing on y odd at x >= 16 (2.7*10^11; sum of 1/x 85.1), the 16 even values 0 < |d| <= 16 of d = y - (2x + 1) were hit 50 times, 3.1 each, and d = 0 never: a random orbit misses with probability about e^-3.1 = 4.5%. By d: -16:1 -14:5 -12:2 -10:4 -8:2 -6:3 -4:2 -2:3 0:0 2:7 4:2 6:5 8:3 10:1 12:4 14:5 16:1, so there is no visible congruence keeping d = 0 out (all residues of d mod 8 are hit nearby).

## The recursion in rule form

The bbchallenge wiki page of this machine gives its recursion as Antihydra's is given (its top level, B(x, y) =
A(0, 2x, y) in the wiki's notation); here with the exact number of steps of each rule, from B(x, y) to the first
moment the tape is the target:

    B(x, y) := 0^∞ 1^(2x) F> 1^y 0^∞          (x >= 1)

    0^∞ A> 0^∞      --8-->                          B(1, 0)
    B(x, 2y)        --4xy - 2y² + 2x + 16y + 12-->  B(2y + 2, 2x - 2y)        x >= y
    B(x, 2y + 1)    --4xy - 2y² + 6x + 12y + 22-->  B(2y + 4, 2x - 2y - 4)    x > y + 1 (y = 0: passes B(x - 1, 2))
    B(x, 2y)        --2x² + 10x + 9-->              B(2x + 2, 2y - 2x - 3)    x < y - 1
    B(x, 2y + 1)    --2x² + 10x + 9-->              B(2x + 2, 2y - 2x - 2)    x < y
    B(x, 2x + 2)    --2x² + 10x + 7-->              B(2x + 1, 0)
    B(x, 2x - 1)    --2x² + 14x + 7-->              B(2, 4x - 2)              x >= 2 (passes B(2x - 1, 0))
    B(x, 2x + 1)    --2x² + 10x + 4-->              HALT

The rules are the wiki's; the step counts are added here. B(1, 1) is outside every rule and no rule leads to it.
B(x, y) is the same tape as the Lean frame f(x, y); each rule is the run of Lean cases from f(x, y) to the next frame
f, except that f(x, 0) is never reached as a frame, so a rule into B(x, 0) and the next one are one run there. The
rules are not stated in Lean; the cases they are made of are (`next_sound`, `none_halts`, `halts_iff` in
`lean/Phases.lean`; the halt ends in `.h l 0 1`), each with its step count in its piece theorem in `lean/Pieces.lean`.
`py/rules.py` checks the rules and step counts against direct simulation (2,449 tapes B(x, y) with x, y < 50, and the
388 visits of the first 10^7 steps from blank tape) and against the Lean cases (the same tapes, the same run, and the
Lean map for 5*10^5 frames, 1,273 frames f). Example: B(1, 16) halts after 21 + 81 + 32 + 37 + 136 = 307 steps
(B(4, 11), B(10, 0), B(2, 20), B(6, 13), halt), as direct simulation gives.

## Status

Open. Lean (`lean/Blank.lean`): the halting configurations (`step_none_iff`), no halt in 10,000 steps by the kernel, in 10,000,000 by `native_decide`. C: no halt in 10^9 steps (`tools/c/triage.c`) and in 10^15 steps (`c/mrun.c`, exact macro simulation). Lean (`lean/Phases.lean`, on `lean/Pieces.lean` generated by `py/pieces.py`): the whole frame map, 66 cases over 11 tape shapes, for all sizes (`next_sound`); the undefined cases halt (`none_halts`); the machine halts iff the orbit of `Ph.g 0 1` reaches one (`halts_iff`); not in the first 10^8 frames (`no_halt_phases`, `native_decide`; about 9.7*10^11 steps). Lean (`lean/Sweep.lean`): k sweeps at once (`sweep`). C (`c/framemap.c`, the Lean map generated from the Lean files): no halt in 2.9*10^21 frames, 1.5*10^32 steps. Lean (`lean/Tent.lean`): the rule map is a tent map with drift, halting only at the exact middle. C (`c/rounds.c`, the rules one at a time): no halt in 8*10^11 rules, 7.7*10^34 steps. Reading the rounds off the binary digits of u reaches only about log2(n) rounds ahead (`py/tent.py`). Open: whether the orbit ever gets there.

## First look

Growth class **power/power** (left: power, exponent 0.339; right: power,
exponent 0.325). After 1,000,000,000 steps: 4,396 cells visited (2,260 left of the
start, 1,268 right), 2,868 ones.

- left, step 977,735,818: `E>0 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 `
- left, step 996,214,690: `F>0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 `
- right, step 980,797,445: `1^3504 0 1^868 B>0`
- right, step 999,366,103: `1^3364 0 1^1027 A>0`






## Pages

- [`pages/holdouts/1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE/explainer.html`](../../pages/holdouts/1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE/explainer.html)
- [`pages/holdouts/1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE/proof-status.html`](../../pages/holdouts/1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE/proof-status.html)






## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE/lean/check.sh
gcc -O2 -o mrun holdouts/1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE/c/mrun.c && ./mrun 1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE 2 1000000000000000
gcc -O2 -I tools/c -o sstat holdouts/1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE/c/sstat.c && ./sstat 1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE 100000000
python3 holdouts/1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE/py/pieces.py && git diff --exit-code holdouts/1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE/lean
python3 holdouts/1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE/py/framemap.py verify 14
python3 holdouts/1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE/py/gen_c.py && git diff --exit-code holdouts/1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE/c
gcc -O2 -o framemap holdouts/1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE/c/framemap.c -lm && ./framemap run 100000000000000000000 1000000000
python3 holdouts/1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE/py/tent.py                 # how many rounds the digits of u predict
gcc -O2 -o rounds holdouts/1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE/c/rounds.c -lm && ./rounds 100000000000 10000000000
python3 holdouts/1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE/py/rules.py                # the wiki's rules and their step counts against the machine and the Lean map
```

## Later

- Find the higher-level rule (one sweep or round to the next) and which sizes lead to an undefined case, as was
  done for the all-ones lengths of `1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_---0RE`.
