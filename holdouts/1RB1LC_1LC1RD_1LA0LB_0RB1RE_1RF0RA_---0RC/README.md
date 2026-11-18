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
to the next. The rules are not stated in Lean; the cases they are made of are (`next_sound`, `none_halts`,
`halts_iff` in `lean/Phases.lean`), each with its step count in its piece theorem in `lean/Pieces.lean`.
`py/rules.py` checks the rules and step counts against direct simulation (3,418 tapes A(a, b) with a, b < 60, and the
238 visits of the first 10^7 steps from blank tape) and against the Lean cases (the same tapes, the same run, and the
Lean map for 5*10^5 frames, 685 visits). Example: A(1, 7) halts after 27 + 82 + 79 + 176 + 79 + 431 + 11 = 885 steps
(A(5, 6), A(4, 14), A(12, 9), A(4, 21), A(12, 16), A(28, 3), halt), as direct simulation gives.

## Status

Open. Lean (`lean/Blank.lean`): the halting configurations (`step_none_iff`), no halt in 10,000 steps by the kernel, in 10,000,000 by `native_decide`. C: no halt in 10^9 steps (`tools/c/triage.c`) and in 10^15 steps (`c/mrun.c`, exact macro simulation). Lean (`lean/Phases.lean`, on `lean/Pieces.lean` generated by `py/pieces.py`): the whole frame map, 30 cases over 6 tape shapes, for all sizes (`next_sound`); the undefined cases halt (`none_halts`); the machine halts iff the orbit of `Ph.e 1 0` reaches one (`halts_iff`); not in the first 10^8 frames (`no_halt_phases`, `native_decide`; about 5.95*10^11 steps). Open: whether the orbit ever gets there.

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
```

## Later

- Find the higher-level rule (one sweep or round to the next) and which sizes lead to an undefined case, as was
  done for the all-ones lengths of `1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_---0RE`.
