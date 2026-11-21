# 1RB0LF_1LC0RC_1RA1LD_0RB0LE_1LC0LB_---1LA

bbchallenge id 153488. One of the six-state holdouts whose halting from blank tape is open. **A base-4 counter of
walls in a sea of `110`**, incremented from the right end; walls drift, merge and are born. Analyzed by hand
(group G02, two passes); the sample-to-sample rules are worked out exactly and the main ones are proved in Lean for
carry chains of any length. Whether it halts is still open.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LF |
| B | 1LC | 0RC |
| C | 1RA | 1LD |
| D | 0RB | 0LE |
| E | 1LC | 0LB |
| F | --- | 1LA |

## What it does

**Sample point**: A on the last 1 at the right end of the tape. There the tape is

    0^inf  (110)^r1 W1  (110)^r2 W2  ...  (110)^rk Wk  (110)^last  10 1 A>1  0^inf

a list of *digits* `(110)^r W` (a run of r words `110`, then a wall W), then the last run. The walls:

| wall | cells | role |
|---|---|---|
| W0 | `11110` | digit 0 (its run r is odd) |
| W1 | `1100` | digit 1 (r even) |
| W2 | `1100 110 11110` | digit 2 (r even) |
| W3 | `1100 1100` | digit 3 (r even) |
| U | `11000` | a digit just reset by an overflow |
| T | `1110` | a U that has received one carry |
| S | `10` | the `10` at the left end (and a few other places): a digit with run 0 |

Example (step 1,999,977,989; the first-pass README's `1 2/2 2x22 ...` read as digits):

    [0]S [0]W1 [22]W1 [27]W0 [394]W3 [356]W3 [14920]W1 [4455]

**One sweep = add one.** The head starts at the right end, walks left across the *carry chain* (the W3 digits next to
the end), changes the first other digit (the *stop*) and walks back, turning every W3 of the chain into W0. The head
never goes further left than the stop, so most sweeps are short; it reaches the left end only when every digit is W3.
In digit form (left runs in brackets; `lean/Sweeps.lean`, any chain length):

| rule | before (stop, chain) | after |
|---|---|---|
| `sweep_w0` | `[2a+1]W0 [2c1]W3 ... [2cj]W3 [2z+1]` | `[2a]W1 [2c1+3]W0 [2c2+1]W0 ... [2z+1]` (j=0: last run 2z+3) |
| `sweep_w1` | `[2a+2]W1` + chain | `[2a]W2 [2c1+1]W0 [2c2+1]W0 ...` |
| `sweep_w2` | `[2a]W2` + chain | `[2a]W3 [2c1+3]W0 [2c2+1]W0 ...` (j=0: last run +2) |

So each digit cycles W0 → W1 → W2 → W3 → W0 (with a carry), a base-4 counter whose lowest digit is next to the head;
the wall positions are the digits' *places*. A digit's own left run goes −1, −2, 0, +3 around its cycle (net 0), but
the digit to its left takes 2 from it at each of its own W1→W2 and W3→W0 steps: **the run between two walls shrinks
by 4 per cycle of the left wall.** The last run grows by one word per sweep (the √t side of the run); the counter
overflows rarely (the log side).

**Edge events** (all found by the digit simulator below, each a symbolic run; the starred ones are Lean theorems):

- *Merger* (a run used up). A W1 with left run 0 that receives a carry cannot shorten its run: after a W0
  (`merge_w0_w1`\*) the two walls become one W0 with left run 2a+3 (one digit fewer); after a W2
  (`merge_w2_w1`\*) they become W1 and W0 with left run 3. Runs of 0 elsewhere (`W2 W2`, `W2 W3`, `W3 W0` ...) are
  harmless.
- *Overflow*. With the top `0^inf 10 1100` and every digit W3, the carry runs off the left: every W3 becomes U, the
  top becomes `0^inf 11110`, and a new digit `W1 [1]` is born at the right end (the sample right after ends in
  `1110 1 A> 1` instead of `10 1 A> 1`). Example, step 18,340,104:
  `[0]S [0]W1 [36]W3 [84]W3 [32]W3 [738]W3 [1153]` → `[0]W0 [0]U [37]U [85]U [33]U [737]U [1151]W1 [1]`.
- *Re-initialisation* after an overflow: a T walks left through the U's, `[b]U [a]T` + carry → `[b]T [a−1]W1`
  (`sweep_u_t`\*), one U per carry that reaches the T. When the T reaches the top, the top cycles
  `0^inf 11110 1110` (`[0]W0 [0]T`) → `0^inf 1100` (`[0]W1`) → `0^inf 10 110 11110` (`[0]S [1]W0`, `prefix_w1`\*)
  → `0^inf 10 1100` (`[0]S [0]W1`, `prefix_10_w0`\*) → overflow, one step per carry that reaches the top.
- *The left edge*. The first run behind the top loses 4 per overflow (43, 39, 35, ... at the first overflows) and
  is used up at about 6·10^9 steps: the top digits rearrange (`[0]W3 [1]W0 [1]W0 [257]W0 ...` →
  `[0]S [2]U [1]U [251]U ...`) and the next run (about 250) becomes the first. Nothing special happens: same rules.

**Halting**: F on a 0 is the only halt; F is entered only from A on a 1 moving left, so it halts iff `0 1 F> 1`
occurs (`halt_shape`). None of the rules above passes through that shape.

## Status

Open. The digit model is exact (checked against the direct run), and it has been run to 8.6·10^15 steps without a
halt or an unknown event, but the closure (a set of digit configurations that maps into itself) is not assembled.

- **Lean, kernel**: `lean/Sweeps.lean` (from `py/sweeps.py`, with `lean/Seq.lean` for lists): `sweep_w0`,
  `sweep_w1`, `sweep_w2`, `merge_w0_w1`, `merge_w2_w1`, `sweep_u_t`, `prefix_w1`, `prefix_10_w0`: each is one sweep
  for every value of the runs, **every carry chain ts (any length)** and every tape L beyond the stop.
  `lean/Rules.lean`: the shift rules of the sweeps and the halting shape. `lean/Blank.lean`: no halt in 10^7 steps.
- **Trusted** (`py/digits.py`): the digit simulator — each sweep a symbolic run of the machine on a window, cached by
  the window's shape — agrees with the direct run at all 30,218 sample points up to 2·10^9 steps (states and step
  counts); from there it ran 6.8·10^7 sweeps more, to 8.6·10^15 steps: no halt, no unknown shape, 22 overflows,
  using 303 window rules (72 shapes up to the length of the carry chain).
  (The long run was made with the scratch predecessor of `py/digits.py`, the same method; the 30,218-sample
  comparison was redone with the code of `py/digits.py`: 0 mismatches.)
- **Trusted**: no halt in 10^9 steps (C).

## Notes for later

What a non-halting proof still needs, and where it is blocked:

1. **The overflow for any chain length.** `seqtm` can cross the chain leftwards but not back: after the top, the
   head comes back in state C over `(110110)^c 11011011`, and the one-block run needs a re-bracketing that `seqtm`
   does not do (`symtm` with `rotate=True` does it for fixed lengths). Either teach `seqtm` to rotate, or write the
   chain element in another bracketing for this rule.
2. **The language.** Unconstrained digit lists are not closed: a T or U elsewhere than right after the top / a U,
   or runs of the wrong parity, lead to runs that touch unknown tape. The reachable configurations (as observed) have
   (a) U's only in one block right after the top, then at most one T; (b) the parities of the table; (c) runs of
   0 only in a few adjacent pairs (`W0 W1`, `W2 W1`, `W2 W2`, `W2 W3`, `W3 W1`, `S W1`, `T W1` ...). A bigram language
   over (wall, run class 0/1/2/.../≥6) with the left neighbour as context is the candidate; checking it means
   running every window case symbolically (the script `py/digits.py` already derives the cases one by one).
3. **Assembly in Lean.** An encoding `enc : List Digit → Tape` written exactly as `seqtm` writes the left tape, one
   rule theorem per case of item 2, and `rep_rotate` equalities between the end tapes the rules write and `enc` of
   the next configuration; then `TM.not_halts_of_forall` with induction over sample points.

## Reproduce

```sh
python3 holdouts/1RB0LF_1LC0RC_1RA1LD_0RB0LE_1LC0LB_---1LA/py/digits.py check 3e6        # digit model vs direct run
python3 holdouts/1RB0LF_1LC0RC_1RA1LD_0RB0LE_1LC0LB_---1LA/py/digits.py far 1e6 300000 50000
python3 holdouts/1RB0LF_1LC0RC_1RA1LD_0RB0LE_1LC0LB_---1LA/py/sweeps.py > holdouts/1RB0LF_1LC0RC_1RA1LD_0RB0LE_1LC0LB_---1LA/lean/Sweeps.lean
python3 holdouts/1RB0LF_1LC0RC_1RA1LD_0RB0LE_1LC0LB_---1LA/py/rules.py > holdouts/1RB0LF_1LC0RC_1RA1LD_0RB0LE_1LC0LB_---1LA/lean/Rules.lean
gcc -O2 -o tok holdouts/1RB0LF_1LC0RC_1RA1LD_0RB0LE_1LC0LB_---1LA/c/tok.c && ./tok 1RB0LF_1LC0RC_1RA1LD_0RB0LE_1LC0LB_---1LA 2000000000 A 1 R 0 100000000 0 > samples.txt
gcc -O2 -o nbhd holdouts/1RB0LF_1LC0RC_1RA1LD_0RB0LE_1LC0LB_---1LA/c/nbhd.c && ./nbhd 1RB0LF_1LC0RC_1RA1LD_0RB0LE_1LC0LB_---1LA 1000000000 F 1
```

## Deep exact run

No halt in the first 4.48x10^19 steps: the macro simulator `holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/c/msim.c` with blocks of 6 cells ran
from blank tape to step 44,851,509,440,286,316,893. It is exact, and at this block size it agrees with the
direct simulator after 2,000,027,050 steps (`python3 holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/deep.py run 240`, then `verify`).

## Long accelerated run (16 November 2026)

**Trusted, bounded: no halt in the first 3.55·10^38 steps.** `py/macro4.py` runs the digit model of `py/digits.py`
many sweeps at a time. It does not change the model: every macro is a symbolic run of `digits.py` sweeps.

- **Macros.** `Inc(0)` is one sweep. `Inc(k)` repeats `Inc(k-1)` until the highest changed digit, counted from the
  bottom, is at least k. A macro is derived symbolically once per *window key*. The key holds the walls of the k+1
  lowest digits, and each run in it is either its exact value or "big" (≥ B(k, i) = 8 + 4^(k-i+1) below the top
  digit, ≥ 16 at the top and beyond it). The macro's effect is affine in the big runs, and a run is counted as big
  only when every comparison the sweeps make is decided over the whole region. A key whose sweeps meet a case that
  cannot be decided falls back to `Inc(k-1)`, and at level 0 to a plain sweep. KMAX = 64.
- **Cycles.** When the same macro key repeats with a constant drift D in the runs, K rounds are applied at once. K
  is the largest number for which every run that moves stays above its threshold. The state at round K is checked
  to give the same key again.
- **Tests** (states and step counts at every landing point, against plain `digits.py` sweeps):
  - from 3·10^7 steps, 3.0·10^7 sweeps (2,855 landing points);
  - from the state at 5·10^19 steps, 10^6 sweeps (257 landing points, 42 cycle skips);
  - on the twin (below);
  - 0 mismatches in all of them.
- **Run.** It starts at the sample 3.0·10^7 steps. 1.6·10^11 sweeps took it to 3.81·10^22 steps, then 2.0·10^19
  sweeps more to **355,306,997,422,069,216,532,069,485,630,435,691,812 ≈ 3.55·10^38 steps**. There was no halt,
  and no window that could not be read back as digits. 20,981 macros were derived and applied 13.3 million times.
  The run passed the previous bounds (8.6·10^15 for the digit model, 4.48·10^19 for msim). At the end the tape is
  `[0]W0 [0]T [11336]W2 [3662]W3 [178638]W1 ...` with 34 runs, the largest about 5.2·10^18.
- The same code covers the twin 1RB1LA_0LC0RE_1LD1LB_1RE1LF_1RC0RA_0RC--- (`twin` argument). See that machine's
  README.

```sh
python3 holdouts/1RB0LF_1LC0RC_1RA1LD_0RB0LE_1LC0LB_---1LA/py/macro4.py test 3e7 30000000        # macros vs plain sweeps
python3 holdouts/1RB0LF_1LC0RC_1RA1LD_0RB0LE_1LC0LB_---1LA/py/macro4.py run 3e7 3600 main.pkl     # resumable checkpoint
```

## Top-part forecast and condition macros (21 November 2026, group C)

**Exact bound unchanged** (the region-memo bound 6.97·10^153 stands). **Forecast: no halt at any top-level timer event for at
least 2.26·10^6 overflow cycles after 4.79·10^63 steps** (trusted computation of a reduced model; the reduction is an argument
checked on data, not a proof).

- `py/cmacro.py` (exact): from the 16 November state at 3.55·10^38 it reached step
  4,793,665,653,522,497,960,519,246,549,042,984,084,070,144,923,733,051,616,030,988,496 (4.79·10^63) in 600 s, passing the
  first top-level timer events of that state (its top runs 11,336, 3,662, 178,638 and 156,728 were used up and merged; the
  top run at 4.79·10^63 is 7,220,965, the former 8,273,482); no halt, no unknown window. Test: `python3 py/cmacro.py py/macro4.py test 3e7 2000000 main`
  (4,472 landing points, 2.0·10^6 sweeps, 0 mismatches against plain digits.py sweeps). It is not faster than regaccel at depth.
- **Method** (`py/forecast.py`, code in `holdouts/1RB0LF_1LC0RC_1RA1LD_0RB0LE_1LC0LB_---1LA/py/forecast.py` and `cmacro.py`). The digit model counts at the bottom, and a carry reaches a digit only through carry walls, so the first P digits (the *top part*) see only carries arriving from below; the lower part decides only *when*. The top part is therefore followed alone: the top P digits of an exact state are kept, the rest is replaced by 3 zero digits with runs of 10^60 (the *reduced model*), and the reduced tape is run by `cmacro.py`, an exact macro engine over the same digits.py window rules (macro keys hold only walls, small runs and parities; every comparison on a big run is recorded as a linear condition and checked at each application). One overflow cycle of the top part is a translation of its runs while none is near exhaustion, so K cycles are jumped at once (top += K·D); near an exhaustion the cycles are run one by one. A merge at index j changes only digits j-1 and j, so the forecast of the top part holds until the real run at index P-1 (lifetime run/|D|) is used up. The forecast says nothing about step counts (they depend on the lower part) and assumes the lower part keeps delivering carries, which is what every exact run so far shows. 
- Check of the reduction: from 3.55·10^38, the exact run and the reduced model (P = 16) give the same top 7 digits at all
  1,984 top events compared (to about 10^63): 0 mismatches. (P = 9 fails after 1,146 events, when merges bring the fake digits
  into the compared window, as expected.)
- Forecast from the exact state at 4.79·10^63 (52 digits, top `[0]W1 [7220965]W0 [419154193]W0 [9371979629]W0 [1116859675]W0
  [11231167]W0 ...`): one overflow cycle moves the run at index i by -4^i. With P = 42 (horizon: index 41, run 1.09·10^31,
  2.26·10^6 cycles) the timer events are at cycle 10,968 (index 5, the run 11,231,167, merge W0 W0), 1,742,014 (index 6) and
  1,805,240 (index 1, the left-edge run 7,220,965); all are ordinary merges. Continued to 1.1·10^8 cycles (two more: index 5 at
  60,257,693 and the left-edge run again at 99,372,823) under the argument that merges above index 41 only lengthen its life
  (x4 per merge). No STOP (halt, split or unparsed window) in any of it.
- Rough scale: the left-edge run lost 3,761 between 4.79·10^63 and the state of a 600 s region-memo run at 10^145 (where it
  is 7,217,204 words 110), about 940 cycles, so
  a cycle is about 0.087 decimal digits of steps at this depth; cycle 10,968 is near 10^1000 steps, cycle 2.26·10^6 near 10^200000.
- Next deciding event: the forecast's horizon (index 41 used up, after 2.26·10^6 cycles; or, with the extension, about
  1.1·10^8). Beyond it the top part depends on digits born after 4.79·10^63.

```sh
python3 holdouts/1RB0LF_1LC0RC_1RA1LD_0RB0LE_1LC0LB_---1LA/py/forecast.py test 60
python3 holdouts/1RB0LF_1LC0RC_1RA1LD_0RB0LE_1LC0LB_---1LA/py/forecast.py run saved 42 3 2.2e6 1700 out.pkl
```

## Pages

- [`pages/holdouts/1RB0LF_1LC0RC_1RA1LD_0RB0LE_1LC0LB_---1LA/explainer.html`](../../pages/holdouts/1RB0LF_1LC0RC_1RA1LD_0RB0LE_1LC0LB_---1LA/explainer.html)
- [`pages/holdouts/1RB0LF_1LC0RC_1RA1LD_0RB0LE_1LC0LB_---1LA/proof-status.html`](../../pages/holdouts/1RB0LF_1LC0RC_1RA1LD_0RB0LE_1LC0LB_---1LA/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LF_1LC0RC_1RA1LD_0RB0LE_1LC0LB_---1LA/lean/check.sh
```
