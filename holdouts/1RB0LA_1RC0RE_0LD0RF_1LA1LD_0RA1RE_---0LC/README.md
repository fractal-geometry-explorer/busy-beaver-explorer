# 1RB0LA_1RC0RE_0LD0RF_1LA1LD_0RA1RE_---0LC

bbchallenge id 91503, group G08 (two-sided sqrt growth). Whether it halts from blank tape is **open**: the epoch map is known for seven of eight tails for every size; the eighth (S1) runs a binary counter and is not understood. Pages:
[`explainer.html`](../../pages/holdouts/1RB0LA_1RC0RE_0LD0RF_1LA1LD_0RA1RE_---0LC/explainer.html),
[`proof-status.html`](../../pages/holdouts/1RB0LA_1RC0RE_0LD0RF_1LA1LD_0RA1RE_---0LC/proof-status.html), both built from
[`status.json`](status.json).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LA |
| B | 1RC | 0RE |
| C | 0LD | 0RF |
| D | 1LA | 1LD |
| E | 0RA | 1RE |
| F | --- | 0LC |

## What it does

**Where it can halt.** Only in F reading a 0; F is entered only from `C>1` (write 0, move right). So the machine halts
exactly when `C>1 0` occurs. In the first 10^8 steps F is entered 6,823,520 times, always onto a 1.

**Main regime** (sampled at each new left end in state A):

    Q a R  =  A>(01110)^a 0 1111 (001)^a R,       R = (01111)^b ...

One round trip eats the first reservoir block `01111` and adds a block to each repeat:
`Q (a+1) (01111 01111 R) -> Q (a+2) (01111 R)` in 28a+55 steps, for every R (the rest of the tape is never read).
The left end is visited twice per trip; the half-way sample reads `A>0 0 11111 (00111)^a (100)^(a+1) (10111)^b ...`.

**Eater regime.**

    Z a c d  =  A>(01110)^a 0 1111 (001)^c 1 1 0 0 1 0 0 1 1 1 1 (001)^d 1 1 0 0 1

A small machine at the right end changes shape every trip and returns to `1 1 0 0 1` every 14 trips, 4 blocks
`001` further left: `Z (a+1) (c+1) (d+9) -> Z (a+15) (c+1) (d+5)`. It needs a few hundred irregular trips to settle
into this cycle at the start of the regime.

**Big cycles** (`py/phases.py`): Q with b = 292, Q with 296, Z with c = 293 and d = 278 ... 2 (to 22,188,348 steps),
a transition, Q with b = 2362 (from 54,698,577), Q with 2366, Z with c = 2363 (from 217,524,700, still running at
3·10^8). The reservoir grows about 8x per big cycle.

**Epochs** (`py/epochs.py`, `c/epochs.c`). Call `E(n, S) = A>(01111)^n S`, with S at most 60 cells, an epoch.
Along the run they occur at steps 42,291 (n = 63), 853,349 (293), 54,698,577 (2363) and 3,502,378,736 (18924).
Starting the machine on `E(n, S)` (blank elsewhere), the next epoch has one of six tails:

    S0 0011110111110111   S1 00111101111001   S2 0011110111101111001111000111
    S3 001111011110111    S4 0011110111100111 S5 00111101111001100111

(plus rarer ones from S1). For S0, S2, S3, S4, S5 the next tail depends only on n mod 4, and n' is affine in n on
each class (checked at n = 100-115 and 400-407; `epochs.py table N`):

| from | n ≡ 0 | n ≡ 1 | n ≡ 2 | n ≡ 3 |
|---|---|---|---|---|
| S0 | S1, 8n+23 | S0, 8n+19 | S1, 8n+17 | S1, 8n+20 |
| S2 | S1, 8n+54 | S3, 8n+52 | S4, 8n+53 | S0, 8n+50 |
| S3 | S0 | S1 | S4 | S3 |
| S4 | S0 | S1 | S4 | S3 |
| S5 | S3 | S0 | S1 | S4 |

From S3, S4 and S5, n' grows by 18 per 4 in n (n' ≈ 4.5n; e.g. S3: 1799 at n = 400, 449 at n = 100). This predicts the run:
293 ≡ 1 gives `E(2363, S0)`, and 2363 ≡ 3 gives `E(18924, S1)`, which the run reaches at step 3,502,378,736. From
S1 there is no such pattern. For n = 100-179, n' − 8n jumps around (roughly 3.5n for odd n, 10n-14n for even n),
and the tail is any of S0-S5 or a new one. An S1 epoch carries a second long counter (a list `(001111)^k` made
from the reservoir), so it contains an epoch structure of its own.

## The epoch map for every size (13 Nov 2026; symbolic runs, not Lean)

`py/closure/epochmap.py classes` runs the accelerated simulator `py/closure/accel.py` from `E(n, S)` with
n = r + 4x and x a free variable. The simulator refuses any step whose outcome depends on x, so a run that ends at
`E(k + c x, S')` holds for every x >= 0. Result for n >= 2000 (28 classes, `py/closure/epoch_classes.json`):

| from | n ≡ 0 | n ≡ 1 | n ≡ 2 | n ≡ 3 (mod 4) |
|---|---|---|---|---|
| S0 | S1, 8n+23 | S0, 8n+19 | S1, 8n+17 | S1, 8n+20 |
| S2 | S1, 8n+54 | S3, 8n+52 | S4, 8n+53 | S0, 8n+50 |
| S3 | S0, (9n−2)/2 | S1, (9n−3)/2 | S4, (9n−2)/2 | S3, (9n−1)/2 |
| S4 | S0, (9n−4)/2 | S1, (9n−5)/2 | S4, (9n−4)/2 | S3, (9n−3)/2 |
| S5 | S3, (9n+8)/2 | S0, (9n+7)/2 | S1, (9n+6)/2 | S4, (9n+7)/2 |
| S6 | S3, 8n+42 | S1, 8n+38 | S4, 8n+43 | S0, 8n+40 |
| S7 | S4, (9n+18)/2 | S3, (9n+19)/2 | S0, (9n+18)/2 | S1, (9n+17)/2 |

S6 = `0011110111110011110111` and S7 = `0011110111101111001` are the two rarer tails. No class halts, and every class
leads to S0, S1, S3 or S4: the tails S2, S5, S6, S7 arise only from S1. `epochmap.py validate` compares every class at
x = 0 and x = 1 with the plain simulator `c/epochs.c`: next n, next tail and step count agree in 56 of 56 runs. The
map is a result of our tool; it is not in Lean.

The run from blank tape, accelerated (`epochmap.py run 300`): n = 63, 293 (S0), 2363 (S0), 18924 (S1, step
3,502,378,736), 350131 (S3, step 1,196,474,995,557), 1575589 (S3, step 24,366,344,552,101), 7090149 (S1, step
493,555,240,386,637). No halt up to there.

## Inside an S1 epoch: a binary counter (observed)

`epochmap.py s1 400` prints the tape right of the big block during the epoch from `E(400, S1)`:

1. The reservoir is turned into a block `(110011)^k`, k about n/2 (k = 200 for n = 400), right of two big blocks
   `(100)^N`.
2. The right-end eater takes the blocks `110011` one at a time. Between the second big block and the eater a binary
   number appears: a leading `11100`, then `100` for the digit 0 and `11100` for the digit 1. It goes up by one for
   every two blocks eaten (1, 10, 11, 100, ..., 1100010 = 98 after 196 blocks), and each new digit costs the big block
   one word `100`.
3. When the blocks `110011` are used up the eater takes the number apart, lowest digit first (50 round trips for the
   7 digits at n = 400), leaving a word on its right that depends on the digits.
4. Then the eater eats the two big blocks (the 14-trip cycle of the eater regime) and the epoch ends.

So the outcome of an S1 epoch depends on the binary digits of about n/4; that is why n' − 8n shows no residue
pattern. `epochmap.py s1map 2000 2300` and `s1map 5000 5200`: none of these 500 epochs halts, n' is between 11.5n and
22.5n, and the next tail is one of S0 ... S7 (S3 144 times, S1 106, S2 72, S0 63, S4 46, S5 28, S6 22, S7 19).

**Step 3 is not a finite-state process** (`epochmap.py unwind SEED 200 DIGITS`): on tapes of the shape of step 2 with
a random number in place of the counter, the part of the tape right of the remaining digits takes 114 different
values for numbers of up to 6 digits, 524 for up to 12 and 1,221 for up to 24 (longest 60, 80, 90 cells). None of the
600 samples halts. A finite set of classes, the method of 1RB0RD_1RC0LF_1LA0LB_---1RE_1LB1RA_0LC0RA, therefore does
not cover S1 epochs.

## What is proved

- `lean/Blank.lean` (generated): halting configurations; 10^4 steps by the kernel, 10^7 by `native_decide`.
- `lean/Rules.lean` (generated by `py/gen_rules.py`, `tools/py/bbtools/symtm.py`): `trip1` (one trip of Q) and
  `cycle3` (14 trips of Z), kernel, for all sizes. `cycle3` is a 0.8 MB proof; the file takes ~2 minutes.
- `lean/Phase.lean` (kernel): `Q_step`, `Q_iter`, `Z_step`, `Z_iter` (re-bracketing and induction).
- `lean/Reach.lean`: `reach_Q : steps 853764 init = some (Q 5 ((01111)^287 T))` and `reach_Z : steps 4090752 init =
  some (Z 359 293 278)` (bounded runs by `native_decide`), then `reach_Q_end`, `reach_Z_end` by the rules (kernel).

## Open, next steps

- **What is left is S1.** The other seven tails are settled by the 28 classes above (as a tool result; a Lean replay
  through the executor of `holdouts/1RB0RC_0RC1RC_0LD0RA_1LE0LF_0LA1LC_---1LA/lean/Exec.lean` is possible but was not
  done, because it would not decide the machine). For S1 a proof needs an invariant over all digit strings of the
  counter: what the eater leaves behind when it takes a number apart (step 3), as a function of the digits, and then
  that the eater regime started on that word reaches an epoch with one of the eight tails. The word grows with the
  number of digits, so this is an induction on the digit string, not a finite case list.

- The transitions: Q with reservoir 1 to the next regime, the start-up of the eater, and Z with d < 5 to the next
  big cycle, each as a symtm rule for all sizes (probably split by residues: the eater eats 4 blocks per period, so
  d mod 4 matters). With those, the big-cycle map would be explicit and the question reduces to arithmetic.
- The eater's start-up is irregular for hundreds of trips: it may need its own analysis (its shapes, a finite-state
  description) before a rule for all c can be stated.

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LA_1RC0RE_0LD0RF_1LA1LD_0RA1RE_---0LC/lean/check.sh    # ~2.5 minutes
python3 holdouts/1RB0LA_1RC0RE_0LD0RF_1LA1LD_0RA1RE_---0LC/py/phases.py 3e8                    # ~1 minute
python3 holdouts/1RB0LA_1RC0RE_0LD0RF_1LA1LD_0RA1RE_---0LC/py/epochs.py run 6e9                    # ~40 s
python3 holdouts/1RB0LA_1RC0RE_0LD0RF_1LA1LD_0RA1RE_---0LC/py/epochs.py table 400                  # ~40 s
D=holdouts/1RB0LA_1RC0RE_0LD0RF_1LA1LD_0RA1RE_---0LC/py/closure
python3 $D/epochmap.py classes          # ~1 minute: the 28 classes (S1 is reported undecided)
python3 $D/epochmap.py validate $D/epoch_classes.json   # ~8 minutes: 56 runs of the plain simulator
python3 $D/epochmap.py s1 400           # the binary counter
python3 $D/epochmap.py unwind 2 200 12  # ~1 minute
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB1RA_1LC0RB_1LE0LD_0LB1LD_0RA0LF_---0RE`](../1RB1RA_1LC0RB_1LE0LD_0LB1LD_0RA0LF_---0RE/README.md): rename A→B, B→C, C→E, D→A, E→D, F→F and exchange left and right; it is this table started in state D, in a mirror
- [`1RB0RE_0LC0RF_1LD1LC_1RA0LD_0RD1RE_---0LB`](../1RB0RE_0LC0RF_1LD1LC_1RA0LD_0RD1RE_---0LB/README.md): rename A→D, B→A, C→B, D→C, E→E, F→F; it is this table started in state B

<!-- end of related machines -->
