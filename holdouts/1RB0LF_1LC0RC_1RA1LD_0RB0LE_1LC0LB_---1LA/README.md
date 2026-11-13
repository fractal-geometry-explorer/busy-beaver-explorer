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

## Pages

- [`pages/holdouts/1RB0LF_1LC0RC_1RA1LD_0RB0LE_1LC0LB_---1LA/explainer.html`](../../pages/holdouts/1RB0LF_1LC0RC_1RA1LD_0RB0LE_1LC0LB_---1LA/explainer.html)
- [`pages/holdouts/1RB0LF_1LC0RC_1RA1LD_0RB0LE_1LC0LB_---1LA/proof-status.html`](../../pages/holdouts/1RB0LF_1LC0RC_1RA1LD_0RB0LE_1LC0LB_---1LA/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LF_1LC0RC_1RA1LD_0RB0LE_1LC0LB_---1LA/lean/check.sh
```
