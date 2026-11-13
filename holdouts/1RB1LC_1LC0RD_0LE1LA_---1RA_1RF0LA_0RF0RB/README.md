# 1RB1LC_1LC0RD_0LE1LA_---1RA_1RF0LA_0RF0RB

bbchallenge id 96840. One of the six-state holdouts whose halting from blank tape is open.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LC |
| B | 1LC | 0RD |
| C | 0LE | 1LA |
| D | --- | 1RA |
| E | 1RF | 0LA |
| F | 0RF | 0RB |

Blocks of 1s separated by gaps of one or two 0s. A single 0 (a *hole*) travels right through a block, the head comes
back, and what happens next depends on the parity of the block it crossed. The machine halts exactly when the head
meets a block of one 1 (in state A) or of two 1s (in state F); from blank tape that has not happened in 10^2000 steps
of an exact accelerated simulation. The event model below is complete enough to simulate with, but only part of it is
in Lean, and no proof either way is known.

## What it does

The tape is always a row of blocks of 1s. Blocks left of the head are separated by a single 0, blocks right of the
head by `00`; the right end of the tape counts as `00`. Every time a hole reaches the right end of a block, three 1s
are added to the front of the next block on the right (or a new block `111` is made at the right end of the tape):
this is the only way the tape grows on the right, two cells at a time.

1. **Travelling hole** (`walk`, Lean). `A> 0 1 1 1 -> 1 A> 0 1 1` in five steps: the 0 under the head moves one cell
   right. It runs to the end of the block.
2. **Sweep at a 00 gap** (`e_g2`, `g2_odd`, `sweep`, Lean). With the head in state E on a gap,
   `1^x E> 00 1^y 00 R` and y odd, y >= 5, one 1 goes left, the hole crosses the rest, and the head is back at the
   gap: `1^(x+1) E> 00 1^(y-4) 00 111 R`. The middle block loses four 1s per sweep: one to the left, three to the
   right.
3. **End of a sweep run.** y = 1: the 1 and the next block merge, `1^x E> 00 1 00 1^z -> 1^(x+2) E> 00 1^(z+1)`
   (`e_one`, Lean). y = 3: the left block is closed off by a single 0 and the three 1s join the next block,
   `1^x E> 00 111 00 1^z -> 1^(x+1) 0 E> 00 1^(z+3)` (`e_three`, Lean; `end3` when the next block is the blank end).
4. **Even blocks: the merge.** If the block the hole crossed is even, the head does not stop at the `00` gap: it
   comes back on the second 0 of the gap (`0 A> 0 1^n`), the hole travels again (n - 2, three more 1s on the right),
   and the head ends on the single 0 between the block and its left neighbour, `1^x A> 0 1^n`. Now the hole merges the
   two blocks into one of x + n - 2 and the head walks left across it. If x + n is even it stops on the next single 0
   and merges again; if x + n is odd it goes on to the left end of the tape, turning every single 0 into `00` and
   taking one 1 off each block it passes (simulation).
5. **Left end.** At the left end of the tape, `A> 0 1^a 00 1^b`, the first block is emptied two 1s at a time into the
   second, three for two (`left`, Lean): a factor 3/2. When it is empty the head starts sweeping from the left,
   `A> 000 1^n 00 ...`, a *round start*.

Round starts from blank tape (step, tape): 5,241 `1^27 00 1^21`; 34,599 `1^137 00 1^3`; 127,627 `1^233 00 1^3`;
1,669,069 `1^737 00 1^3`; 3,292,853 `1^1121 00 1^3`; 7,014,825 `1^1697 00 1^3`; 16,118,863 `1^2567 00 1^3`; …
There are 15,707 round starts in the first 10^2000 steps; 3,497 of them have a single block, and at most 23 runs of
equal cells are on the tape at any record. A long stretch of single-block rounds multiplies n by 3/2 each time
(6186294186981, 9279441280491, 13919161920747, …); in between the tape breaks into several blocks whose sizes depend
on residues mod 2 and mod 4 of the block lengths.

The left side of the tape holds the blocks and grows with them (a round of block size n costs about n^2 steps: the
sqrt side). The right end moves two cells each time a hole reaches it (the log side).

## Does it halt?

The only undefined transition is D0, and D is entered only by B reading a 1. Two local patterns lead there, both
proved in Lean:

- `A> 0 1 0`: state A arrives on a 0 followed by an isolated 1 (`halt_a`, two steps). A round start with n = 1,
  `A> 000 1 00`, halts this way after 8 steps (`halt_start`).
- `F> 1 1 0`: state F, which runs right over a gap after E, finds a block of exactly two 1s (`halt_f`), e.g. a sweep
  with y = 2.

So the machine halts when a hole or a sweep meets a block of length 1 or 2 with the wrong parity. Blocks that small
do appear at the right end (every new block starts as `111` and grows by threes), so the question is whether one of
them is ever met at exactly the wrong size. Started from `A> 000 1^n 00 1^m` with small n, m the machine does halt
for some values (n = 1, n = 2, (n, m) = (17, 5), (18, 2), …), so a proof of non-halting has to use what the real run
keeps. From blank tape `py/accel.py` finds no halt in 10^2000 steps.

## For later

- Lean has the hole, the odd sweep, the two ends of a sweep run and the halting patterns, but not the even-block
  return (`0 0 1^(2k) A> 0 1 1 0 0 -> 0 A> 0 1^(2k) 0 0 1 1 1`), the merge and the leftward pass of item 4: symtm
  needs the block once as `1^n` (hole going right) and once as `(11)^k` (head coming back), so these have to be
  proved in two halves and joined with `TM.rep_rotate`. With them the event model can be written as a Lean function
  on lists of block lengths and `HaltsFromBlank <-> the orbit meets a block of 1 or 2` stated as for the other
  reduced machines.
- Write the event model as a map on block lists (py) and check it against `py/accel.py` record by record; then look
  for an invariant of the real run (for example on the residues of the small right-hand blocks, which are 3, 6, 9,
  12, … when created) that excludes the halting patterns.

## Files

- `lean/Rules.lean`: `left`, `sweep`, `end3`, `walk`, `e_g2`, `e_one`, `e_three`, `g2_odd`, `halt_start`, `halt_a`,
  `halt_f`, for all values of their counts and any tape outside the pattern, generated by `py/gen_rules.py`
  (`bbtools.symtm`).
- `py/accel.py`: exact accelerated simulator on a run-length tape (hole walks, A/C runs and F runs in one move, and
  jumps over repeated sweeps and transfers). `--rounds` prints the round starts.
- `c/rounds.c`: plain simulator printing the round starts, to check `py/accel.py` (identical for 6·10^10 steps; with
  the jumps switched off, `BLKP=0`, `py/accel.py` gives the same round starts as with jumps for 4.7·10^12 steps).
- `c/holes.c`: prints the run-length tape at each reversal of the head next to a `00` hole.

## Status

Open. Lean: `step_none_iff`, no halt in 10,000 steps by the kernel and in 10^7 by `native_decide` (`lean/Blank.lean`),
and the eleven rules above (`lean/Rules.lean`, kernel). C (`tools/c/triage.c`): no halt in 10^9 steps. Accelerated
simulator (`py/accel.py`, jumps not proved, checked against the plain machine for 6·10^10 steps): no halt in 10^2000
steps.

## Pages

- [`pages/holdouts/1RB1LC_1LC0RD_0LE1LA_---1RA_1RF0LA_0RF0RB/explainer.html`](../../pages/holdouts/1RB1LC_1LC0RD_0LE1LA_---1RA_1RF0LA_0RF0RB/explainer.html)
- [`pages/holdouts/1RB1LC_1LC0RD_0LE1LA_---1RA_1RF0LA_0RF0RB/proof-status.html`](../../pages/holdouts/1RB1LC_1LC0RD_0LE1LA_---1RA_1RF0LA_0RF0RB/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LC_1LC0RD_0LE1LA_---1RA_1RF0LA_0RF0RB/lean/check.sh
PYTHONPATH=tools/py python3 holdouts/1RB1LC_1LC0RD_0LE1LA_---1RA_1RF0LA_0RF0RB/py/gen_rules.py
python3 holdouts/1RB1LC_1LC0RD_0LE1LA_---1RA_1RF0LA_0RF0RB/py/accel.py 1e2000 --rounds | tail -3
gcc -O2 -o rounds holdouts/1RB1LC_1LC0RD_0LE1LA_---1RA_1RF0LA_0RF0RB/c/rounds.c && ./rounds 1RB1LC_1LC0RD_0LE1LA_---1RA_1RF0LA_0RF0RB 3000000000
```
