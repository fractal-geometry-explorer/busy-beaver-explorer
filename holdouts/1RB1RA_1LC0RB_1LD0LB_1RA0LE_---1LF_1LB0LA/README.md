# 1RB1RA_1LC0RB_1LD0LB_1RA0LE_---1LF_1LB0LA

bbchallenge id 55074. One of the six-state holdouts whose halting from blank tape is open (group G07, family: **Collatz-like (3z/2) phases with a growing block stack**).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RA |
| B | 1LC | 0RB |
| C | 1LD | 0LB |
| D | 1RA | 0LE |
| E | --- | 1LF |
| F | 1LB | 0LA |

## What it does

After a few hundred steps the run is a sequence of **phases**. A phase starts with the tape `P 0^z` and the head just
right of it, in state B on a blank (`P 0^z B>0`), where P is a prefix of a few hundred to a few thousand cells.

- **Sweeps.** The head zig-zags left through the block of 1s at the right end, bites four 0s off the zero block and
  returns: `0^z 1^b` becomes `0^(z-4) 1^(b+6)`. Proved for all sizes in Lean (`lean/Sweep.lean`):
  `L (00)^(a+2) (11)^(b+3) A> blank` reaches `L (00)^a 1^(2b+12) A> blank` in `10b + 38` steps.
- **Phase end.** When one or three 0s are left (z is always odd), the head walks into P, rewrites its right end, and
  turns the whole block of 1s into the next zero block. The new zero block is

      z = 4k+1  ->  z' = 6k+1          z = 4k+3  ->  z' = 6k+7          (+ a rare bonus c, below)

  so z runs 11, 19, 31, 49, 73, 109, 163, 247, 373, 559, 841, 1261, ... (z' about 3z/2). The phase that starts at z
  begins near step 0.77 z^2; phases grow by a factor of about 9/4 in steps.
- **The stack.** P is a list of blocks (1s in multiples of 6, even runs of 0s), e.g. after phase 30
  `1^6 0^24 1^6 0^24 1^12 0^18 1^6 0^4 1^12 0^18 1^6 0^4 1^6 0^10 1^6 0^8 1^6 0^4 1^6`. Each phase end rewrites only
  its last few blocks, according to z mod 4: with z = 3 mod 4 the last zero block shrinks by 4 and the last block of
  1s grows by 8 (the same game one level down); with z = 1 mod 4 a new short pair such as `0^12 1^6` is split off.
  When an inner zero block runs out, the walk reaches one level deeper and the next outer zero block gets a bonus
  c: 62 (five times), 56, 98, 146, 26 and 50 in the first 900 phases, 0 in all the others. P grows by about 4.5
  cells per phase (4,056 cells after 900 phases); no phase end rewrote more than the last 7 blocks (106 cells), and
  the first 60 cells have not changed since phase 5.

The residues z mod 4 look like coin tosses (466 phases with 1, 434 with 3 in the first 900), so the stack is a
record of a Collatz-like sequence.

**Halting** needs state C on a 0 with `0 1` to its left (C0 -> 1LD, D1 -> 0LE, E0 halts). It never happens inside a
sweep, so a halt would have to come from a phase-end walk into the stack.

## Evidence

- `c/phase.c` runs one phase cell by cell; `py/check_full.py` runs the first phases with the true z and compares with
  the reduced map below (the first 25 phases agree, to step 101,946,644,740; the phase starts are the steps of the
  plain simulator: 218, 546, 1220, 2618, 5394, 10908, ...).
- `py/drive.py` iterates the phases far beyond direct simulation: each phase is run with a small stand-in zero block
  of the same residue mod 4 (larger than anything in P; rechecked every 25 phases with one twice as large) and the
  true z is carried exactly. **900 phases ran with no halt**; z then has 160 digits and the machine has made about
  10^319 steps. This rests on the observation, not a proof, that a phase depends on z only through z mod 4 once z is
  large compared to P (heuristic trust level). `notes/phases.txt` lists the residue, bonus and prefix length of each
  phase.

## Status

Open. Proved in Lean: the halting configurations and 10^7 steps without a halt (`lean/Blank.lean`, generated), and
the sweep rule for all sizes (`lean/Sweep.lean`, kernel). Computed: the phase structure for the first 25 phases
(trusted), and no halt in 900 phases with the reduced map (heuristic, about 10^319 steps).

## Next steps

- Prove the phase-end walks in Lean for general z (one shift-rule chain per stack shape and residue), which would
  make the reduced map exact.
- Understand the stack as a counter driven by z mod 4: which sequences of residues let a walk reach the left end,
  and whether the halting pattern `0 1 C>0` can appear there. That looks like a question about the coin-toss
  sequence of a Collatz-like map, and may be out of reach.

## First look

Growth class **fixed/sqrt** (left: fixed, exponent 0.0; right: sqrt,
exponent 0.489). After 1,000,000,000 steps: 40,047 cells visited (31 left of the
start, 28,737 right), 22,701 ones.

- right, step 970,103,100: `1^6 0^24 1^6 0^24 1^12 0^18 1^6 0^4 1^6 0^12 1^6 0^18355 1^21020 A>0`
- right, step 985,766,418: `1^6 0^24 1^6 0^24 1^12 0^18 1^6 0^4 1^6 0^12 1^6 0^17771 1^21896 A>0`

## Pages

- [`pages/holdouts/1RB1RA_1LC0RB_1LD0LB_1RA0LE_---1LF_1LB0LA/explainer.html`](../../pages/holdouts/1RB1RA_1LC0RB_1LD0LB_1RA0LE_---1LF_1LB0LA/explainer.html)
- [`pages/holdouts/1RB1RA_1LC0RB_1LD0LB_1RA0LE_---1LF_1LB0LA/proof-status.html`](../../pages/holdouts/1RB1RA_1LC0RB_1LD0LB_1RA0LE_---1LF_1LB0LA/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RA_1LC0RB_1LD0LB_1RA0LE_---1LF_1LB0LA/lean/check.sh
gcc -O2 -o phase holdouts/1RB1RA_1LC0RB_1LD0LB_1RA0LE_---1LF_1LB0LA/c/phase.c
python3 holdouts/1RB1RA_1LC0RB_1LD0LB_1RA0LE_---1LF_1LB0LA/py/drive.py 200 out.txt       # the reduced phase map
python3 holdouts/1RB1RA_1LC0RB_1LD0LB_1RA0LE_---1LF_1LB0LA/py/check_full.py out.txt 20 ./phase   # the first phases at full size
```
