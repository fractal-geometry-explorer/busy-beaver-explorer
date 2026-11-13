# 1RB0LD_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF

bbchallenge id 141594, a six-state holdout of group G05 (growth class fixed/sqrt). **Open**, and reduced in Lean
(kernel) to one question: does a sweep ever carry a power of two to the left end of the tape?

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LD |
| B | 1LC | 1RD |
| C | 0LE | 1LA |
| D | 0RB | 1RD |
| E | --- | 0LF |
| F | 1RA | 1LF |

## What it does

**The tape.** At every turn the tape is a row of blocks of 1s, each followed by a single 0, except at one place,
the *gap*, where two 0s stand side by side; the head (state B) is on the second 0 of the gap. Write a gap
configuration `(b, ls, rs)`: `b` the block left of the gap, `ls` the blocks further left, `rs` the blocks right of
the gap (both nearest first; the first of `rs` may be empty). Beyond the leftmost block the tape is blank.

**A round** (`round_gap`, 2b + 5 steps): E erases the last 1 of `b`, F runs left over it and writes a 1 into the 0
in front of it, A and D come back to the gap, now one cell further left:

    (a, b, c)  ->  (a + 1, b - 2, c + 1)          for b >= 3  (b = 2: 8 steps, round2)

**A block.** Rounds repeat (`rounds_gap`, m rounds in m(2c + 2m + 7) steps, c the final size):
- even block 2m: it is used up, each neighbour gets m, and the gap moves on to the next block left (`even_gap`);
- odd block 2m + 1: after m rounds one 1 is left; the gap closes (`1 0 0` becomes `1 1 1`, so the right
  neighbour gets 3 more), D runs right across the tape (`drun`) and opens a new gap at the right end (`odd_gap`).

**A sweep** starts at the right end (right neighbour: the blank tape, an empty block) and goes left through even
blocks until the first odd one. Example (step 417): `3 8 6 4 |` -> `3 8 8 | 0 2` -> `3 12 | 0 4 2` -> `| 9 0 6 4 2`
(left end) -> `4 7 6 4 2 |`. Every sweep adds two 1s and keeps the number of blocks, except at the left end.

**The emergent behaviour: a carry chain.** A sweep gets far only when the blocks it meets are even, like a carry
through a binary counter. Near the right end the blocks are small and the sweep depths are periodic
(`3 1 2 5 3 1 2 6 ...`); further left the blocks are huge and their parities look irregular. Sweeps that get through
every block and reach the left end are rare: in the first 10^11 sweeps, 17 of them (at sweeps 0, 1, 5, 9, 21, 25, 37,
169, 1353, 2377, 10569, 107081, 893513, 15946569, 478635753, 9245583081, 13142925897), each 1.4 to 30 times as many
sweeps after the one before.

**Where it can halt.** E reads a 0 only (a) at a gap on an empty block (excluded by the invariant) or (b) when an odd
block closes its gap with nothing to its left: D steps into the blank and B, C, E read three blank cells. At the left
end an even block 2m gives m to a new leftmost block and the gap moves onto it, again with nothing to its left, so a
block 2^k·q (q odd) halves k times; then q >= 3 closes safely and q = 1 halts. **The machine halts iff some sweep
reaches the left end carrying a power of two.** The 17 carried values were 3, 3, 7, 9, 25, 23, 26 = 2·13,
106 = 2·53, 1292 = 4·323, 649, 7148 = 4·1787, 94000 = 16·5875, 281084 = 4·70271, 6578056 = 8·822257,
283561618 = 2·141780809, 7939115926 = 2·3969557963, 10931368378 = 2·5465684189: none a power of two.

## Status and evidence

**Lean, kernel only** (`lean/Macro.lean`): the cell rules `round`, `round2`, `dissolve`, `dblock` (written by
`bbtools.symtm.prove` or by `rfl`); the block rules `round_gap`, `rounds_gap`, `even_gap`, `odd_gap`, `drun`,
`sweep_start`; the halts `halt0` (`gap 0 ls rs`) and `halt1` (`gap 1 [] rs`); the block machine `mstep` with cost
`mcost`, `mstep_sound` (the machine follows it, step count exact) and `mstep_halt`.

**Lean, kernel only** (`lean/Reduce.lean`): `init_gap` (blank tape reaches `gap 3 [] []` in 7 steps); the invariant
`Inv` (every block nonempty except the first right of the gap) is kept (`inv_next`), so the rules cover the whole
run (`mrun_ne_stuck`); **`halts_iff`: `HaltsFromBlank ↔ ∃ n, mrun n m0 = .halt`**; `mstep_halt_iff` (under `Inv`,
halt exactly at `b = 1 ∧ ls = []`); `wall_halve`, `wall_chain`, `wall_odd` (the power-of-two reading).

**Lean, `native_decide`** (`lean/MacroRun.lean`): `macro_runs`, `blank_runs_macro`: 20,000,000 macro steps
(9,122,017 sweeps), no halt, so no halt in the first 221,196,908,934,683 steps; `runN_sound` (kernel) says the
compiled runner computes a run of the machine. Also `blank_runs_native` (10^7 steps directly, `lean/Blank.lean`).
`lean/Axioms.lean` prints the axioms.

**Computed (trusted)**: `py/macro.py check 1e8` compares the whole tape and the step count at each of the 16,429 gap
configurations of the first 10^8 steps with the block machine: all agree. `c/sweeps.c` (one sweep at a time, 128-bit
step counts; agrees with `py/macro.py` on step counts): no halt in the first 10^11 sweeps, 19,546,906,269,883,249,177,370 steps (1.95·10^22), with
the left-end visits listed above.

**Heuristic**: if the carried value v behaves like a random number of its size, a visit is fatal with chance about
log2(v)/v; with v >= 10^10 and the visits ever rarer, the chance of a halt after the computed range is about 4·10^-9.

**Open**: whether a power of two ever reaches the left end. The carried value is fixed by the parities of all the
blocks, a Collatz-like dependence; no invariant excluding powers of two is visible (the values have no fixed residue
mod 3, 5 or 7).

## Reproduce

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LD_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF/lean/check.sh   # about 1 minute
python3 holdouts/1RB0LD_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF/py/macro.py check 1e8     # block machine vs machine
python3 holdouts/1RB0LD_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF/py/macro.py walls 1e6     # left-end visits
python3 holdouts/1RB0LD_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF/py/macro.py run 20000000  # the number in MacroRun.lean
gcc -O2 -o sweeps holdouts/1RB0LD_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF/c/sweeps.c && ./sweeps 100000000000   # ~25 min
```

## Layout

| path | what it is |
|---|---|
| `lean/Machine.lean`, `lean/Blank.lean` | the machine and bounded runs (generated) |
| `lean/Macro.lean` | blocks, the gap, the rules, the block machine `mstep` and its soundness |
| `lean/Reduce.lean` | the invariant, `halts_iff`, the power-of-two characterization |
| `lean/MacroRun.lean` | the block machine run 2·10^7 macro steps with `native_decide` |
| `lean/Axioms.lean` | the axioms of the main theorems |
| `py/macro.py` | the block machine in Python, checked against the machine; left-end visits |
| `c/sweeps.c` | the block machine in C, one sweep at a time, for 10^11 sweeps |

## Pages

- [`pages/holdouts/1RB0LD_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF/explainer.html`](../../pages/holdouts/1RB0LD_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF/explainer.html)
- [`pages/holdouts/1RB0LD_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF/proof-status.html`](../../pages/holdouts/1RB0LD_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF/proof-status.html)

## For later

A proof of non-halting needs a reason why the value a sweep carries to the left end is never a power of two. The
next step would be to study the sweeps that reach the left end as a map of their own: the blocks just after such a
visit are `x, x+3, 2x+1, 4x+2, ...` (the halvings), and the next visit depends on how the parities of the large blocks
evolve under repeated half-splits; a formula or a 2-adic invariant for that map would settle the machine.
