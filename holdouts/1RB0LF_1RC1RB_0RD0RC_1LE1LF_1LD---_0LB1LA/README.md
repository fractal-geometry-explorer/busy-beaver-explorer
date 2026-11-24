# 1RB0LF_1RC1RB_0RD0RC_1LE1LF_1LD---_0LB1LA

bbchallenge id 116372. One of the six-state holdouts whose halting from blank tape is open.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LF |
| B | 1RC | 1RB |
| C | 0RD | 0RC |
| D | 1LE | 1LF |
| E | 1LD | --- |
| F | 0LB | 1LA |

## What it does

**Tape**: a short counter on the left, then `1^K 0^Z`. **Sample point**: C on a 0 at the right end (once a sweep).
At step 16,085,367: `11 0^6 111 0^8 1^21 0^7 1^2670 0^1377`.

**One sweep** (all passes are Lean shift rules in `lean/Rules.lean`): leftward, D/E turn the zeros into ones
(`d_run`), A/F turn the ones into `(10)^n` (`a_run`); near the counter the head turns and a zigzag turns `(10)^n`
back into ones, 10 steps a pair (`d_zigzag`); B crosses ones (`b_run`) and C turns the former zeros back into zeros
(`c_run`). 18,762 steps later: `... 1^21 0^6 1^2669 0^1381` (K -1 or -3, Z +4, the counter ticks).

**The trip through the block** (`lean/Passes.lean`, from `py/passes.py`, for every block length): leaving the
counter as `0 0 D>` or `1 0 C> 0`, with `(10)^(k+1) (11)^(2j+2)` and blank tape to the right, the head crosses the
block, turns, and comes back to the counter in `8j + 12k + 32` (or `+ 34`) steps, F or A on the block's first cell,
with 4 more ones; the counter is never read (`pass_d`, `pass_c`). The same trip with an odd number of ones halts at
the far end (`pass_d_halt`, `pass_c_halt`); the count only ever gains 4, so the right end is safe and a halt has to
come from the counter. In a direct run to 4·10^7 steps, 3,351 of the 3,394 returns from the counter have exactly
the shape of `pass_d` or `pass_c`; the other 43 are in the sweeps around a phase change, which `py/phasemap.py`
runs in full.

## The phase map

`py/phasemap.py` runs the machine exactly, phase after phase, with the step count:

- **One sweep.** By the trip above a sweep depends on w and on K mod 4 only. It is run on `w 1^K0 0^Z0` with
  K0 = 32 + K mod 4, Z0 = 32 + Z mod 4 and lifted: w' is the same, K and Z move by the same amounts, and the
  steps are dt0(w) + 6K + 2Z (every one of the 6,552 sweeps with K, Z ≥ 20 of a direct run to 1.5·10^8 steps
  agrees).
- **Many sweeps.** In a phase w is an odometer: each sweep reads only the right end of w, down to the deepest
  carry. The script caches, for each suffix v of w, the run of sweeps until one reads left of v, and builds long
  runs from short ones. Some thousands of sweeps are run for real per phase, however long the phase.
- **Phase change.** When K is used up the sweeps are run one by one with K exact; in the sweep where the zeros
  become the new block, the run on Z0, Z0 + 8 and Z0 + 16 is checked to be linear in Z.
- **Check.** `python3 py/phasemap.py --check`: the starts of phases 1 to 13 (to step 2,411,853,311) agree, tape and
  step, with the same sweeps run on the whole tape without the reduction or the cache.

Phase n starts at the sweep where the zeros become the block: the tape is `w_n 1^(K_n) 0^1`. Phase 1 starts at
step 13 with K = 6; then K = 14, 38, 94, 198, 418, 838, 1678, 3358, 6718, 13446, ...

**Run:** to phase 800 (step 1.6·10^483, K_800 ≈ 2^802), with no halt (`results/phases.tsv`; one line a phase).

**What the run shows** (exact for phases 1 to 800; not proved for later phases):

- `K_(n+1) = 2 K_n + c_n` with c_n = 2, except at the *events* n = 3, 4, 5, 6 (c = 10, 18, 10, 22) and
  11, 94, 122, 218, 490 (c = 10). From phase 11 on, `K_n + 2 = 13448 · 2^(n-11) + 8 · Σ 2^(n-m)` over the events m ≤ n.
- Steps: t_n / K_n^2 → 5/6. Phase n lasts 5 K_n^2 / 2 + O(K_n |w_n|) steps (K drops by 1 and 3 on alternate
  sweeps, so a phase is about K_n / 2 sweeps of about 6K + 2Z steps).
- The counter word grows: 6,482 cells at phase 250, 46,254 at phase 800. Read from the right it ends in a
  list of blocks `1^b 0^3` that change slowly, with a part on the left that changes every phase.
- **Events.** c_(n+1) ≠ 2 exactly when w_n ends in `1^2 0^2`, in every phase so far. The last block `1^b 0^3`
  loses one 1 a phase (230 of the 238 phases 10 to 250; the 8 others are the two phases after each event, when
  blocks merge), so the whole list of blocks slides one cell toward the block each phase. At b = 2 the next phase
  ends `... 0^7`, the next `... 1^2 0^2`, and the one after is an event; then the block before it becomes the
  last, and merges with its neighbours, so the next event is about as many phases away as that block is long.
  Predicted this way from phase 218 (last block 269): an event at phase 490. The run then found it there. After
  it the last blocks merged into one of 2,581 cells (phase 498), so if the blocks keep
  sliding the next event cannot come before about phase 3,080.

A halt needs `1 D> 0` (`halt_shape`), which no sweep through phase 800 produced. Each sweep the cache reuses was
run once for real, so a halt in any of them would have been seen.

## Status

Open.

- **Lean, kernel** (`lean/Rules.lean`, from `py/rules.py`): `d_run`, `a_run`, `d_zigzag`, `b_run`, `c_run`,
  `halt_shape`, `halt_after_shape`. `lean/Passes.lean` (from `py/passes.py`): `pass_d`, `pass_c`, `pass_d_halt`,
  `pass_c_halt`. `lean/Blank.lean`: no halt in 10^7 steps.
- **Trusted**: no halt to phase 800, step 1.6·10^483 (`py/phasemap.py`), checked against full sweeps through phase 13;
  no halt in 10^9 steps (direct); near-miss counts (`c/nbhd.c`).
- **Heuristic**: the event rule and the countdown of the last block.

## Notes for later

- Decode the counter word as numbers: the odometer of a phase (digits written as runs, about base 4, counting
  double sweeps) and the block list across phases (countdown of the last block, merges after an event). A proof
  either way needs the rule for the list, and the condition for `1 D> 0` inside the counter: no zero run of the
  word at a phase start has length 1 mod 4 (lengths seen: 2, 3, 4, 6, 7, 8, 10, 11, 12, 14, 15, 16, 18, 19, 20,
  23, 24), but runs of 1, 5 and 9 zeros occur inside phases.

## Reproduce

```sh
gcc -O2 -o tok holdouts/1RB0LF_1RC1RB_0RD0RC_1LE1LF_1LD---_0LB1LA/c/tok.c && ./tok 1RB0LF_1RC1RB_0RD0RC_1LE1LF_1LD---_0LB1LA 1000000000 C 0 R 0 10000000 0 | awk 'NR%2000==1'
gcc -O2 -o nbhd holdouts/1RB0LF_1RC1RB_0RD0RC_1LE1LF_1LD---_0LB1LA/c/nbhd.c && ./nbhd 1RB0LF_1RC1RB_0RD0RC_1LE1LF_1LD---_0LB1LA 1000000000 D 0
python3 holdouts/1RB0LF_1RC1RB_0RD0RC_1LE1LF_1LD---_0LB1LA/py/rules.py > holdouts/1RB0LF_1RC1RB_0RD0RC_1LE1LF_1LD---_0LB1LA/lean/Rules.lean
python3 holdouts/1RB0LF_1RC1RB_0RD0RC_1LE1LF_1LD---_0LB1LA/py/passes.py > holdouts/1RB0LF_1RC1RB_0RD0RC_1LE1LF_1LD---_0LB1LA/lean/Passes.lean
python3 holdouts/1RB0LF_1RC1RB_0RD0RC_1LE1LF_1LD---_0LB1LA/py/phasemap.py --check          # about a minute
python3 holdouts/1RB0LF_1RC1RB_0RD0RC_1LE1LF_1LD---_0LB1LA/py/phasemap.py 300              # phase 300 in about 2 minutes
python3 holdouts/1RB0LF_1RC1RB_0RD0RC_1LE1LF_1LD---_0LB1LA/py/phasemap.py 800 --log phases.log --ckpt ckpt.json
```

## Pages

- [`pages/holdouts/1RB0LF_1RC1RB_0RD0RC_1LE1LF_1LD---_0LB1LA/explainer.html`](../../pages/holdouts/1RB0LF_1RC1RB_0RD0RC_1LE1LF_1LD---_0LB1LA/explainer.html)
- [`pages/holdouts/1RB0LF_1RC1RB_0RD0RC_1LE1LF_1LD---_0LB1LA/proof-status.html`](../../pages/holdouts/1RB0LF_1RC1RB_0RD0RC_1LE1LF_1LD---_0LB1LA/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LF_1RC1RB_0RD0RC_1LE1LF_1LD---_0LB1LA/lean/check.sh
```
