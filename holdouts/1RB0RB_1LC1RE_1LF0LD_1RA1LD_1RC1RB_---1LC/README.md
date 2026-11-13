# 1RB0RB_1LC1RE_1LF0LD_1RA1LD_1RC1RB_---1LC

bbchallenge id 53489. One of the six-state holdouts whose halting from blank tape is open; analyzed by hand (group G02). The pages are built from [`status.json`](status.json).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RB |
| B | 1LC | 1RE |
| C | 1LF | 0LD |
| D | 1RA | 1LD |
| E | 1RC | 1RB |
| F | --- | 1LC |

Named "Space Needle-like" on the bbchallenge wiki (cryptid, probviously non-halting, mxdys, August 2024).

## What it does

Every time the head is in D on the leftmost visited cell (reading a 1), the tape is N ones with exactly one 0 (the
hole) at position p, e.g. step 1,137,813,213: `D>1 1^24348 0 1` (N = 24,351, p = 24,349). Between samples the
head bounces (square-root side); each sample adds one cell on the left (logarithmic side).

**The hole map** (proved in Lean for all values, `lean/Map.lean`; S(p, r) = `D> 1^p 0 1^r` on blank tape,
N = p + r + 1, p, r >= 1):

| case | next sample | as (N, p) |
|---|---|---|
| p = 1 | **halt** | |
| p = 3, r odd | S(r+5, 2) | N odd: N' = N + 4, p' = N' − 3 |
| p = 3, r even | S(r+5, 1) | N even: N' = N + 3, p' = N' − 2 |
| p = 2k+2 | S(3k+r+4, 1) | N' = N + p/2 + 2, p' = N' − 2 |
| p = 2m+1 >= 5 | S(m−1, m+r+3) | N' = N + 1, p' = (p−3)/2 |

Worked example: (24351, 24349) → (24352, 12173) → (24353, 6085) → (24354, 3041) → (24355, 1519) → (24356, 758)
→ (24737, 24735), as the machine does.

**How each case runs** (rules of `lean/Steps.lean`, proved by `bbtools.symtm` from `py/steps.py`):

- p = 2k+2: the sample builds the block `0 1 D> 1 (11)^k 0` (`initE`); one pass of 4k+7 steps moves it one cell
  right past a 1 (`drift`), r−1 times; at the right end each pass of 12k+25 steps eats one 11 and leaves 111 behind
  (`loop`), k times; then `finalE` makes the next sample.
- p = 2m+1 >= 5: one step (`initO`), then m halving rounds `D> 0 1 (11)^(i+1) 0 R → 1 D> 0 1 (11)^i 0 1 R` (4i+7
  steps; an 11 becomes a 1 on each side of the hole), then `endO`.
- p = 3: single symbolic runs by the parity of r (`p3a0`, `p3as`, `p3b0`, `p3bs`); p = 1 is `halts_family`
  (`lean/Rules.lean`).

`Map.lean` iterates the loop rules by induction (`iterate`), sums the step counts in closed form (`cost p r`), and
proves `sample_step` for all p, r >= 1. Same construction as `holdouts/1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_---1LB`.

## Status

Open, **reduced in Lean**: `halts_iff : HaltsFromBlank ↔ ∃ n, orb n = none`, where `orb` is the orbit of (2, 2)
(the sample reached at step 11) under f and `none` means it reached p = 1. A halving chain p → (p−3)/2 reaches 1
only from 2^j − 3, and chains start at N − 2 (or N − 3 right after p = 3), so the run halts iff an end-of-tape
sample has length N = 2^j − 1 (or close variants after p = 3). N grows by a factor about 3/2 per even step; the map
iterated 30,000 times (1,835 digits) never reaches p = 1 or 3. Heuristic chance of a hit beyond N ≈ 3·10^4:
Σ_{j>=15} 2/(2^j ln 1.5) ≈ 3·10^-4.

- Lean, kernel (no `native_decide`; axioms propext, Classical.choice, Quot.sound):
  - `lean/Map.lean`: `sample_step` (the map with exact step counts, all p, r >= 1), `halts_iff` (the reduction).
  - `lean/Bound.lean`: `no_halt_10_3669`: no halt in the first 10^3669 steps (the kernel follows the proved map for
    30,000 samples, `decide +kernel`, about 30 s).
  - `lean/Rules.lean`: `to_halt`, `halts_family`: `D> 1 0 R` with blank tape to the left halts, for every R.
  - `lean/Blank.lean`: the halting configurations, 10^4 steps from blank (`native_decide`: 10^7).
- Computed: no halt in 10^10 steps (`tools/c/tmrun.c`); `py/holemap.py check`; `bbtools.ctl` K = 2..7 allows a
  halt (as it must); n-gram CPS fails.
- No cycle or safe region: the orbit grows without bound and nothing found constrains N modulo powers of 2, so
  the reduction does not decide the machine.

## Notes for later

- The remaining question is purely arithmetic. Pushing the orbit further is cheap (`python3 py/holemap.py run K`; in
  Lean, `check K B` in `lean/Bound.lean`).

## Pages

- [`pages/holdouts/1RB0RB_1LC1RE_1LF0LD_1RA1LD_1RC1RB_---1LC/explainer.html`](../../pages/holdouts/1RB0RB_1LC1RE_1LF0LD_1RA1LD_1RC1RB_---1LC/explainer.html)
- [`pages/holdouts/1RB0RB_1LC1RE_1LF0LD_1RA1LD_1RC1RB_---1LC/proof-status.html`](../../pages/holdouts/1RB0RB_1LC1RE_1LF0LD_1RA1LD_1RC1RB_---1LC/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RB_1LC1RE_1LF0LD_1RA1LD_1RC1RB_---1LC/lean/check.sh
```
