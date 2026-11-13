# 1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_---1LB

bbchallenge id 86694. One of the six-state holdouts whose halting from blank tape is open; analyzed by hand (group G02). The pages are built from [`status.json`](status.json).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RB |
| B | 1LB | 0LC |
| C | 1RD | 1LC |
| D | 1RE | 0RA |
| E | 0RF | 1RA |
| F | --- | 1LB |

## What it does

Almost every visited cell is a 1. Sample the run each time the head is in C on the leftmost visited cell reading a
1: the tape is then N ones with exactly one 0 (the hole) at position p (0-based), e.g. at step 800,549,613
`C>1 1^18646 0 1` (N = 18,649, p = 18,647). Between samples the head bounces across the tape (square-root side);
each sample adds one cell on the left and samples get rarer as N grows (logarithmic side).

**The hole map** (proved in Lean for all values, `lean/Map.lean`; in terms of S(p, r) = `C> 1^p 0 1^r` on blank
tape, N = p + r + 1, with p, r >= 1):

| case | next sample | as (N, p) |
|---|---|---|
| p = 1 | S(r+4, 1) | N' = N + 4, p' = N' − 2 |
| p = 2, r = 3m+1 | S(3m+6, 1) | N ≡ 1: N' = N + 4, p' = N' − 2 |
| p = 2, r = 3m+2 | S(3m+5, 2) | N ≡ 2: N' = N + 3, p' = N' − 3 |
| p = 2, r = 3m+3 | **halt** | 3 \| N |
| p = 3k+3 | S(4k+r+6, 1) | N' = N + p/3 + 3, p' = N' − 2 |
| p = 3k+4 | S(4k+r+8, 1) | N' = N + (p−1)/3 + 4, p' = N' − 2 |
| p = 3k+5 | S(k+1, 2k+r+5) | N' = N + 1, p' = (p−2)/3 |

Worked example: (18649, 18647) → (18650, 6215) → (18651, 2071) → (19345, 19343), as the machine does.

**How each case runs** (the rules of `lean/Steps.lean`, proved by `bbtools.symtm` from `py/steps.py`):

- p = 3k+3: the sample builds the block `0 C> 1 (111)^k 0` (`init0`); one pass of 8k+5 steps moves it one cell right
  past a 1 (`drift0`), r+1 times; at the right end each pass of 32k+34 steps eats one 111 and leaves 1111 behind
  (`loop0`), k times; then `final0` makes the next sample.
- p = 3k+4: the same with the block `0 1 1 C> 1 (111)^k 1 0` (`init1`, `drift1`); at the right end `end1z` (k = 0)
  or `end1s` (turns it into the p = 3k+3 block with k−1).
- p = 3k+5: `initD`, then k division rounds `C> 0 1 1 (111)^(m+1) 0 R → 1 C> 0 1 1 (111)^m 0 1 1 R` (8m+13
  steps; one 111 becomes a 1 left of the hole and two 1s right of the next 0), then `endD`.
- p = 1, p = 2: single symbolic runs (`p1`, `p2a`, `p2b`; the halt is `halts_family` in `lean/Rules.lean`).

`Map.lean` iterates the loop rules by induction (`iterate`), sums the step counts in closed form (`cost p r`,
e.g. 8k+11 + (8k+5)(r+1) + 16k(k−1)+34k + 4k+r+17 for p = 3k+3), and proves `sample_step` for all p, r >= 1.

## Status

Open, **reduced in Lean**: `halts_iff : HaltsFromBlank ↔ ∃ n, orb n = none`, where `orb` is the orbit of (3, 1)
(the sample reached at step 11) under the map f above and `none` means it reached the halting case p = 2, 3 | r.
A division chain p → (p−2)/3 → ... ends at 2 only if it starts at 3^k − 1, i.e. at a tape length N = 3^k + 1 (then
the length at p = 2 is N + k − 1, divisible by 3 iff 3 | k). The lengths at end-of-tape samples grow by about 4/3
per step; the map iterated 30,000 times (to 1,874 digits) never reaches p = 2. Heuristically the chance of ever
hitting 3^k + 1 from here is about Σ_{k>=11} 3/(3^k ln(4/3)) ≈ 10^-4: probably non-halting.

- Lean, kernel (no `native_decide`; axioms propext, Classical.choice, Quot.sound):
  - `lean/Map.lean`: `sample_step` (the map with exact step counts, all p, r >= 1), `halts_iff` (the reduction).
  - `lean/Bound.lean`: `no_halt_10_3747`: no halt in the first 10^3747 steps (the kernel follows the proved map for
    30,000 samples, `decide +kernel`, about 25 s).
  - `lean/Rules.lean`: `to_halt`, `halts_family`: from `C> 1 1 0 1^(3m+3)` (blank around) the machine halts.
  - `lean/Blank.lean`: the halting configurations, 10^4 steps from blank (`native_decide`: 10^7).
- Computed: no halt in 10^10 steps (`tools/c/tmrun.c`); `py/holemap.py check` (the map against the machine);
  `bbtools.ctl` K = 2..7 allows a halt (as it must; the halting family is real); n-gram CPS fails.
- No cycle or safe region: the orbit grows without bound and nothing found constrains N mod 3^k, so the reduction
  does not decide the machine.

## Notes for later

- The remaining question is purely arithmetic (does the orbit of (3, 1) under f reach p = 2 with 3 | r?). Pushing
  the orbit further is cheap (`python3 py/holemap.py run K`; in Lean, `check K B` in `lean/Bound.lean`).

## Pages

- [`pages/holdouts/1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_---1LB/explainer.html`](../../pages/holdouts/1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_---1LB/explainer.html)
- [`pages/holdouts/1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_---1LB/proof-status.html`](../../pages/holdouts/1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_---1LB/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_---1LB/lean/check.sh
```
