# odometer: the PR 89 technique (closed-form drains + exact executor) on three counter holdouts

None of the three machines halted in the runs. The executors are exact, step counts included. Evidence levels used
below: **computed** means an exact accelerated run, checked against direct simulation on its first events. The closed forms
rest on Lean theorems where the repo has them, and on simulation over many parameters elsewhere. No halt was found, so no
Coq proof was attempted.

Scripts are in `m1/`, `m2/`, `m3/`. Run logs are in `logs/` (one JSON line per event). The family code that is
reused (`hybrid.py`, `cf.py`, `rle.py`) lives in
`holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---/py/`. It was copied to `/tmp/odo/f05py`, which the scripts import,
so change that path to rerun.

## 1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_0RE--- (base-5 marker counter, F05)

- The repo already has a PR 89-style executor, the F05 `hybrid.py`. Clean visits use the closed form `go_closed`,
  which is a Lean theorem: a depth-k visit is 5^k inner rounds in one operation (the "k-level drain"). Every other
  visit is run by an exact run-length simulation, recursively. The repo had run it to 3.4e200 steps.
- I ran it further without the memo table, which held 4 GB and gave only about 1% hits (`m1/far1.py`).
- **Computed: no halt in 1.6e712 steps.** The run has 1,960 left-end events and 684 F-events, and every F-event reads 0. At
  the end the list has 509 blocks; block i is about 5^i, and the last block has 350 digits. The smallest drift
  |b(i+1) - 5 b(i)| is still 708,572, the same value seen after 1e100. The drift would have to approach 0 for a
  halt.
- Speed: the cost per left-end event grows about like k², so the run slows to roughly 25 digits every 10 minutes at
  k = 500. Profiling shows the time goes to `rle.suffix_list` and `_fold`, which are O(k) per simulated visit. A C
  port, or offsets stored lazily on the list, would be the next speed-up.

## 1RB1LF_1LC0RD_0LD0LC_1RE0LA_0RA0RC_0RE--- (base-5 gadget counter) — now reduced to the F05 executor

- New finding: this table is a mirror image of `1RB0LC_0RC0RB_1LD0RE_0LE0LB_1LA1RF_0LD---` started in state E
  (`m3/conj.py`, an exact table check). That machine is the F05 core with E1 = 1RF and F0 = 0LD. On every tape where
  the cell right of E is 0, E1 → F0 makes the same move as the core's E1 = 0LB, only in 3 steps instead of 1. D1 = 0LB
  equals machine 1's D1 → F0 → E1 detour whenever F reads 0. So **this machine halts exactly at an E1 read that has a
  1 on its right.**
- Clean visits:
  - On 400 clean lists, a direct simulation (`m3/visit3.py`) gives the same tape as the F05 closed form. No E1 read in
    them has a 1 on its right.
  - Each clean visit of depth k reads E1 exactly (5^k-3)/2 times, so it takes `cf.steps + 5^k - 3` steps.
  - This rests on simulation evidence; it is not a Lean theorem.
- Executor `m3/h3.py`: the F05 hybrid with this table and the corrected step count. Unclean visits are simulated
  with this machine's own table, so a halt inside one would be caught.
- Validation:
  - All 25 left-end events up to 7.4e10 steps match a direct C run of the original machine, cell for cell, step and
    head position included (`m3/chk3.c`, `m3/val3.py`).
  - Against direct runs of the frame-A table, the starts A, C and E match 19, 19 and 24 events of 24 or 19
    (`logs/val3_*.txt`).
- **Computed: no halt in 1.4e515 steps** (the repo had 2.4e14). At the end there are 1,512 left-end events and 367
  blocks; the first blocks are 312, 418064, 1405936, …
- The first run, which kept the memo table, was killed by out-of-memory at 1e351. The rerun without memo reached
  1e515.
- Bonus, sibling holdout `1RB0LC_0RC0RB_1LD0RE_0LE0LB_1LA1RF_0LD---`: this is the same table started in A. Its repo
  status says 1e16 steps. **Computed: no halt in 1.6e522 steps** (`logs/m3A.log`).
- The other sibling, `1RB0LC_0RC0RE_1RD1LF_1LE0RA_0LA0LE_0RB---`, is the same table started in C (mirror image). The
  executor passes validation for that start but was not run far: its run is not the same as the A run.

## 1RB1LF_1RC0RA_0RD1RA_1RE1LA_0LA---_1RF0LD (binary counter with paying blocks) — new executor

- Event: the head is in A on a 0 with only blank cells to its left. The tape from the head reads
  `0 a^x b1 a^y1 … bk a^yk`, with a = 10, taking a's greedily.
- Regular decrement:
  - It applies when the lowest set bit is j, x ≥ 1 and y_1..y_j ≥ 1.
  - It sets b_1..b_{j-1} to 1 and b_j to 0, and it changes y_j-1 and x+2.
  - It takes 6(x+y_1+…+y_{j-1})+10 steps, and the head ends 2 cells further left.
  - The repo proves this in Lean for j ≤ 3. I checked it by direct simulation on 6,000 random cases with j ≤ 45
    (`m2/dec_check.py`).
- **Closed-form drain** (`m2/m2exec.py: drain`):
  - It counts the counter value V down to the first exceptional decrement in one operation. That is the first
    multiple of 2^(i-1) after block i has been emptied, or 0.
  - Each y_i is reduced by the number of u in the range with ν2(u) = i-1.
  - The step sum is in closed form, using arithmetic series over the multiples of 2^i.
  - On 3,000 random states it agrees exactly with iterated single decrements (`m2/drain_check.py`).
- Exceptional events, where an empty block is met or all bits are 0, are run by the exact run-length simulator until
  the next event.
- Validation: 169 sampled events up to 1.9e10 steps match a direct C simulation (state, position and the whole tape;
  `logs/val2e10.txt`).
- **Computed: no halt in 1.2e1572 steps** (the repo had 2.7e129). The run has 24,638 full borrows (right-end events)
  and 93,330 exceptional events. At the end there are 2,608 blocks, and the low blocks have about 785 digits.
- Closeness to a halt: a halt needs two neighbouring empty blocks with zero bits around them. I measured the
  smallest neighbour of an empty block met by the borrow, after 1e20 and away from the 4-block tail. It is 49, at
  step 2.1e643 (y = [49, 0, huge, …], bits 0 0 1 1). All other values are much larger; to 1e660 the only values under
  10^4 are the two at 1e643 (`logs/near.txt`). Low blocks are rebuilt small after rewrites, so a near-coincidence like
  this can recur. This is the machine that looks most worth running further.
- Speed: about 85 digits every 10 minutes at the end (k ≈ 2,600). It is cheap to continue.

## What would come next
- m2: keep running, which is cheap. Decode the exceptional rewrite as a map and add it to the drain. That removes the
  run-length simulation and makes a busycoq-style proof of a halt (or a long-run certificate) feasible: the drain is
  pure arithmetic, like PR 89's `towerK`.
- m3: a Lean or Coq lemma that clean visits never read E1 next to a 1, and the (5^k-3)/2 count. The induction is
  the same as `go_spec`.
- m1 and m3: port the hybrid to C/GMP to get past 1e1000.
