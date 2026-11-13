# 1RB0LE_1RC0RF_0RD0RB_1RE0RC_1LA0LA_1RA---

bbchallenge id 70977, a six-state holdout of group G05 (growth class fixed/sqrt). **Open.** The fill sweeps are
proved in Lean (kernel). A jumping simulator, checked against direct simulation, runs 28 cycles (1.06·10^17 steps)
without a halt.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LE |
| B | 1RC | 0RF |
| C | 0RD | 0RB |
| D | 1RE | 0RC |
| E | 1LA | 0LA |
| F | 1RA | --- |

## What it does

**Cycles.** Sample the run at the E-records: state E on a new rightmost cell, reading 0. Cycle n starts at

    P 1^3 0^K 1 E>0

where P is a short prefix and K is the gap: K = 9, 15, 27, 51, 99, 197, 389, 773, 1539, 3069, ..., 798641935
(cycle 28), roughly 3·2^n.

**Fill sweeps** (`lean/Macro.lean`). Inside a cycle the E-records are `L 0^z 1 0 1 1 1 0 (10)^m 1 E>0`, and

    L 0^(z+4) 1 0 1 1 1 0 (10)^m 1 E>0  ->  L 0^z 1 0 1 1 1 0 (10)^(m+4) 1 E>0        4m + 40 steps   (fill)

L is never read. k sweeps take k(4m + 40) + 8k(k − 1) steps (`fills`). So a gap costs about K²/2 steps, and each
cycle is about 4 times longer than the last.

**Passes.** When fewer than 4 zeros are left:
- one pass runs to the left end of the tape and one runs back, about 12·K steps in all;
- they rewrite P and turn `(10)^m` into the next gap, K' = 2K − c. Here c is small (3, 3, 3, 1, 5, 5, 7, 9, 11, 13, ...)
  at first and grows with the prefix later (12127 at cycle 28).

Example, cycle 8 → 9:

    1^2 0^3 1^3 0^5 1^3 0 1^3 0^3 1^3 0 1^3 0 1^3 0 1^3 0^5 1^3 0^11 | 1^3 0^773
    1^2 0^3 1^3 0^3 1^3 0^5 1^3 0 1^3 0 1 0 1^5 0 1^3 0^5 1^3 0^5 1^3 0^15 | 1^3 0^1539

**The prefix.** It alternates between two head forms (`1^2 0^3 1^3 0^3 1^3 0^5 1^3 0 1^3 0 1 0 1^5 ...` and
`1^2 0^3 1^3 0^5 1^3 0 1^3 0^3 1^3 0 1^3 0 1^3 0 1^3 ...`), and its tail holds gaps that grow from cycle to cycle.
The last four zero-runs at each cycle:

| cycle | K | last zero-runs of P | P length |
|---|---|---|---|
| 13 | 24461 | 1, 5, 5, 89 | 147 |
| 16 | 195273 | 1, 5, 1, 295 | 377 |
| 20 | 3121037 | 11, 1, 43, 1523 | 1645 |
| 24 | 49920115 | 7, 55, 215, 7383 | 7727 |
| 28 | 798641935 | 5, 313, 711, 36103 | 37199 |

The largest grows by about 1.48 per cycle, the next ones by 1.36 to 1.5. New gaps appear and older ones merge
(e.g. `0^27 1^3 0^5 1^3 0^33` at cycle 12 becomes `0^89` at cycle 13). Overall it is a hierarchy of counters at
different rates, much like a nested bouncer.

**Where it could halt.** F is entered only by B reading 1, and F1 is the halting transition, so it halts exactly on
`B>1 1`. The fill sweeps never get there: `fill` proves the sweep completes. A halt would have to come during the
passes over the prefix.

## Status and evidence

**Lean, kernel only**:
- `fill_raw` (`lean/Gadgets.lean`, by `py/gen_gadgets.py` with `bbtools.symtm.prove`);
- `fill`, `fills`, `fcost`, `fcost_23` (`lean/Macro.lean`);
- `fsteps3224` and `reach3224`: blank tape reaches `fcfg 95 2 P5` in 3,224 steps;
- `reach_fill_end`: 23 sweeps later, `fcfg 3 94 P5`.

**Lean, native_decide**: `blank_runs_native`, no halt in 10^7 steps (`lean/Blank.lean`).

**Computed (trusted)**:
- `c/cyc17.c` simulates directly. At each fill record with at least 12 zeros left, it rewrites all sweeps but the last
  two in one go and adds k(4m + 40) + 8k(k − 1) steps.
- With `nojump` it is a plain simulator. Through cycle 12 (25,164,855 steps) the cycle starts agree exactly: step,
  K and the whole prefix.
- `./cyc17 1500000000 60`: 28 cycles with no halt, 106,309,693,328,363,073 steps. The last cycle has
  K = 798,641,935, and 9.99·10^9 steps were simulated directly. It then ran out of its tape array.

**Heuristic**: the growth rates above. **Open**: the prefix dynamics, and so the question.

## Reproduce

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LE_1RC0RF_0RD0RB_1RE0RC_1LA0LA_1RA---/lean/check.sh
python3 holdouts/1RB0LE_1RC0RF_0RD0RB_1RE0RC_1LA0LA_1RA---/py/gen_gadgets.py
gcc -O2 -o cyc17 holdouts/1RB0LE_1RC0RF_0RD0RB_1RE0RC_1LA0LA_1RA---/c/cyc17.c
./cyc17 2000000 12 nojump; ./cyc17 2000000 12     # same C lines
./cyc17 1500000000 60                            # 28 cycles, ~2 min, 1.5 GB
```

## Layout

| path | what it is |
|---|---|
| `lean/Machine.lean`, `lean/Blank.lean` | the machine and bounded runs (generated) |
| `lean/Gadgets.lean` | the fill sweep as the symbolic run writes it (generated) |
| `lean/Macro.lean` | `fcfg`, `fill`, `fills`, the reach from blank tape |
| `py/gen_gadgets.py` | writes `lean/Gadgets.lean` |
| `c/cyc17.c` | simulator with the fill jump; prints every cycle start |

## For later

- **The passes as a map.** Prove the two passes over the prefix with `symtm.prove`, for prefixes given as words over
  `1^3 0^a`, `1 0`, `1^5`. That gives an exact cycle map `(P, K) -> (P', 2K − c)` and a cycle-level simulator
  needing only O(|P|) work per cycle.
- **Then the prefix.** Study it as a map of its own. Its gaps look like a nested bouncer: each gap fills at its own
  rate. A non-halting proof would need a description of the reachable prefixes that keeps `B>1 1` away.
