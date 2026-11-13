# 1RB0LE_0RC0RA_1LD0LC_1LA0LB_1RA1LF_---0LC

One of the six-state holdouts whose halting from blank tape is open (group G05, growth class fixed/sqrt).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LE |
| B | 0RC | 0RA |
| C | 1LD | 0LC |
| D | 1LA | 0LB |
| E | 1RA | 1LF |
| F | --- | 0LC |

## Status

**Open.** The machine is a binary counter written in six-cell units, incremented once every three sweeps. When the
counter is full, the carry runs into the part of the tape left of it. That part is rewritten, and the counting starts
again with the same counter. Every so often the carry reaches the far left end. Then the old counter is frozen into
the left part, and the wall becomes a new, much longer counter. The left part does not settle into a pattern, so the
question does not close.

- Lean, kernel: every increment (`lean/Rules.lean`, `lean/Counter.lean`). A full count of a counter of any length,
  from any value (`up`, `lean/Count.lean`). Every left-end event on the way from blank tape up to the second level,
  for all counter and wall lengths (`fe`, `s1`, `fo`, `lean/Left.lean`).
- Lean, kernel on top of one `native_decide` (the first 59,129 steps): blank tape gets through the first carry into
  the left end (`reach_S1`). The new counter then has 2·8^(p0+1) values, so there is **no halt in the first
  8^(p0+1) steps** (`no_halt_early`, `lean/Frontier.lean`). Here p0 = 321,163,084,821,590,067,792,163, so this bound
  has about 2.9·10²³ decimal digits.
- Trusted computation (C++ and Python, `py/accel/`): the next three left-end events (S2, S3, S4) also do not halt. Further on, the
  question becomes iterating a chaotic map on a few hundred cells, with each level taking far longer than the one
  before.

## What the tape is made of

At its right end the tape is a periodic **wall** `…010111 010111` that grows by two cells per sweep. Left of the
wall, read the tape in **units** of six cells, starting from the wall and going left. The units alternate between
two kinds: an `X` unit (one bit) and a `Y` unit (two bits).

| unit | cells | | unit | cells |
|---|---|---|---|---|
| X0 | `111110` | | Y0 | `111011` |
| X1 | `111011` | | Y1 | `111010` |
| | | | Y2 | `111111` |
| | | | Y3 | `111110` |

The units nearest the wall are `X Y X Y …`, holding bits 0, 1–2, 3, 4–5, …. Together they make a binary counter.
Once per three sweeps, the head is at the right end in state B and the tape is (phase R):

    L  [unit ds_m] … [unit ds_1] [unit ds_0]  111110  10111 (010111)^n  B>0          R ds n L

Here `ds_0` is an X unit and `L` is whatever lies further left. In blocks of ones, the units are the odd blocks of
the record files. `X0 Y3` side by side is `1^5 0 1^5 0`, which is the long run of blocks `1^5` seen in the
simulation: it is just a stretch of high counter bits that read `0 11`. `X1 Y3` is `1^3 0 1^7 0`.

## One increment: three sweeps

From phase R, the three sweeps are:

1. A deep sweep. The head walks left over the wall (8 steps per unit), then over every unit holding its maximum
   (`X1`, `Y3`), and turns at the first unit that is not at its maximum.
2. A sweep that turns at the unit next to the wall.
3. Another sweep that turns at the unit next to the wall.

After the three sweeps the counter has gone up by one and the wall has gained a unit (`sweep_PQ`, `sweep_QR`, and the
cycle rules `cyc_*`). In order: `X0 → X1`. Otherwise a carry turns `X1 → X0` and `Y3 → Y0` and stops at the next
unit: a `Y` below 3 goes up by one, or an `X0` becomes `X1`. With `j` pairs `Y3 X1` passed, the number of steps is:

| stop | steps |
|---|---|
| bit 0 (`X0 → X1`) | 48n + 122 |
| `Y0 → Y1`, `Y2 → Y3` | 60j + 48n + 154 |
| `Y1 → Y2` | 60j + 48n + 162 |
| `X0 → X1` above bit 0 | 60j + 48n + 182 |

Here `n` is the length of the wall, which goes up by one per increment. So the k-th increment costs about 48k steps,
and the run is quadratic. In the simulation the head's deepest turning points form a ruler sequence: the depth is
set by the number of trailing ones of the count. This model was first checked against the direct simulation on
every increment from step 59,129 to step 9.3·10⁶ (950 increments, exact in steps and digits). Lean now proves it.

## The run from blank tape

The first 145 sweeps are irregular: a small counter grows at the left end. At sweep 139, a single sweep reaches the
left end and rewrites the wall of 45 units into 45 blocks `1^5`. From sweep 145 on, the tape is:

    1 0 1^11 0 1^3 0 1 0 1^3 0 1 0 1 0 1^5 0  |  X1 Y3 X1 Y3 (X0 Y3)^21 X1 Y0 X1  |  111110  wall

The 34 cells on the left are the irregular part `L0`. The 49 units after them are a counter of 73 bits. At step
59,129 the digits, nearest the wall first, are `ds0 = [1, 0, 1, 3, 0, 3, …, 0, 3, 1, 3, 1]` and the wall has 2 units.
The last 6 cells of `L0` read as one more unit, `Y3`. So the counter has 50 units (`ds0' = ds0 ++ [3]`, `R0_eq`) and
the true left part `L_0` has 28 cells.

## Carries into the left part

With the counter all ones (`top`), the next three sweeps carry out of its top unit into the left part `L`. In every
case met so far, the result is again phase R. The counter is all zeros (`bot`), the wall has gained a unit, and `L`
has become `F(L)`. `F` depends on `L` and on the parity of the counter length only, not on the wall length or the
counter length itself. After that, the counter counts again from zero: `capP − 1` increments, where `capP` is the
number of values of the counter (`up`).

Rarely, the carry does not stop near the counter. It runs to the left end of the tape. This is an **S event**, and it
takes 5 sweeps instead of 3. It rewrites the whole tape:

- the old counter becomes a run of blocks `B = 1^9 0 1 0`, one block per two units;
- the wall becomes the new counter;
- the new wall is empty.

### Level 0, from blank tape (Lean, kernel)

- `fe 0` … `fe 16`: 17 carries `L_0 → L_1 → … → L_17`, each with a 50-unit counter (even length) and any wall. Each
  is followed by a full count of 2·8^24 values.
- `s1`: the carry into `L_17` is an S event. At that moment the wall has 2·p0 + 2 units, with
  p0 = 321,163,084,821,590,067,792,163, around step 10⁴⁹. The result is:
  - the left part `L1 = P B^24 Q`, with `P` 28 cells and `Q = 1^5 0 1 0 1 0`;
  - the counter `ds1 p0 = 1, 3, 0, 3, 0, …, 3, 0` of 2·p0 + 3 units, which is odd;
  - an empty wall.

`fe` and `s1` are proved for every counter length 2j + 2 and every wall, so they are rules, not one-off runs
(`lean/LeftRules.lean`, generated by `py/gen_left.py` with `bbtools.symtm`).

### Level 1 (Lean for the first six events, then trusted)

The counter now has 2·8^(p0+1) values, so the run between two carries into `L1` takes more than 8^(p0+1) steps.

- The first six carries into `L1` only rewrite `Q` (`fo 0` … `fo 5`, `Q_0 → … → Q_6`, for every odd counter length,
  every wall and every tape left of `Q`).
- The seventh is the first one that crosses the blocks into `P`.

How the carries work from there on:

- The blocks are transparent. The carry crosses them leftward in state C (a block reads `100000010111` when the head
  reaches its first cell) and comes back in state A, restoring them.
- So a carry either stops in `Q` and the cells it has grown (call them `R`), or it makes a **jump**: it crosses the
  blocks and changes `P`. The change to `P` depends only on `P`. Call this map `J`.
- `R` slowly eats blocks.
- An S event happens when a jump comes back out of `P` in state B instead of A.

The trusted simulator `py/accel/acc.cpp` iterates the carry map with a memo over windows of the tape. It finds that
`L1` takes 2,266,846,918 carries before S2. Each carry is followed by a full count of 2·8^(p0+1) values. S2 gives:

- `P2` (406 cells), then `B^(p0+1)` (the old counter), then `Q`;
- a new counter from the old wall.

### Level 2 and beyond (trusted, under the jump model)

The `J` model was checked against the direct run: for `P2 B^300 Q`, the `P` regions after jumps 1 to 11 agree
exactly. The result of the S event was also checked: the next `P` is the same for 20, 30 and 40 blocks and for two
different `R`.

| level | P before | jumps until S | P after S |
|---|---|---|---|
| 1 | `P` (28 cells) | (2,266,846,918 carries in all) | `P2`, 406 cells |
| 2 | `P2`, 406 cells | 170,793,835 | `P3`, 460 cells |
| 3 | `P3`, 460 cells | 2,048,289,505 | `P4`, 500 cells |

No halt occurs at S2, S3 or S4, and none in the jumps of levels 2 and 3. Level 3 took about 50 minutes with the memo
capped at 1.5 GB (3.1·10⁸ simulated jumps, 4.3·10¹¹ simulated steps).

## Where it could halt

The only missing transition is F reading 0. F is entered only from E reading 1 (`1LF`), so **the machine halts
exactly when E reads a 1 whose left neighbour is a 0**. In all proved rules, F lands on a 1. The arrival at the left
end in an S event decides it: E there with a 0 on its left halts. This does happen for nearby configurations. In ten
synthetic tests (`P B^k Q`, with `P` from `L1`, k = 0, 1, 2, 3, 5, and counters of both parities), one halts: with
k = 2 and an even counter, the machine halts after 1,129 carries. Such a configuration does not occur from blank
tape (from S1 on, the counters have odd length), but it shows that halting at the left end is possible.

## Why it does not close

- Each level has a new, irregular `P` (28, 406, 460, 500 cells).
- `J` acts on it like a pseudo-random map.
- The number of jumps until the next S is large and irregular (about 2.3·10⁹ carries at level 1, 1.7·10⁸ jumps at
  level 2, 2.0·10⁹ at level 3).

Each S event is a fresh trial for halting, so there is no parametrized family of configurations to prove invariant.
The times between S events grow like a tower: level k+1 starts with a counter of about 8^(previous wall) values.

If each S event halts with some fixed small probability, the machine "probviously" halts, but only at a time beyond
any feasible computation. The levels themselves can be computed by iterating `J` on a few hundred cells, without the
counter, which costs about the number of jumps.

## What is proved

| file | content | level |
|---|---|---|
| `lean/Rules.lean` | `sweep_PQ`, `sweep_QR`, the five three-sweep cycles `cyc_*`, for every carry length and wall length (`py/gen_rules.py`) | kernel |
| `lean/Counter.lean` | the encoding `enc`, phase R `R ds n L`, `next`, `next_sound`, `run_sound` | kernel |
| `lean/Counter.lean` | `reach_s0` (59,129 steps from blank tape), `no_halt_240000021742916313` | native |
| `lean/Count.lean` | `up`: from any valid digit list of `m` units, the counter counts to all ones (`top`) in at least `capP − 1 − val` steps, for every `m`, wall and `L`; `top_even`, `top_odd`, `bot_even`, `bot_odd` | kernel |
| `lean/LeftParts.lean`, `lean/LeftRules.lean` | the left parts `L_0..L_17`, `P`, `B`, `Q_0..Q_6` and the runs `fe_run_*`, `s1_run`, `fo_run_*` (`py/gen_left.py`, `py/left_parts.json`) | kernel |
| `lean/Left.lean` | `fe` (k < 17), `s1`, `fo` (k < 6) as moves between phase-R configurations, for all counter and wall lengths | kernel |
| `lean/Frontier.lean` | `reach_L17`, `reach_S1`, `reach_jump` (blank tape to just before the seventh carry into `L1`), `no_halt_early : ∀ t ≤ 8^(p0+1), ∃ c, steps t init = some c` | kernel, on top of native `reach_s0` |
| `py/accel/` | S2 after 2,266,846,918 carries into `L1`; S3 after 170,793,835 jumps; S4 after 2,048,289,505 jumps | trusted |
| | the jump model and its independence of the blocks and `R` | trusted, checked on samples |

`no_halt_early` uses one `native_decide` (in `reach_s0`) and otherwise only the kernel.

## Reproduce

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LE_0RC0RA_1LD0LC_1LA0LB_1RA1LF_---0LC/lean/check.sh
python3 holdouts/1RB0LE_0RC0RA_1LD0LC_1LA0LB_1RA1LF_---0LC/py/gen_rules.py   # lean/Rules.lean
python3 holdouts/1RB0LE_0RC0RA_1LD0LC_1LA0LB_1RA1LF_---0LC/py/gen_left.py    # lean/LeftParts.lean, LeftRules.lean
cd holdouts/1RB0LE_0RC0RA_1LD0LC_1LA0LB_1RA1LF_---0LC/py/accel && g++ -O2 -o acc acc.cpp
ODD=1 ./acc 8 < Lp24.txt      # level 1: S2 after 2266846918 events, about 30 s
JUMP=1 ./acc 8 < P2.txt       # level 2: S3 after 170793835 jumps, a few minutes
MEMCAP=1500000000 python3 chain.py P3.txt 3   # level 3 (about 50 min, S4 -> P4.txt), then level 4 onwards
```

`Counter.lean` takes about 1.5 minutes (the 10⁸-increment `native_decide`), and `LeftRules.lean` about 1 minute.

## For later

1. Level 4: iterate `J` on `P4` (`py/accel/P4.txt`, 500 cells) until S5. Not run. Level 3 took 2·10⁹ jumps, which
   is about 50 minutes, so level 4 is feasible if its count is similar. Each later level is a new trial for halting.
2. Lean: S2 is out of reach as a direct proof (2.3·10⁹ carries), but the jump rules (blocks transparent in both
   directions) could be proved for every number of blocks. With them, S2 and S3 would follow from finite checks on
   `P` alone, using the compiled checker, as `reach_s0` does.
3. A non-halting proof would need a reason why the arrival state at the left end is never E over a 1 next to a 0. No
   such reason is visible: the `P` regions look random.
