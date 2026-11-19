# 1RB0RE_1LC0RA_1RE1LD_0LB0LF_1RA1RA_0LD---

bbchallenge id 123390, group G12. Whether it halts from blank tape is **open**. Family: two-level counter (a fast
binary counter at the right end, one walker step per round in a list of 6-cell digits, rebuilds).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RE |
| B | 1LC | 0RA |
| C | 1RE | 1LD |
| D | 0LB | 0LF |
| E | 1RA | 1RA |
| F | 0LD | --- |

## What it does

**Rounds.** A round ends each time the head, in state A, stands on the first blank cell right of everything written
(`tmrun MACHINE STEPS at A R`). The tape then reads

    1 1 1 0 0   u_1 u_2 ... u_k   X   (1 0)^N 1

a *leader*, a list of six-cell *units* `1 x y 1 0 0`, a stretch X that stays fixed for a whole epoch, and a *tail* of
N single 1s. Write each unit as a digit by its middle bits xy:

    1 00 100 = 1      1 01 100 = 0      1 10 100 = 2      1 11 100 = 3

The tail is the low end of a binary counter: a round is that counter running to its top (about 2^N steps, the head
going back and forth over the tail and into the list), and the tail is one 1 longer at the end of it.

**The walker law.** Inside an *epoch* each round makes one local change in the digits, at a walker that moves left,
and its length T' is twice the length T of the round before plus a constant c that depends only on the change:

| phase | change | c |
|---|---|---|
| 1 (building 2s) | `0` → `1` at the walker | +16 |
| 1 | that `1` → `2`, the walker moves one digit left | +4 |
| 1 → 2 | the walker finds an old `1`: it becomes `3` | +18 |
| 2 (a carry) | `0 3` → `1 0` (the digit left of the `3`, and the `3`) | +14 |
| 2 | that `1` → `3`, the carry moves one digit left | −10 |
| 2, at the front | the leader takes the place of the digit: `11100` → `10100` | +14 |
| 1, at the front | the walker has no digit left: the leader `11100` → `10100`, digits unchanged | +16 |

So within an epoch the step of every round end is a closed form, T_r = 2^r T_0 + Σ 2^(r−i) c_i. After the leader
changes (from either phase) the next round is a **rebuild** (not modelled).

* Epoch 2 starts at step 40,509,722 with digits `0000100000` (then `3 0`, part of X), T = 2,926, N = 6; this
  configuration is proved in Lean (`epoch2_start`, `native_decide`). The walker turns digits 9..5 into `2`s (10
  rounds), meets the old `1` (→ `3`, 1 round), carries the `3` to the front (8 rounds) and changes the leader (1
  round) at step 6,201,936,302: `py/epoch.py` gives all 20 round ends to the step.
* Epoch 3 starts after the rebuild, at step 12,398,695,221 (digits `000001000|1220`, the walker at digit 5, N = 12).
  The law gives every round end seen; the ends at 96,327,513,809 and 180,338,374,341 were predicted before the
  simulator reached them. At 180,338,374,341 the digits are `222222000`: the phase-1 walker has reached the leader,
  a case epoch 2 did not show. In the next round, ending at 348,360,095,421, the leader becomes `10100` and the digits
  stay `222222000`; the step is T' = 2T + 16, as `py/epoch.py` gives it (12 rounds of epoch 3, all to the step).
  The round after is a rebuild, at 348,489,525,650.
* Epoch 4 starts there with 14 digits `00000030000010` and N = 2. Its first rounds (to 354,122,694,764) do not follow
  the table: the `3` becomes a `2`, then the digits run `0000011`, `0000031`, `0001001`, `0003001`, `0010001`,
  `0030001` (left part), a carry pattern with new constants that is not modelled yet.

**Rebuilds** at about 2.3·10^4, 4.05·10^7, 1.2·10^10 and 3.48·10^11 steps turn the tail and X into a new, longer list (4, 12, 13, 14
digits) and a new X; the tail starts again short (N = 1, then 11, then 1). Their rule is not known.

## Status

**Decided outside: it never halts.** busycoq pull request 86 (Alex Havrilla, DeepMind) proves it in Rocq; compiled here with Coq 8.20.1, no axioms. A token engine with base-4 digit blocks (6 cells per digit, carries proved for all sizes) runs 84,472 steps, about 10^708.37 machine steps, to a fixed window of 102 cells around the head in state D; 6,419 more engine steps return to the same window further right without reading anything left of it. What follows is this repository's own status.

Open. Proved in Lean, kernel only: the halting configurations (`step_none_iff`), no halt in 10,000 steps, three
early rounds for every tape further left (`lean/Rounds.lean`). With `native_decide`: no halt in 10^7 steps, and the
exact configuration at step 40,509,722, the start of epoch 2 (`epoch2_start`, `lean/Epoch.lean`). Computed
(trusted): no halt up to 354,122,694,764 steps; the walker law on every round of epochs 2 and 3, including the round
where the phase-1 walker changes the leader (`py/epoch.py check`, 32 rounds). A closed
tape language of windows up to 6 cells closes but allows F to read a 1, so it does not confine the halt.

## How far it was run

Direct simulation to 354,122,694,764 steps (`c/evrun.c`, resumable; about 70 minutes in pieces). The walker law is an
accelerated run of each epoch: from the start of an epoch it gives the step of every round end, as far as the walker
goes (for epoch 2 the 20 rounds to 6.2·10^9 steps, for epoch 3 the 12 rounds to 3.48·10^11), in microseconds. It
does not go through a rebuild.

## Open questions

* The rebuild map: the new digit list and X from the old ones (and the tail). With it, the walker law gives the
  whole run as arithmetic, and a `halts_iff` reduction would be in reach.
* Whether the phase-1 leader rule (c = +16, seen once) holds for all sizes, and the rounds of epoch 4, which start
  with a carry pattern not in the table.
* A proof of the walker law: the round is a binary counter of 2^N steps on the tail with one carry into the list;
  a Lean proof needs that counter as an induction on N, beyond `bbtools.symtm`'s shift rules.

## Related machines

1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE--- and 1RB0RF_1RC1LB_1LD1RE_1LB0LD_1RF0RC_1RA--- (their own folders) are
"binary counters applying one list operation W per tick", whose transients are likewise simulated, not modelled.
Here the list operation is the walker step above, and the time law T' = 2T + c is exact.

## Layout

| path | what it is |
|---|---|
| `lean/Machine.lean`, `lean/Blank.lean` | the machine, the halting configurations and bounded runs (generated) |
| `lean/Rounds.lean` | three early rounds, for every tape further left (generated by `py/gen_rounds.py`) |
| `lean/Epoch.lean` | the configuration at step 40,509,722, by `native_decide` (generated by `py/gen_epoch_lean.py`) |
| `py/epoch.py` | the walker law: `check` against a run, `ahead` for the rounds of epochs 2 and 3 |
| `c/evrun.c` | direct simulation with round-end output and checkpoints |

## Reproduce

```sh
. /etc/profile.d/lean.sh      # after scripts/setup-lean.sh
holdouts/1RB0RE_1LC0RA_1RE1LD_0LB0LF_1RA1RA_0LD---/lean/check.sh
gcc -O2 -o tmrun tools/c/tmrun.c && ./tmrun 1RB0RE_1LC0RA_1RE1LD_0LB0LF_1RA1RA_0LD--- 60000000000 at A R 5000 > ar.txt
python3 holdouts/1RB0RE_1LC0RA_1RE1LD_0LB0LF_1RA1RA_0LD---/py/epoch.py check ar.txt
python3 holdouts/1RB0RE_1LC0RA_1RE1LD_0LB0LF_1RA1RA_0LD---/py/epoch.py ahead
gcc -O3 -o evrun holdouts/1RB0RE_1LC0RA_1RE1LD_0LB0LF_1RA1RA_0LD---/c/evrun.c
./evrun 1RB0RE_1LC0RA_1RE1LD_0LB0LF_1RA1RA_0LD--- 150000000000 A R - ck1 > ev1.txt
./evrun 1RB0RE_1LC0RA_1RE1LD_0LB0LF_1RA1RA_0LD--- 400000000000 A R ck1 ck2 > ev2.txt
```

Pages: [`explainer.html`](../../pages/holdouts/1RB0RE_1LC0RA_1RE1LD_0LB0LF_1RA1RA_0LD---/explainer.html), [`proof-status.html`](../../pages/holdouts/1RB0RE_1LC0RA_1RE1LD_0LB0LF_1RA1RA_0LD---/proof-status.html).
