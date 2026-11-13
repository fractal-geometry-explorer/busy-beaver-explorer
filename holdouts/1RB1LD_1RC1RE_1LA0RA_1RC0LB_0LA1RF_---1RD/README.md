# 1RB1LD_1RC1RE_1LA0RA_1RC0LB_0LA1RF_---1RD

bbchallenge id 19219. One of the six-state holdouts whose halting from blank tape is open. It writes the same tape as
[`1RB1LD_1RC1RF_1LA1RD_1RE0LB_---0RA_0LA1RC`](../1RB1LD_1RC1RF_1LA1RD_1RE0LB_---0RA_0LA1RC/README.md), step for step, in every run so far (10^9 steps; observed, not proved).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LD |
| B | 1RC | 1RE |
| C | 1LA | 0RA |
| D | 1RC | 0LB |
| E | 0LA | 1RF |
| F | --- | 1RD |

## What it does

**A base-4 countdown on a list of blocks, and an exact map for the whole run.** At the start of every tick, the
head turns in state A just past the near end of the tape, and the tape reads

    0^inf 1110 (111110)^n 1 A> [word] 0^inf        (n even)

Every cell pair right of the head starts with a 1. So the right side is a bit string, the **word**: the pair `1b`
is the bit b. A block of v = `101110` is the bits `010`. The separators r = `10`, q = `1110`, p = `101011` and
s = `11` are the bits `0`, `10`, `001` and `1`. The block of w = `111110` on the left grows by two copies per tick.
The first block of the word is the *timer*.

A tick is a borrow into the separator after the timer. At a separator with block a before it and block b after it:

| separator | becomes | blocks | Lean |
|---|---|---|---|
| r `0` | q `10` | b - 1 | `tick_r` |
| q `10` | p `001` | a - 1 | `tick_q`, `tick_q2` |
| p `001` (any bits starting `00`) | s `1` (drop the `00`) | none | `tick_p`, `tick_p1` |
| s `1` | r `0` | a - 1, b + 1, the borrow goes on to the next separator | `tick_s` |

Each separator is a base-4 digit, so block i loses about 2·4^-(i+1) per tick. A tick takes 72n + 6j + 182 + 4m + 10
steps, without the 10 unless it ends with q -> p. Here j is the bit position of the last separator the borrow
reaches and m is the number of s -> r. Then n grows by 2.

The rules are stated on bits, so they also cover the separators that appear when a block in the middle runs out,
such as `10001` (a q and a p with nothing between). Two more local moves complete the tick rule:

- **The other phase.** A word `01 W` whose own tick does not apply is the same tick half a step later. It moves as W
  does with n - 1, and takes 90 more steps.
- **The wall.** The word `0101 v^x` (a timer of one, then s) goes to `<2>10<x-2>` in 72n + 228 steps (`tick_w`).
  Two ordinary ticks bring it back to `0101 v^(x-2)`. So the block behind the s runs down by 2 every 3 ticks, and no
  borrow passes it. The long run below makes 185,236,728 wall moves.

Everything else is an **event**: a borrow reaches the far end, or the timer runs out. Two events have exact
formulas, which hold at every overflow the run reaches:

- **F1, overflow.** If every separator is s and the far end reads `11`, the list (n; x1, ..., xk) becomes
  (6; n+1, x1-1, x2-1, x3, ..., xk). The separators become r, q, r, ..., r and the far end becomes `0011`. The grown
  w-block is the new timer, which is why new timers are close to 4^k. Lean proves this
  for k = 2 and k = 3 (`overflow_2`, `overflow_3`): 148n + 46x1 + 28(x2 + ...) + const steps.
- **F2, the timer runs out at a q.** For the word `01 v^x1 s ... s v^xk 11`, the list becomes
  (6; n, x1+1, x2-1, x3, ...), and the separators and far end become r, q, r, ..., r and `0011` as in F1.

The other events are borrows reaching the far end while it is still being worn down. They are computed by running
the machine itself on a copy of the configuration with every block cut to 40 copies and n cut to 30. The copy is
run again with each block, and n, one larger, which shows how the result and the step count depend on each size.
Each event is computed with two different cuts (40/30 and 47/38), and the two must agree.

## The map against the machine

`py/macro.py` is this map: the tick rules, the other phase, the wall, and events from cut copies.
`c/rword.c` prints every tick boundary of the real run. `py/check_macro.py` checks each row against the one before
it.

- **The first 6·10^9 steps:** 22,198 of 22,198 moves reach exactly the machine's next row: the same n, the same
  word and the same step count. 53 of the moves are events.
- **The twin:** the same rows and the same check, run with the twin's own transitions, pass for
  1RB1LD_1RC1RF_1LA1RD_1RE0LB_---0RA_0LA1RC.

Run on its own from the first tick (`py/longrun.py`), the map reaches 1.0·10^19 steps, 627,024,786 ticks and
205 events, all with both cuts agreeing. The first 400 moves by the other phase and by the wall were
also compared with the machine. No cut copy halts. At the end the list is

    n = 613,394,514; blocks 1, 222,014,566, 1, 612,354, 493, 644, 9,920, 1,002

The run meets 89 overflows (F1 and F2), the last at about 3.5·10^18 steps. The largest new timers are 4,194,301 (at 1.1·10^15), 33,628,307 (at 2.2·10^16), 129,459,917 (at 3.3·10^17), 416,954,747 (at 3.5·10^18).

## Where it could halt

The machine halts only on F reading 0. Ticks never do that. A borrow arriving at the far end halts the machine when
the far end reads `01`, `101`, `1101`, `11101`, `101001` and similar: these are all the cases up to 8 bits
(`py/farend.py`). The run has shown 102 different far ends (what follows the last block of 10 or more). Closed under
borrow arrivals they give 128, and none of them halts. Every one of them falls into the 2-cycle `11` -> (overflow) ->
`0011` -> `11`. In that cycle the last block loses one at every overflow. So the far end cannot halt as long as the
last block lasts. That block is 1,002 at the end of the long run, and the far end is reached exponentially rarely (once in about 4^k ticks).
Whether halting ever happens comes down to what the list looks like when that block, and the ones before it, have
worn away.

## Rules proved in Lean (`lean/Rules.lean`, generated by `lean/rules.py`)

All of these hold for every length of the w-block and of the blocks shown:

- `tick_r`, `tick_q`, `tick_p`, `tick_s`: the four ticks, for every tape beyond the next block. `tick_s` is stated
  with the following separator a p.
- `tick_w`, `tick_q2`, `tick_p1`: the wall cycle (`0101 v^x` -> `<2>10 v^(x-2)` -> `<1>001 ...` -> `<1>1 ...`).
- `overflow_2`, `overflow_3`: overflow F1 with two and with three blocks, from the tick boundary to the next tick
  boundary.

## Status

**Open.** Proved in Lean: the halting configurations and no halt in 10^7 steps (`lean/Blank.lean`), nine tick and
overflow rules (`lean/Rules.lean`). Checked against the machine: the map reproduces every tick boundary of the first
6·10^9 steps exactly, and it runs on to 1.0·10^19 steps without a halting event. Heuristic: the far end
cannot halt while the last block lasts.

## For later

- Lean versions of the borrow chain (a run of s separators) and of F1 for every k, by induction on the list. The
  pieces (the sweep through one block and separator in each direction) should be symtm rules with arbitrary tapes
  on both sides.
- A proof of the far-end closure: the 128 suffixes and their moves, each as a symtm rule.
- What the list looks like when the last block is worn away, and whether a far end like `...01` can then appear.
- Proving the twin correspondence in Lean, which needs the three local patterns as an invariant.

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LD_1RC1RE_1LA0RA_1RC0LB_0LA1RF_---1RD/lean/check.sh
cd holdouts/1RB1LD_1RC1RE_1LA0RA_1RC0LB_0LA1RF_---1RD
gcc -O2 -o /tmp/rword c/rword.c
/tmp/rword 1RB1LD_1RC1RE_1LA0RA_1RC0LB_0LA1RF_---1RD 6000000000 | awk '$2%2==0' > /tmp/rows6.txt     # ~4 min
python3 py/check_macro.py verify < /tmp/rows6.txt
python3 py/farend.py < /tmp/rows6.txt
python3 py/longrun.py 2700 verify checkshifted=400                  # the map on its own, 45 min
gcc -O2 -o /tmp/twin c/twin.c && /tmp/twin 1RB1LD_1RC1RE_1LA0RA_1RC0LB_0LA1RF_---1RD 1RB1LD_1RC1RF_1LA1RD_1RE0LB_---0RA_0LA1RC 1000000000
gcc -O2 -o /tmp/turns c/turns.c && /tmp/turns 1RB1LD_1RC1RE_1LA0RA_1RC0LB_0LA1RF_---1RD 300000000 100000000 30 | python3 py/check_countdown.py
```

## Pages

- [`pages/holdouts/1RB1LD_1RC1RE_1LA0RA_1RC0LB_0LA1RF_---1RD/explainer.html`](../../pages/holdouts/1RB1LD_1RC1RE_1LA0RA_1RC0LB_0LA1RF_---1RD/explainer.html)
- [`pages/holdouts/1RB1LD_1RC1RE_1LA0RA_1RC0LB_0LA1RF_---1RD/proof-status.html`](../../pages/holdouts/1RB1LD_1RC1RE_1LA0RA_1RC0LB_0LA1RF_---1RD/proof-status.html)

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same run as [`1RB1LD_1RC1RF_1LA1RD_1RE0LB_---0RA_0LA1RC`](../1RB1LD_1RC1RF_1LA1RD_1RE0LB_---0RA_0LA1RC/README.md) (observed, not proved).** At every one of the first 10^7 steps from blank tape the two machines have the same tape and the head on the same cell. Their tables differ, and no renaming of the states turns one into the other. While they run, the states pair up as A–A, B–B, C–C, C–E, D–D, E–F, F–C (this machine first), which is not one to one. Transitions not used in these steps: this machine never uses F0 and the other never uses E0. Lean proves (`lean/Twin.lean` in the other machine's folder, `lock_or_break`, `not_halts_of_noBreak`) that the two runs have the same tape, the same head position and paired states up to the first break, a configuration where the paired states act differently, and that neither machine halts if no break ever comes. A halt of either machine is itself a break, and the halting transitions of the two do not correspond, so the two are not known to halt together.

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB1RE_1LC0RC_1RA1LD_1RB0LA_0LC1RF_---1RD`](../1RB1RE_1LC0RC_1RA1LD_1RB0LA_0LC1RF_---1RD/README.md): rename A→C, B→A, C→B, D→D, E→E, F→F; it is this table started in state B

<!-- end of related machines -->
