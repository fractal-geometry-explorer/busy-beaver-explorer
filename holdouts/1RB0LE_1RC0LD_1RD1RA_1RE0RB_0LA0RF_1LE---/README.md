# 1RB0LE_1RC0LD_1RD1RA_1RE0RB_0LA0RF_1LE---

bbchallenge id 23154. One of the six-state holdouts whose halting from blank tape is open (group G05, growth class
fixed/sqrt).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LE |
| B | 1RC | 0LD |
| C | 1RD | 1RA |
| D | 1RE | 0RB |
| E | 0LA | 0RF |
| F | 1LE | --- |

## Status

**Open.** This machine **is** [1RB0LC_1RC1RE_1RD0RA_0LE0RF_1RA0LD_1LD---](../1RB0LC_1RC1RE_1RD0RA_0LE0RF_1RA0LD_1LD---/README.md):
its table is that one with the states renamed A→B, B→C, C→D, D→E, E→A (F stays). Started on blank tape in A, it
starts the other machine's table in its state E, so it runs the same counter from another start: digits are blocks of
ones, and the head sweeps the tape once per increment, with the same digit rules and step counts.

Lean proves every ordinary sweep and every left-end sweep except the start of a *nested run* (a carry through every
digit into a leftmost block of even length, after which the counter runs again inside the tape), and proves that the
inner sweeps of a nested run follow the same digit rule. The run from blank tape has two nested runs in its first 29
sweeps and the third at sweep 258,075, step 266,357,150,814; the proved run goes up to there.

- Lean, kernel: the sweep rules (`lean/Sweep.lean`, `lean/Carry.lean`), the run from blank tape to sweep 29
  (`lean/Reach.lean`), the sweeps on run-length coded digits (`lean/Rle.lean`), the start of a nested run and its
  inner sweeps (`lean/Inner.lean`).
- Lean, `native_decide`: 258,046 consecutive proved sweeps, so **no halt in the first 266,357,150,814 steps**
  (2.7·10¹¹, `lean/RunLong.lean`, `no_halt_long`; before: 1,595,848,115 steps, `lean/MacroRun.lean`), and the next
  sweep is the start of the third nested run (`run_stops`).
- C: no halt in the first 3·10¹¹ steps (`c/brec.c`, cell by cell; the third nested run is still going on there).
  `c/dsim.c` (the proved sweep rules on run-length coded digits) reaches the third nested run in 0.02 s.

## What the tape is made of

A digit `d` is a block `0 1^(3d+2)`: a separator 0 followed by `3d+2` ones. Once per sweep the head is at the right
end in state C, and the tape is

    0^∞  1^r  [0 1^(3d₁+2)] … [0 1^(3dₘ+2)]  0 1 C>0  0^∞                         (P (raw r) [d₁ … dₘ])

or, in the other phase, the same with `0 1^4 C>0` at the end (`Q`). The leftmost block `1^r` is not a digit. Most
digits are 1 (`1^5`): a run of them fills the right part and grows by one digit every two sweeps. The active
digits form one cluster at the left, next to `1^r`. For example, at sweep 20,000:

    r3 0 0 1 2 0 0 3 1 1 0 1 1 1 1 1 2 … 1^9985

## One sweep

From the right end the head walks left in state E. It turns each odd block into `0 0 (1 0)^n` (`left_odd`) and turns
at the first even block (`turn_zero`, `turn_even`). It then walks back right in state B and rebuilds every block three
cells further right (`right_odd`, `tail_right`). With `a` the digit left of the stop digit `b` and odd digits
`2k₁+1, …` right of it (`sweep_zero`, `sweep_even`):

* `b = 0`:      `a 0 (2k₁+1) … (2kₙ+1)`  becomes  `(a+2) 0^(2k₁) 1 … 0^(2kₙ) 1`;
* `b = 2i+2`:   `a b (2k₁+1) … (2kₙ+1)`  becomes  `(a+1) 0^(b−1) 1 0^(2k₁) 1 … 0^(2kₙ) 1`,

in `21 + 10b + Σⱼ (20kⱼ + 16)` steps. This is an odometer. The rightmost even digit is the one that moves, the odd
digits right of it carry, and the long run of digits 1 is a run of carries already made.

The two machines' Lean files cut the turn differently (here `L 0 11 E>0` becomes `L 1111 B>` in 9 steps, and
`L 0 1^(6i+8) E>0` becomes `L 1110 110 (110110)^i 111 B>` in 20i+29 steps); the machines themselves are the same table
(see Status), so every piece is the other machine's with the states renamed.

## The left end

When no even digit is left, the left pass reaches `1^r`. The cases are proved as in the other machine:

* if the first digit is even, it merges into `1^r` (`raw_zero`: r + 6, `raw_even`: r + 3);
* if every digit is odd and r = 3 (`carry3_sweep`), the counter gets two leading zeros and the tape grows three
  cells to the left;
* if every digit is odd and r = 6j+9 (`carry9_sweep`), the block shrinks back to `1^3`, followed by zeros;
* if every digit is odd and r is even, a **nested run** starts.

## The nested run

The nested run is the counter counting inside its own count; it is described in the other machine's README, section
The nested run. In short: the left pass has turned every passed digit into a word (`0 0 1 0 1 0` for a digit 1); at
`1^(6j+6)` with a first digit 1 the leftmost block becomes `1^3` and `2j+1` digits 0 and the head turns back before
the right end (`nest_sweep`, kernel); from there an inner counter, left of a frontier, grows into the passed region
three cells per sweep. Its right end alternates between the phases `0 1 1 A>1 0` and `0 1 1 1 0 F>0 1 0`, every inner
sweep changes the digits by exactly the outer rule, and every sweep from the first phase eats one passed digit 1
(`inner_X_zero`, `inner_X_even`, `inner_Y_zero`, `inner_Y_even`, kernel). Not formalized: passed digits 3, 5, …, the
inner left-end events (which can nest again) and the end of the run, which leaves the right end in the other phase
`0 1^4 C>0`, after which `phase2_sweep` turns the last digit 1 into `2 0`.

In the run from blank tape:

| sweep | step | event |
|---|---|---|
| 5 | | nested run at r = 12 |
| 28 | | nested run at r = 6; at step 5,512 the tape is `Q (raw 3) [0,0,1,1,1,0,2,1^10]` |
| 127,004 | 64,493,655,427 | first digit 0 merges (r 3 → 9) |
| 192,540 | 148,246,566,259 | first digit 2 merges (r 9 → 12) |
| 258,075 | 266,357,150,814 | carry into `1^12`: the third nested run starts, at `1^12 \| 1 1 5 1^9 3 1^129022 \| 0 1 C>0` |

The third nested run runs on a tape of about 7.7·10⁵ cells and should take about 3·10¹¹ steps (the first nested run
of the other machine, on 1.6·10⁴ cells, took 1.2·10⁸, about half the square of the tape length).

## Where it could halt

The only halting transition is F on a 1. Following the table backwards (as in the other machine, renamed), **the
machine halts exactly when C reads a 0 followed by `0 1 1`**: C writes 1, D reads 0, E reads 1 and moves right, F
reads 1. No proved rule produces this pattern, so a halt would have to come from a nested run.

## What is proved

| file | content | level |
|---|---|---|
| `lean/Rules.lean` | the pieces of a sweep, for all parameters (`py/gen_rules.py`, `bbtools.symtm`) | kernel |
| `lean/Sweep.lean` | `sweep_zero`, `sweep_even`, `raw_zero`, `raw_even`, `cost_sum` | kernel |
| `lean/Carry.lean` | `carry3_sweep`, `carry9_sweep`, `phase2_sweep` | kernel |
| `lean/Reach.lean` | `reach_D0`: blank tape reaches `Q (raw 3) [0,0,1,1,1,0,2,1^10]` in 5,512 steps | kernel |
| `lean/MacroRun.lean` | `next`, `stepT`, `next_sound`, `run_sound`; `no_halt_1595848115` | native |
| `lean/Rle.lean` | `nextR` (sweeps on run-length coded digits), `nextR_sound`, `runR_sound` | kernel |
| `lean/RunLong.lean` | 258,046 sweeps: `no_halt_long` (266,357,150,814 steps), `run_stops` | native |
| `lean/InnerRules.lean` | the end pieces of inner sweeps and the start of a nested run (`py/gen_inner.py`) | kernel |
| `lean/Inner.lean` | `core_zero`, `core_even`, `inner_X_*`, `inner_Y_*`, `nest_sweep` | kernel |

## Evidence

- `c/dsim.c` (shared with the other machine) runs the proved sweep rules on run-length coded digits with exact step
  counts; its numbers are the ones `RunLong.lean` checks.
- `c/brec.c` (`gcc -O2 -o brec c/brec.c && ./brec MACHINE 300000000000 50000 C`) prints the digits every 50,000
  sweeps; it finds no halt in 3·10¹¹ steps, which ends inside the third nested run.

## Reproduce

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LE_1RC0LD_1RD1RA_1RE0RB_0LA0RF_1LE---/lean/check.sh
python3 holdouts/1RB0LE_1RC0LD_1RD1RA_1RE0RB_0LA0RF_1LE---/py/gen_rules.py > holdouts/1RB0LE_1RC0LD_1RD1RA_1RE0RB_0LA0RF_1LE---/lean/Rules.lean
python3 holdouts/1RB0LE_1RC0LD_1RD1RA_1RE0RB_0LA0RF_1LE---/py/gen_inner.py > holdouts/1RB0LE_1RC0LD_1RD1RA_1RE0RB_0LA0RF_1LE---/lean/InnerRules.lean
gcc -O2 -o dsim holdouts/1RB0LE_1RC0LD_1RD1RA_1RE0RB_0LA0RF_1LE---/c/dsim.c
./dsim 3 1 0,0,1,1,1,0,2,1,1,1,1,1,1,1,1,1,1 5512 1e12          # stops at the third nested run
```

## For later

The same as for the other machine: the whole nested run as a theorem, written once for the shared rules (it would
serve both machines), would make `nextR` total. A direct simulation of the third nested run (about 3·10¹¹ steps,
a few hours in C) would give the configuration after it, from which `c/dsim.c` can go on; crossing it in Lean needs
the nested run as a theorem, since 3·10¹¹ single steps are beyond `native_decide`.

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB---_0RC0LA_1LD0RB_1LE0RF_1LF1LC_1LB0LD`](../1RB---_0RC0LA_1LD0RB_1LE0RF_1LF1LC_1LB0LD/README.md): rename A→C, B→D, C→E, D→F, E→B, F→A and exchange left and right; it is this table started in state F, in a mirror
- [`1RB0LC_1RC1RE_1RD0RA_0LE0RF_1RA0LD_1LD---`](../1RB0LC_1RC1RE_1RD0RA_0LE0RF_1RA0LD_1LD---/README.md): rename A→E, B→A, C→B, D→C, E→D, F→F; it is this table started in state B

<!-- end of related machines -->
