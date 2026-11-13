# 1RB0LC_1RC1RE_1RD0RA_0LE0RF_1RA0LD_1LD---

bbchallenge id 115779. One of the six-state holdouts whose halting from blank tape is open (group G05, growth class
fixed/sqrt).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LC |
| B | 1RC | 1RE |
| C | 1RD | 0RA |
| D | 0LE | 0RF |
| E | 1RA | 0LD |
| F | 1LD | --- |

## Status

**Open.** The machine is a counter written in blocks of ones, swept by the head once per increment. Every ordinary
sweep and every sweep at the left end but one kind is proved in Lean for all values of its parameters. The one kind
left, a carry through every digit into a leftmost block of even length, starts a *nested run*: the same counter runs
again inside the tape, growing into the part the head has just passed. Its inner sweeps are proved too, but not the
whole nested run, so the proof does not close.

- Lean, kernel: the sweep rules (`lean/Sweep.lean`, `lean/Carry.lean`), the sweeps on run-length coded digits
  (`lean/Rle.lean`), the inner sweeps of a nested run and its start (`lean/Inner.lean`), and the reduction
  `halts_imp_uncovered` (`lean/Reduce.lean`): **if the machine halts, the counter, run from step 231,327,122, reaches
  a sweep the proved rules do not cover** (in practice: the next nested run).
- Lean, `native_decide`: the first nested run, cell by cell (`lean/Nested.lean`, 115,676,475 steps), and the proved
  sweeps around it: **no halt in the first 400,000,471,326,994 steps** (4·10¹⁴, `lean/RunLong.lean`, `no_halt_long`).
- C (`c/dsim.c`, the proved sweep rules on run-length coded digits): from step 231,327,122 the counter runs
  2,121,320,341 sweeps, to step 1.8·10¹⁹, and never meets an uncovered sweep. So **no halt in the first 1.8·10¹⁹
  steps** (trusted).

The other machine of this pair, `1RB0LE_1RC0LD_1RD1RA_1RE0RB_0LA0RF_1LE---`, **has this machine's table**: its table is this
one with the states renamed A→B, B→C, C→D, D→E, E→A (F stays). It starts on blank tape in the state that is E here,
so it runs the same counter from a different start.

## What the tape is made of

Read the tape as **digits**: a digit `d` is a block `0 1^(3d+2)`, a separator 0 followed by `3d+2` ones (so `1^2`,
`1^5`, `1^8`, `1^11`, … are the digits 0, 1, 2, 3, …). Once per sweep the head is at the right end in state B and the
tape is

    0^∞  1^r  [0 1^(3d₁+2)] [0 1^(3d₂+2)] … [0 1^(3dₘ+2)]  0 1 B>0  0^∞            (P (raw r) [d₁ … dₘ])

with a leftmost block `1^r` that is not a digit (r = 3 for most of the run), or the same with `0 1^4 B>0` at the end
(`Q`, the other phase of the right end, after a nested run).

## One sweep

From the right end the head walks left. Moving left it turns each block of ones into alternating `0 1`; a block of
odd length (an **odd digit**) is passed, the first block of even length (an **even digit** `b`) stops it. The head
turns there and walks back right to the end, rebuilding every block, now three cells further right. On digits, with
`a` the digit left of the stop digit `b` and odd digits `2k₁+1, …, 2kₙ+1` right of it (`sweep_zero`, `sweep_even`):

* `b = 0`:      `a 0 (2k₁+1) … (2kₙ+1)`  becomes  `(a+2) 0^(2k₁) 1 … 0^(2kₙ) 1`;
* `b = 2i+2`:   `a b (2k₁+1) … (2kₙ+1)`  becomes  `(a+1) 0^(b−1) 1 0^(2k₁) 1 … 0^(2kₙ) 1`,

in `21 + 10b + Σⱼ (20kⱼ + 16)` steps. Every sweep adds three cells, so after `s` sweeps the tape is about `3s` cells
long and the step count is about `4s²`. This is an odometer: the rightmost even digit is the active one, the odd
digits right of it are like the 9s of a decimal increment, and runs of digits 1 are passed unchanged (a digit 1 stays
a digit 1), so a long run of 1s separates independent clusters of active digits.

## The left end

When no even digit is left, the left pass reaches the leftmost block `1^r`:

* the first digit is even (`raw_zero`, `raw_even`): it merges into the leftmost block, `r` grows by 6 or 3;
* every digit is odd, `r = 3` (`carry3_sweep`): the counter gets two new leading zeros, the tape grows three cells to
  the left;
* every digit is odd, `r = 6j+9` (`carry9_sweep`): the leftmost block becomes `1^3` followed by `2j+3` zeros;
* every digit is odd, `r` even (`r = 6j+6`): a **nested run** starts.

## The nested run

The left pass has turned every digit into its left-pass form (a digit `2k+1` into the word `0 0 (1 0)^(3k+2)`, a
digit 1 into `0 0 1 0 1 0`) and reached `1^(6j+6)`. If the first digit is 1 (`nest_sweep`, kernel), the leftmost
block becomes `1^3` and `2j+1` digits 0, and the head turns back **without going to the right end**: right of it lies
the passed region. From here the left part is again a counter, swept by *inner sweeps*, whose right end sits at a
frontier inside the passed region, in one of two phases:

    X:   [digits]  0 1 1 E>1 0  [passed region]
    Y:   [digits]  0 1 1 1 0 F>0 1 0  [passed region]

`lean/Inner.lean` proves (kernel, for every digit list) that an inner sweep changes the digits by **exactly the same
rule** as an outer sweep (both use the same core, `core_zero` / `core_even`, with any tape right of the left pass),
that the phase alternates X, Y, X, …, and that every sweep from phase X eats one passed digit 1 (`inner_X_zero`,
`inner_X_even`, `inner_Y_zero`, `inner_Y_even`). So the inner counter grows into the passed region three cells per
sweep, as the outer counter grows into blank tape: the nested run is the counter counting *inside its own count*.

Not formalized, seen in simulation (`py/nested_view.py` prints the phases X and Y of a nested run with its inner
digits and the passed region; heuristic):

* passed digits 3, 5, … (`0 0 (1 0)^(3k+2)`) are eaten in a different phase pattern, with sweeps whose right end
  closes a block `1^4` instead of `1^5`;
* the inner counter has its own left-end events, including carries into an even leftmost block, which start a
  nested run inside the nested run (seen at depth 2, e.g. from `1^6 | 1^10`);
* when the passed region is used up the run ends with the right end in phase `Q` (`0 1^4 B>0`); when a deeper level
  ends first, the rest of the passed region of the level above is closed up into one large digit.

In the run from blank tape there is **one** nested run so far, at sweep 5,391 (`nested_run`, native):

    1^12 | 1 3 1 1 1 1 1 3 1^2686 | 0 1 B>0      step 115,650,647
    1^15 | 2 0 0 1 1 1 1 1 1 0 2 1^2686 | 0 1^4 B>0      step 231,327,122

(the passed digits 3 make this run use the unformalized patterns). The next sweep (`phase2_sweep`) turns the last
digit 1 into `2 0` and the counter goes on.

## The long run

| sweep | step | event |
|---|---|---|
| 1,295 | 6,576,428 | carry at the left end, `r = 3` |
| 3,343 | 44,357,912 | first digit 0 merges, `r` 3 → 9 |
| 4,367 | 75,831,560 | first digit 2 merges, `r` 9 → 12 |
| 5,391 | 115,650,647 | carry into `1^12`: the nested run, to step 231,327,122, `r` = 15 |
| to 2.1·10⁹ | to 1.8·10¹⁹ | nothing: the left end is not reached again |

After the nested run the digits form three clusters: a fixed left part `2 0 0 1^6 0 2`, a long run of 1s (2,686 at
first), a middle cluster, a `2`, a growing run of 1s, and a small right cluster at the end, e.g. at sweep 10⁹ (step
4.0·10¹⁸):

    2 0^2 1^6 0 2 1^2657 2 1^2 0 2 1^2 0 1 2 1 0 2 0 2 1 0 1 2 0 2 0 1^7 2 1^499999999

The middle cluster eats into the run of 1s slowly, about three digits per factor 10 of sweeps (2,667 at sweep 10⁶,
2,660 at 10⁸, 2,656 at 2.1·10⁹). The left end can only be reached again when no even digit is left on the whole
tape; at this rate that is very far away (extrapolating, around 10⁸⁰⁰ sweeps; heuristic).

## Where it could halt

The only halting transition is F on a 1. Following the table backwards, **the machine halts exactly when B reads a 0
followed by `0 1 1`** (B writes 1, C reads 0, D reads 1 and moves right, F reads 1): a right-moving head meeting
`0 0 1 1`. F is entered only from D on a 1 (moving right); D reaches a 1 from C moving right, or from E or F moving
left, and in the last two cases, and when C comes from A, the cell it then moves onto is a 0 just written, so the only
way in is B, C, D, F moving right over `0 0 1 1`. No proved rule produces this pattern;
`halts_imp_uncovered` puts any halt after a sweep the rules do not cover, i.e. inside a later nested run (or the other
phase with a last digit other than 1, which the nested runs seen so far do not produce).

## What is proved

| file | content | level |
|---|---|---|
| `lean/Rules.lean` | the pieces of a sweep, for all parameters (`py/gen_rules.py`, `bbtools.symtm`) | kernel |
| `lean/Sweep.lean` | `sweep_zero`, `sweep_even`, `raw_zero`, `raw_even`, `cost_sum` | kernel |
| `lean/Carry.lean` | `carry3_sweep`, `carry9_sweep`, `phase2_sweep` | kernel |
| `lean/Reach.lean` | `reach_D0`: blank tape reaches `P (raw 3) [0,2,2,1,1,1,1,1,2,0]` in 2,340 steps | kernel |
| `lean/MacroRun.lean` | `next` (one sweep on digit lists), `next_sound`, `no_halt_115650647` | native |
| `lean/Rle.lean` | `nextR`: one sweep on run-length coded digits (same cases as `next`), `nextR_sound`, `runR_sound` | kernel |
| `lean/Nested.lean` | `nested_run`: the first nested run, 115,676,475 steps, by the list simulator | native |
| `lean/RunLong.lean` | 5,373 sweeps, the nested run, 10⁷ more sweeps: `no_halt_long` (4·10¹⁴ steps) | native |
| `lean/Reduce.lean` | `nextR_pos`, `not_halts_of_runR`, `halts_imp_uncovered` | kernel (on `reach_B`, native) |
| `lean/InnerRules.lean` | the end pieces of inner sweeps and the start of a nested run (`py/gen_inner.py`) | kernel |
| `lean/Inner.lean` | `core_zero`, `core_even`, `inner_X_*`, `inner_Y_*`, `nest_sweep` | kernel |

`lean/check.sh` checks all of them (about 6 minutes, most of it `Nested.lean` and `RunLong.lean`).

## Evidence

- `c/dsim.c` runs the proved sweep rules on run-length coded digits (exact step counts, 64-bit): 2.1·10⁹ sweeps in
  30 s. It agrees with the Lean runs (`run1_value`, `run2_value` use its numbers) and with the cell simulator
  `c/brec.c` (sweep 5,373 at step 115,650,647; the end of the nested run at 231,327,122).
- `c/brec.c` (cell by cell) finds no halt in 3·10¹¹ steps.

## Reproduce

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LC_1RC1RE_1RD0RA_0LE0RF_1RA0LD_1LD---/lean/check.sh
python3 holdouts/1RB0LC_1RC1RE_1RD0RA_0LE0RF_1RA0LD_1LD---/py/gen_rules.py   # regenerates lean/Rules.lean
python3 holdouts/1RB0LC_1RC1RE_1RD0RA_0LE0RF_1RA0LD_1LD---/py/gen_inner.py   # regenerates lean/InnerRules.lean
gcc -O2 -o dsim holdouts/1RB0LC_1RC1RE_1RD0RA_0LE0RF_1RA0LD_1LD---/c/dsim.c
./dsim 3 0 0,2,2,1,1,1,1,1,2,0 2340 1e9                         # to the first nested run (sweep 5,373)
./dsim 15 1 2,0,0,1,1,1,1,1,1,0,2$(python3 -c "print(',1'*2686)") 231327122 1.8e19 100000000
```

## For later

The missing piece is the whole nested run as a theorem: the inner left-end events (which can start a deeper nested
run), passed digits other than 1, and the end of the run, so that `nextR` becomes total. Then the question becomes
one about the counter alone: whether its nested runs, which come at ever longer intervals, always end in a sweep
configuration. A closed invariant on macro configurations would have to describe the stack of passed regions of
nested runs; generic closed tape languages (cell windows up to 6, and run-length windows) fail early because they
lose the block lengths mod 3. A direct cell simulation of the next nested run is out of reach (it is not due before
10¹⁹ steps).

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB---_0RC0LA_1LD0RB_1LE0RF_1LF1LC_1LB0LD`](../1RB---_0RC0LA_1LD0RB_1LE0RF_1LF1LC_1LB0LD/README.md): rename A→D, B→E, C→F, D→B, E→C, F→A and exchange left and right; it is this table started in state F, in a mirror
- [`1RB0LE_1RC0LD_1RD1RA_1RE0RB_0LA0RF_1LE---`](../1RB0LE_1RC0LD_1RD1RA_1RE0RB_0LA0RF_1LE---/README.md): rename A→B, B→C, C→D, D→E, E→A, F→F; it is this table started in state E

<!-- end of related machines -->
