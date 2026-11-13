# 1RB0LF_0LC0RE_0RA1LD_1LB0LD_0RA1RC_1LA---

bbchallenge id 129771, a six-state holdout of group G05. **Open.** The tape is a binary counter on blocks
`(10)^D x`. Its phases grow by a Collatz-like 3/2 map. An exact block-level macro machine reproduces direct
simulation record for record. Every crossing rule it used in the first 300,000 records is proved in Lean (kernel), for
all block sizes and all surrounding tapes. The macro run finds no halt in 338,536,834,271,065 (3.39·10^14) steps. No invariant that excludes
the halt is known.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LF |
| B | 0LC | 0RE |
| C | 0RA | 1LD |
| D | 1LB | 0LD |
| E | 0RA | 1RC |
| F | 1LA | --- |

## The tape at a left record

A *left record* is a moment when state B stands strictly left of every cell visited so far. Write
`P = 10`. At every left record the tape is

    0^inf  ell  B>c  P^D1 x1  P^D2 x2  P^D3 x3 ...  0^inf          x = i (1) or o (0)

Here `ell` is empty or a single 1, and `c` is 0 or 1 (`ell = 1, c = 1` occurs only right after a reset). The blank
right end is the same as an endless list of blocks `(0, o)`. The previous worker's separators fit this as follows:
`1^2 0` is `... P^D i  P^0 ...`, and `1 0^2` is an o-block.

In the first 10^5 records (a one-off scan of the macro run; heuristic):
- no block `(0, i)` appears after the first;
- the block after an o-block has D + x even;
- the first block has D + x odd, or `ell = 1, c = 1`, first block `(0, o)` and the second has D + x odd.

## One sweep

From the record, the head goes right. For blocks with D ≥ 8 it carries a phase bit, α (state A) or β (state B/E).
Crossing a block `P^D x` flips the phase when D + x is even. The sweep turns at the first o-block with D + phase
odd: α turns at an odd o-block, β at an even one. On the way out it re-encodes `1010` as `1100`. On the way back,
state B (or D) restores the blocks and changes the ones the counter changes. It then reaches the left end one cell
further out, which is the next record.

Most sweeps are of this kind (99.99% of macro steps: right crossings, one turn, left crossings). The rest bounce
several times on short blocks. The macro machine handles every pattern of bounces the same way; nothing is
special-cased.

The long sweep, for the common even case, is the theorem `carry_even` (`lean/Sweep.lean`, kernel, for all a, b, the
list ts and the tape R):

    0^inf B> 0 (1010)^(a+2) 1 10 1 [ (1010)^(t+4) 1 ]^ts 10 (1010)^(b+4) 0 R
      ->  0^inf B> 0 1 0 1 (0101)^a 0 1 0 0 0 1 0 1 0 1 [ (0101)^(t+3) 0 1 0 0 1 ]^ts 0 1 0 1 (0101)^(b+3) 0 1 1 0 R

In blocks this is one increment. The head pair `P^(2a+4) i P i` becomes `P^(2a+3) o o`. The even i-blocks of the
list become o-blocks, with +2 on the first. The odd o-block `P^(2b+9) o` becomes an i-block, and the block after it
gets +1. The short sweep that follows (`short`, `lean/Macro.lean`) restores the head pair.

## The block macro machine (`py/blockmm.py`)

`macro_step(ell, c, blocks)` maps a record to the next record exactly, or reports a halt.
- **Words.** The tape between the two records is a left stack and a right stack of *words*. A word is a token list
  with its own parameter t. A block with D < 8 is a literal word. Larger blocks are `(1010)^(t+4) x` (D even) or
  `10 (1010)^(t+4) x` (D odd).
- **Crossings.** The head is in a *situation*: moving right with the last 8 cells known, moving right on the blank
  side, or moving left with up to 1000 cells known on its right. Crossing a word of a given kind from a given
  situation is one `bbtools.symtm` run, valid for every t, and it is cached. The run either passes the word, turns
  inside it, reaches the record, or halts.
- **Normal form.** Between crossings, `normalize` rewrites words so every repeat count is at least 2, or writes the
  word out in full. At the record, `reparse` reads the cells back into P-blocks.
- **Rules.** The first 300,000 records use 111 right-crossing and 276 left-crossing rules. `py/gen_rules.py` writes
  each one as a Lean theorem (`lean/Rules.lean`, `right0` ... `right110`, `left0` ... `left275`). Each theorem is
  `steps n <start> = some <end>` for every t and every tape outside the known context.

What is **not** proved in Lean is the composition: that the Python bookkeeping (stacks, `normalize`, `reparse`)
glues the rules together correctly. That part is trusted Python. It is cross-checked against direct simulation:
`py/check_macro.py` compares steps, head cell and blocks at each of the first 15,144 records (3·10^8 steps). All
agree. It also reproduces the previous worker's C run exactly: record 300,000 at step 116,666,829,938.

## Phases and the reset map

The first block counts down by 2 per increment. When it runs out, the next blocks move down. Resets found by the
macro run (record, step, first two blocks after the reset):

| record | step | X | Y |
|---|---|---|---|
| 280 | 100,433 | 142 i | 53 o |
| 1,454 | 2,651,707 | 727 o | 337 i |
| 7,392 | 68,628,877 | 3,697 o | 1,810 o |
| 37,459 | 1,757,615,063 | 18,733 o | 9,314 o |
| 189,692 | 45,293,767,053 | 94,849 o | 47,362 o |
| 960,369 | 1,157,584,303,737 | 480,190 i | 240,019 o |
| 4,861,933 | 29,630,629,246,279 | 2,430,970 i | 1,215,401 o |
| 7,292,906 | 66,659,636,161,183 | 3,646,456 i | 1,823,142 i |
| 10,939,365 | 150,649,541,815,643 | 5,469,685 o | 2,734,754 o |
| 16,409,053 | 338,536,834,271,065 | 8,204,530 i | 4,102,173 o |

**Heuristic.** At every reset so far (27 of 27 transitions), X maps to X' = 3X/2 + 1 for even X and to
X' = (3X + 5)/2 for odd X. For example, 142 → 214 → 322 → 484 → 727 → 1093. Y follows Y' ≈ 3Y/2 + c, where c grows
slowly (8 ... 40). Each phase takes about 2.25 times as many steps as the one before. The parities of the blocks
decide the corrections, so the long-run behaviour is a Collatz-like question.

## Where it could halt

F is entered only by A reading 1 (A1 = 0LF), and F1 halts. So the machine halts exactly on `1 A>1`. Neither the
macro run nor the direct simulation has reached it. The record patterns above are **not** an invariant.
`py/random_check.py` builds 20,000 random block lists and runs one macro step on each. 2 of 14,742 lists that obey
the three patterns halt, and 2 of 5,258 that do not. Excluding the halt therefore needs finer information about
which lists the run can reach.

## Status and evidence

**Lean, kernel**:
- `right0` ... `right110`, `left0` ... `left275` (`lean/Rules.lean`, from `py/gen_rules.py`): every crossing rule of
  the macro machine used in the first 300,000 records, for all t and all tapes;
- `carry_even` (`lean/Sweep.lean`, from `py/gen_sweep.py` with `bbtools.seqtm`): the even long sweep over an
  arbitrary list of blocks; `lean/Seq.lean` is the sequence library, copied from bb6-1RB1RF_1LC0LB;
- `short_raw` / `short` (`lean/Gadgets.lean`, `lean/Macro.lean`): the short sweep for every x and tape;
- `reach2438`, `reach2522`: the run from blank tape reaches the first counter configuration;
- `step_none_iff`, `blank_runs_kernel` (`lean/Blank.lean`): halting configurations; no halt in 10^4 steps.

**Lean, native_decide**: `blank_runs_native`, no halt in 10^7 steps.

**Computed (trusted)**:
- `py/check_macro.py`: the macro machine agrees with `c/recp.c` (direct simulation) at all 15,144 records up to
  step 299,979,488.
- `py/run_macro.py`: no halt through 16,409,053 left records, 338,536,834,271,065 (3.39·10^14) steps and
  28 resets. This rests on the composition in `py/blockmm.py`; each rule it applies is a symtm run, and the
  rules of the first 300,000 records are the ones in Lean.
- `c/rec18.c` (previous pass): no halt in 1.17·10^11 steps, by direct simulation.

**Heuristic**: the reset map, the three record patterns, and the 99.99% share of simple sweeps.

**Open**: whether it halts. The Lean theorem `¬ Halts` is not proved, and no `halts_iff` reduction is stated.

## Reproduce

```sh
holdouts/1RB0LF_0LC0RE_0RA1LD_1LB0LD_0RA1RC_1LA---/lean/check.sh
D=holdouts/1RB0LF_0LC0RE_0RA1LD_1LB0LD_0RA1RC_1LA---
python3 $D/py/gen_rules.py 3e5              # rewrites lean/Rules.lean (a few minutes)
python3 $D/py/gen_sweep.py                  # rewrites lean/Sweep.lean
gcc -O2 -o recp $D/c/recp.c && ./recp 4000000 3e8 1 100000 > r3e8.txt && python3 $D/py/check_macro.py r3e8.txt
python3 $D/py/run_macro.py 2e7 1e6          # the long macro run, about 40 minutes
python3 $D/py/random_check.py SEED 20000     # random block lists, one macro step each
```

## Layout

| path | what it is |
|---|---|
| `lean/Machine.lean`, `lean/Blank.lean` | the machine and bounded runs (generated) |
| `lean/Gadgets.lean`, `lean/Macro.lean` | the short sweep and the reach from blank tape |
| `lean/Rules.lean` | the 387 crossing rules of the macro machine (generated) |
| `lean/Seq.lean`, `lean/Sweep.lean` | sequence library; `carry_even` (generated) |
| `py/blockmm.py` | the block macro machine |
| `py/run_macro.py`, `py/check_macro.py` | long macro run; comparison with direct simulation |
| `py/gen_rules.py`, `py/gen_sweep.py`, `py/gen_gadgets.py` | Lean generators |
| `py/random_check.py`, `py/check_counter.py` | random-list test; the previous pass's counter check |
| `c/recp.c`, `c/rec18.c` | direct simulators printing records in P-notation / the old notation |

## For later

- **Soundness of composition in Lean.** Define the block lists and `reparse` in Lean, and prove that a macro step
  built from the `Rules.lean` lemmas yields `steps n` between consecutive records. Then the macro bound is
  kernel-level.
- **Invariant search at block level.** Find a property of reachable block lists, finer than the three patterns,
  that random halting lists violate and the macro step preserves. If the parities are the issue, a `halts_iff` to a
  Collatz-like statement on (X, Y, digits) may be the realistic target.
- **Speed.** A C port of `blockmm`, or an increment-at-a-time or phase-at-a-time acceleration via `carry_even`,
  would push the bound by many more phases.
