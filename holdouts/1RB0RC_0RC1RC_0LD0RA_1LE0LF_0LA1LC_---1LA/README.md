# 1RB0RC_0RC1RC_0LD0RA_1LE0LF_0LA1LC_---1LA

bbchallenge id 65826. **It does not halt: Lean theorem `nonhalt` (`lean/Replay.lean`), level native** (the kernel
plus two long computations and twelve short ones evaluated by `native_decide`). From step 1,818,198,163,340,705 on, the run is a *growth cycle*: the
configuration

    C(r) = E> 0 (1011001)^59 1011 00000 1101100110110 (011)^16 001101100110 (011)^r        (rest of the tape blank)

comes back as C(r + 321,042,928) after 116,320,154 arrivals at the left end, for **every odd r >= 65**, in
650,373,336,347,246,654 + 4,382,930,856 (r - 65) steps. The run from blank tape reaches C(16,797,709). The set
{C(r) : r odd, r >= 65} is closed and contains no halting configuration.

What rests on what:

* "the cycle and the arrival imply that the machine never halts": Lean, kernel (`lean/Cycle.lean`);
* a symbolic executor (blocks with counts `c + a x`, shift rules, re-bracketing, cycle rules applied N times) and its
  soundness theorem `run_sound`: Lean, kernel (`lean/Exec.lean`); its 31 shift rules: kernel (`lean/ExecData.lean`);
* the cycle (`grow_cyc`: C(65 + 2x) reaches C(65 + 2(x + 160,521,464)) for every x) and the arrival (`reach_cyc`: blank
  tape reaches C(16,797,709)): two runs of that executor, 5.6 and 5.0 million moves, and one run for each of its twelve
  cycle rules, evaluated by `native_decide` (`lean/Period.lean`, `lean/Arrive.lean`, `lean/ExecData.lean`);
* the numbers of steps and events quoted here: computed by `py/closure/accel.py`, `py/replay/engine.py` and
  `verify/sim3.cpp`, which agree; trusted code, not part of the Lean statement.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RC |
| B | 0RC | 1RC |
| C | 0LD | 0RA |
| D | 1LE | 0LF |
| E | 0LA | 1LC |
| F | --- | 1LA |

## The tape as words

Everything is read at an *event*: state E arrives at the left end of the visited tape. The tape is then a left block
of seven-cell words `(1011001)^p`, a short irregular zone, and blocks of three-cell words `(011)^n` separated by
`0`, `000` and a few other short separators. The last block, `(011)^r`, ends the tape. Going right the head shifts a
block of three-cell words by one cell (3 steps a word); going left it crosses two words at a time (18 steps), so
**only the parity of a block's length matters** to what happens at its ends. Every cycle rule the simulator needed
has modulus 2.

## Three phases

| phase | tape at an event | one cycle | Lean |
|---|---|---|---|
| collect | `0 (1011001)^p (101)^5 10 (011)^q 000 (011)^r`, q even, r odd | 2 events: p + 2, q - 2 | `collect2`, `collect_n` |
| expand | `0 (1011001)^p 1011 0^5 110110011010 (101)^m 1000 (011)^r`, m even, r odd | 4 events: p - 2, m + 14 | `expand4`, `expand_n` |
| drain | `0 (1011001)^p 1011 0^5 1101100110110 (011)^16 001101100110 (011)^r`, r odd | 72 events: p - 52, r + 414 | `rule8_ok` (native) |

Collect and expand alternate, so the left block is rebuilt about 7 times longer each time (about 600, 4,370, 30,750,
215,000, 1,506,000 words). Between them come short irregular stretches (a few hundred to a few thousand events)
in which separators collide, trains of cars `(011)^4 0` are built and taken apart, and `r` grows a little
(95, 209, 1,111, 1,421, 2,643). After some rounds the irregular stretch ends in the *drain* pattern instead: the
whole left block is poured into the last block, 414 words of three for 52 words of seven, and the left part starts
again from a small state in front of a much larger `r`.

## The growth cycle

The left part never looks at `r` beyond its parity, and the drains add even amounts, so `r` stays odd. After the
second drain the left part is in a state it comes back to exactly:

| event | step | what |
|---|---|---|
| 2,260,329 | 6.7e13 | first drain: p 1,505,827 -> 115, r 4,001 -> 11,991,785 |
| 5,251,395 | 1.07e15 | second drain: p 603,155 -> 111, r -> 16,797,295 |
| 6,086,451 | 1.818e15 | **C(16,797,709)**, first time |
| 59,675,352 | 5.4e16 | drain after 11 phases: p 35,724,983 -> 99, r -> 301,226,589 |
| 116,039,645 | 6.0e17 | drain after 10 phases: p 4,598,419 -> 111, r -> 337,840,223 |
| 122,406,605 | 7.26e17 | **C(337,840,637)** = C(16,797,709 + 321,042,928) |

One period is two epochs (two drains). `py/closure/cycle.py check` proves the period with `r = 65 + 2x`, x a free
variable: 5.4 million moves of the word-level engine, 24 jumps over long phases by 13 cycle rules (each proved by its
own symbolic run for all values of its counts, and re-checked on numbers), and no question about x that the
constant part of a count does not answer.

### Why this is a proof, and of what kind

1. *Word level.* A shift rule `u q> w -> v u q>` is found by running the machine on the cells of `u w` alone; if the
   head leaves them only on the far side, in the same state, the same happens to every further copy of `w`.
2. *Counts with variables.* A count is a number or `c + a x`. Comparing, halving and decrementing such a count is
   done only when the answer is the same for every x >= 0; otherwise the run stops (`Undecided`). No threshold is
   guessed: the domain of every statement is its start configuration with x >= 0.
3. *Cycle rules.* A rule "this shape with counts `b_i + 2 x_i` comes back with counts `b_i + D_i + 2 x_i`" is the
   result of one such run. It is applied N times at once only where its precondition holds at every one of the N
   applications (the smallest count is checked), and to a count with a variable only if the precondition holds
   for every x and the rule does not shrink that count.
4. *Closure.* The run from C(65 + 2x) returns to C(65 + 321,042,928 + 2x), and 321,042,928 is even: the family is
   mapped into itself. No halting transition occurs on the way.

This Python code is not verified; the Lean replay below does not use it (it has its own engine and proves every move).
Evidence that the Python simulator, which supplies the step and event counts, is right: the word-level engine agrees with a
plain C simulator at all 24,646 events of the first 10^10 steps (step count and CRC of the tape,
`py/closure/check_events.py`); the step polynomial agrees with three consecutive periods of the numeric run and
with numeric runs from C(65), C(67), C(79); 17 injected defects (in the claim, in the rules, in the machine) are all
reported (`cycle.py mutate`).

### Classes next to it do halt

The same node with other counts is not safe, so no "all sizes" domain could have been closed:

* `E> 0 (1011001)^61 1011 0^5 1101100110110 (011)^16 001101100110 (011)^r`, r odd >= 65, **halts** after
  1,772,276 + 5,220 (r - 65) steps (confirmed by plain simulation for r = 65, 67, 71);
* C(r) with **r even** >= 64 halts, at event 21,362,421.

The real run avoids them because it sits on the one orbit above. This is why bbchallenge's regular-language
deciders fail here.

## Lean (`lean/`)

| file | level | content |
|---|---|---|
| `Rules.lean` (generated by `py/rules.py`) | kernel | three sweeps; `collect_raw`, `expand_raw`: one cycle of each long phase, for all p, a, b |
| `Phases.lean` | kernel | `collect2`, `expand4` in start form; `collect_n`, `expand_n`: n cycles by induction |
| `Cycle.lean` | kernel | `nonhalting_of_growth_cycle`: if blank tape reaches some C(65 + 2x) and every C(65 + 2x) reaches C(65 + 2(x + 160,521,464)) in at least one step, the machine does not halt from blank tape |
| `Exec.lean` | kernel | the symbolic executor and `run_sound`: whatever it does in k moves, the machine does, for every value of the variables; `run_pos` (at least one step); `rule_instN` (a cycle rule N times, by induction); `ruleOK_of_run` |
| `ExecData.lean` (generated by `py/replay/gen.py`) | kernel, native | 13 + 18 shift rules, each by `rfl` (`shRTbl_ok`, `shLTbl_ok`); 12 cycle rules, each one executor run by `native_decide` (`rule0_ok` ... `rule11_ok`); the tables `T`, `T_ok` |
| `Arrive.lean` (generated) | native | `arrive_run`: 5,037,044 moves from blank tape end at C(16,797,709) |
| `Period.lean` (generated) | native | `period_run`: 5,581,714 moves from C(65 + 2x), x free, end at C(321,042,993 + 2x) |
| `Replay.lean` | native | `reach_cyc`, `grow_cyc`, and **`nonhalt : ¬ HaltsFromBlank`** |

`lean/check.sh` takes about 1 minute (the two long runs 13 s each). `#print axioms nonhalt`: `propext`, `Quot.sound`
and the 14 `native_decide` evaluations.

### The executor

A configuration is two token lists (nearest cell first on each side) and a state; a token is a cell or a block, a word
repeated `c + a_0 x_0 + a_1 x_1 + ...` times. `den rho S` is the machine configuration it stands for when
`x_i = rho i`. One move is

* a *shift rule* from a table: in state q, with a word u carried, k = 1 or 2 copies of a block's word are crossed and
  leave a word v; the block's count n is divided, n = k m + rem, which must be possible for every value of the
  variables. A rule is valid when it is a statement about the machine for all surrounding tapes (proved by `rfl`),
  and `TM.cross_r` / `TM.cross_l` give the whole block;
* otherwise one machine step; a block is opened only if its count is surely at least 1;
* and when state E arrives at the left end, the right side is re-bracketed (`norm`: rotate a block to the left past
  a cell, absorb copies, merge, write out blocks of fewer than three copies, form blocks from four or more equal
  words; every case is proved to keep the cells) and a table of *cycle rules* is tried.

A cycle rule is a template of the whole tape whose counts are `b0_i + 2 x_i` before and `b1_i + 2 x_i` after. Its
validity for all `x_i` is one run of the executor itself, without cycle rules, from the template before to the
template after (`ruleOK_of_run`). It is applied N times at once: N is the largest number for which the shrinking
counts stay above their bases; the check and the induction over N are in Lean (`appToks`, `rule_instN`), so the
choice of N is not trusted. The same holds for the whole strategy (which rule, how to re-bracket): only soundness
is proved, and the final states are compared by evaluation.

`py/replay/engine.py` is the Python model of the executor, move for move; `py/replay/gen.py` runs it twice: once
finding the shift rules and cycle rules on the way, once with the tables fixed (what Lean replays), and writes the
generated Lean files. Its events and step counts equal those of `py/closure/accel.py` (116,320,154 events and
650,373,336,347,246,654 + 8,765,861,712 x steps for the period; event 6,086,451, step 1,818,198,163,340,705 for
the arrival).

What Lean does not state: the number of steps or events of the period and of the arrival (only "reaches, in at
least one step"). The kernel alone can check the short cycle rules (`decide +kernel`; tried on rule 4, 422 moves,
1 s, and rule 11, 3,255 moves, 4 s), but the drain rule (201,007 moves) in one piece ran out of memory, and so would
the two long runs; cutting them at a few thousand checkpoints would take hours of kernel time and has not been done.

## Independent check

`verify/` holds a second accelerated simulator written from scratch (`sim3.cpp`), not derived from `py/closure/`. It
reproduces the arrival C(16,797,709) at step 1,818,198,163,340,705 exactly, and one full period at the predicted step
for r = 65, 67, ..., 85 and r = 16,797,709; even r halt (the halting transition is one step after the count given in
the notes). It checks listed values only; "for every odd r" is the Lean theorem `grow_cyc`. See
`verify/README.md`.

## Status

Decision in the ledger: **nonhalting** (`nonhalt`, level native). Kernel: the executor's soundness, the shift rules,
the implication, the two long phases by hand, halting configurations, 10,000 steps. Native: the twelve cycle rules,
the arrival, the period, 10^7 steps. Trusted: the step and event counts.

## First look

Growth class **sqrt/sqrt** (left: sqrt, exponent 0.498; right: sqrt,
exponent 0.478). After 1,000,000,000 steps: 43,491 cells visited (12,594 left of the
start, 17,410 right), 26,502 ones.

- left, step 971,976,277: `E>0 1 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 `
- left, step 987,704,249: `E>0 1 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 `
- right, step 972,322,623: `1 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 `
- right, step 988,040,901: `1 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 1^2 0 1^2 0^2 `

## Pages

- [`pages/holdouts/1RB0RC_0RC1RC_0LD0RA_1LE0LF_0LA1LC_---1LA/explainer.html`](../../pages/holdouts/1RB0RC_0RC1RC_0LD0RA_1LE0LF_0LA1LC_---1LA/explainer.html)
- [`pages/holdouts/1RB0RC_0RC1RC_0LD0RA_1LE0LF_0LA1LC_---1LA/proof-status.html`](../../pages/holdouts/1RB0RC_0RC1RC_0LD0RA_1LE0LF_0LA1LC_---1LA/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RC_0RC1RC_0LD0RA_1LE0LF_0LA1LC_---1LA/lean/check.sh      # all Lean files, 1 min
python3 holdouts/1RB0RC_0RC1RC_0LD0RA_1LE0LF_0LA1LC_---1LA/py/replay/gen.py --check   # model of the Lean executor; without --check rewrites ExecData, Arrive, Period (40 s)
python3 holdouts/1RB0RC_0RC1RC_0LD0RA_1LE0LF_0LA1LC_---1LA/py/closure/cycle.py check      # the cycle, from the claim alone (20 s)
python3 holdouts/1RB0RC_0RC1RC_0LD0RA_1LE0LF_0LA1LC_---1LA/py/closure/cycle.py reach      # blank tape reaches C(16797709) (5 s)
python3 holdouts/1RB0RC_0RC1RC_0LD0RA_1LE0LF_0LA1LC_---1LA/py/closure/cycle.py instance   # numeric runs from C(65), C(67), C(79) (40 s)
python3 holdouts/1RB0RC_0RC1RC_0LD0RA_1LE0LF_0LA1LC_---1LA/py/closure/cycle.py mutate     # 17 defects, all must be reported (6 min)
python3 holdouts/1RB0RC_0RC1RC_0LD0RA_1LE0LF_0LA1LC_---1LA/py/closure/classes.py          # neighbouring classes (4 min)
gcc -O2 -o events holdouts/1RB0RC_0RC1RC_0LD0RA_1LE0LF_0LA1LC_---1LA/c/events.c && ./events 1RB0RC_0RC1RC_0LD0RA_1LE0LF_0LA1LC_---1LA 10000000000 > ev10.txt   # 90 s
python3 holdouts/1RB0RC_0RC1RC_0LD0RA_1LE0LF_0LA1LC_---1LA/py/closure/check_events.py ev10.txt --plain     # word-level engine against it (15 s)
python3 holdouts/1RB0RC_0RC1RC_0LD0RA_1LE0LF_0LA1LC_---1LA/py/closure/accel.py prove      # finds the cycle without being told (15 s)
python3 holdouts/1RB0RC_0RC1RC_0LD0RA_1LE0LF_0LA1LC_---1LA/py/rules.py > holdouts/1RB0RC_0RC1RC_0LD0RA_1LE0LF_0LA1LC_---1LA/lean/Rules.lean
```

## Coq (busycoq) proof

`coq/` holds a second, independent-kernel proof of the same statement on top of [busycoq](https://github.com/meithecatte/busycoq): `nonhalt : ~ halts tm c0` in `coq/H65826.v`, no axioms (`Print Assumptions` says closed under the global context), all runs evaluated by `vm_compute`. Build: `sh coq/build_H65826.sh /path/to/busycoq` (Coq 8.18.0, about 40 s). Details: [coq/README.md](coq/README.md).
