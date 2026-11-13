# 1RB1RE_1LC0RF_1LA0LD_1LE1LC_0RA0LC_1RA---

bbchallenge id 175626. One of the six-state holdouts whose halting from blank tape is open.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RE |
| B | 1LC | 0RF |
| C | 1LA | 0LD |
| D | 1LE | 1LC |
| E | 0RA | 0LC |
| F | 1RA | --- |

## What it does: a base-4 counter whose digits carry timers

Look at the tape each time the head is at the left end in state C (the start of a *sweep*). It is made of the word
`a = 001` and four separators, one per base-4 digit:

    C> a^n0  s(d1) a^n1  s(d2) a^n2  ...  s(dk) a^nk  01        s(0) = 0, s(1) = 011, s(2) = 00, s(3) = 0101

For example, from blank tape (steps on the left, `a5` is `a^5`):

    447   a5  0    a3 011 a3 01        digits 0 1 (lowest first)
    493   a6  011  a2 011 a3 01        1 1
    547   a7  00   a2 011 a3 01        2 1
    609   a8  0101 a1 011 a3 01        3 1
    697   a9  0    a2 00  a3 01        0 2   (carry)
    775   a10 011  a1 00  a3 01        1 2

**One sweep adds one to the base-4 number** V = d1 + 4 d2 + 16 d3 + ... . The head runs right over `a^n0` (each `001`
becomes `110` in state F), over every separator `0101` (a digit 3) and the block after it, to the first digit below 3,
turns there and runs back, restoring the `a`s. The digits 3 it crossed become 0 and the digit where it turned goes up
by one. The blocks change too: each block left of the turning digit gains one `a`, and the block right of it loses one
when that digit goes 0 → 1 or 2 → 3. The sweep takes 8 (n0 + ... + nj) + 10 j + 6 steps when it carries through j
digits. This is proved in Lean for every value of the blocks and any number of carries (`lean/Rules.lean`).

So the leftmost block n0 grows by one every sweep, and for every other digit the number N_i = n_i + c(d_i)
(c = 0, 1, 1, 2 for d = 0, 1, 2, 3) stays fixed except that it drops by one each time digit i wraps from 3 to 0, that
is every 4^i sweeps: every digit carries a **timer** that counts its own wraps down. Two things are not covered by the
sweep rule, and they make up the long-term behaviour:

* **Overflow.** When every digit is 3 the carry runs into the end `01`. The head then crosses the whole tape and
  comes back, every digit becomes 0, and a new lowest digit appears: its block is the old `a^n0`, so its timer
  starts at n0 = 4^k (k the number of digits); n0 starts again from 2. The tape grows by one digit.
* **A timer runs out.** When a block reaches 0 the separators on its two sides touch (`0101011`, `01100`, `0000`,
  `010`, `010100`, `0110101`, `01101` ...); within the next few cycles of the lower digit the two digits fuse into one
  and the counter loses a digit. For example (steps, tape):

      5622078  a112 0101 a999 0101 a123 00 a1 011 a50 0 a3 01
      5631976  a113 0    a1000 0   a124 0101011  a50 0 a3 01     the block a1 has run out
      5680420  a129 0    a996 0    a123 0 a1 00  a50 0 a3 01
      5730766  a145 0    a992 0    a122 01100    a50 0 a3 01
      5783024  a161 0    a988 0    a121 0000     a50 0 a3 01
      5837194  a177 0    a984 0    a120 010      a50 0 a3 01
      5890707  1010 a192 0 a980 0  a119 011      a49 0 a3 01     two digits have become one

  The block just before the end `01` loses one `a` at every overflow and is replaced the same way when it runs out.

A new digit gets the timer 4^k but wraps 4^k times in the next cycle alone, so most new digits fuse with their
neighbour soon after they are made; the number of digits still grows, slowly: about 0.83 digits per factor 10 in the
step count (248 digits after 10^300 steps). That is the exp/sqrt shape. Each sweep costs about 8 n0 steps and adds
three cells at the left end, so the tape grows to the left like the square root of the step count. The cells right of
the start hold the highest digits and the end `01`, which change only at overflows and merges, every 4^k sweeps: that
side grows like the logarithm.

## Does it halt?

Open, and **it cannot be settled by the shape of the tape alone**: tapes of exactly the counter form above, with
other block lengths, do halt. For example (both proved in Lean by evaluation, `lean/Perturbed.lean`; the step
counts agree between the exact accelerated simulator and a plain C simulator):

    C> a^2  0 a^4 01                    one digit (0), block 4              halts at step   309,457
    C> a^43 0101 a^4 0101 a^4 01        two digits (3, 3), blocks 4 and 4   halts at step 4,905,443

So any nonhalting proof has to use the particular values the timers take in the run from blank tape. A brute-force
search over all tapes with one or two digits, blocks 1..4 and n0 = 2..12 finds 136 that halt within 10^7 steps; of
300 random tapes with 2..7 digits and the block after digit i up to 4^(i+2) (the range seen in the actual run),
22 halt within 10^150 steps (`py/perturb.py random 7 300 150`).

**How a halt happens.** The only halting transition is F1, and F is entered only from B1. In a normal sweep F only
ever reads the 0s of `001` (proved). In the halting examples several timers run out close together: two digits fuse
while the blocks below them are short too, the fused patterns run into each other (`0110`, `000`, `01101101`,
`011011101`, ...) and the counter collapses until the end `01` is eaten (from `C> a^2 0 a^4 01` the end becomes
`010101`, `011011`, `0111`, `01111`, ... and finally `11`, where B reads a 1 and F the next one). In the run from
blank tape that never happens: up to 10^300 steps there is never more than one irregular pattern inside the counter
at a time (3,008 simulated sweeps with one, 2,405 with none, the rest at the left end or the end `01`).

**How far it has been checked.** The accelerated simulator `py/accel.py` runs the sweep rule in closed form between
irregular events (t sweeps at once: V += t, each timer minus the number of wraps of its digit, the step count summed
exactly) and simulates every irregular sweep with an exact run-length simulator. It reaches **10^2000 steps** from
blank tape without a halt; in all that time only about twenty different irregular separator patterns occur
(`python3 py/accel.py run 1e300` prints the catalogue), each over and over.

**Heuristic.** The random tapes above halt at steps with 6 to 25 digits (20 of the 22), then once near 10^52 and once
near 10^89: the rate of halting falls off as the timers get longer (a fusion is only dangerous when other timers run
out in the same short window, and with timers of size about 4^i such windows get rarer). This is the shape of a
cryptid: the run from blank tape is past the dangerous early stage, and that it keeps surviving is likely but not
forced by anything known.

## For later

Stopped at (second pass): the counter and timer structure, the sweep rules in Lean, the accelerated run to
10^2000 steps, and the observation that the same tape shape halts with other timers (`lean/Perturbed.lean`). A
proof therefore needs an *arithmetic* invariant of the timers along the actual run, not a closed family of
patterns. Next: (1) write the fusion and overflow events as symbolic rules (a pair of digits with an empty block
between them, for each pair of digit values; the overflow with a short last block), so that the whole run becomes a
map on the list (V, N_1, ..., N_k) and `accel.py` can run without simulating any sweep; (2) find what the timers
satisfy right after each overflow (n0 = 4^k at the new digit's birth; the others look irregular: at sweep 41,168
they are 16384, 2884, 975, 2712, 3752, 678, 44, 31) and whether some inequality between neighbouring timers keeps
two fusions from overlapping; (3) measure along the run how close two timers come to running out in the same window
(a crude margin, min over lower digits j of n_j 4^j / 4^i at a fusion of digit i, has gone down to 0.15, at a
fusion of digit 10 near 10^13 steps, without trouble; a sharper measure is needed).

## Files

- `lean/Rules.lean` (generated by `py/rules.py`): `step0`..`step2`, one sweep without carry with its exact step count;
  `sweep0`..`sweep2`, one sweep with any list of carried digits (by induction on the list, `lean/Seq.lean`).
- `py/accel.py`: the accelerated simulator (`run`, `check` against the plain simulator, `fuzz`); `py/rlsim.py` the
  run-length simulator it uses. The sweep rule and the closed-form bulk were also compared with `tools/c/tmrun.c` at
  every sweep start up to 3·10^8 steps.
- `lean/Perturbed.lean`: `counter_2_0_halts`, `counter_43_33_halts`: two counter tapes with short timers that halt
  (`native_decide` on the list simulator), and `halts_of_eval`, the bridge from a bounded evaluation to `Halts`.
- `py/perturb.py`: the search for halting counter tapes (`small`: all short ones; `random`: random timers, run with
  the accelerated simulator).

## Status

Open. Lean (`lean/Blank.lean`): the halting configurations (`step_none_iff`), no halt in 10,000 steps by
the kernel, in 10,000,000 by `native_decide`. Lean (`lean/Rules.lean`, kernel): the sweep rules. C
(`tools/c/triage.c`): no halt in 1,000,000,000 steps. Python (`py/accel.py`): no halt in 10^2000 steps. Lean (`lean/Perturbed.lean`, `native_decide`): two
tapes of the counter form with short timers halt, so the tape shape alone does not decide the question.

## Pages

- [`pages/holdouts/1RB1RE_1LC0RF_1LA0LD_1LE1LC_0RA0LC_1RA---/explainer.html`](../../pages/holdouts/1RB1RE_1LC0RF_1LA0LD_1LE1LC_0RA0LC_1RA---/explainer.html)
- [`pages/holdouts/1RB1RE_1LC0RF_1LA0LD_1LE1LC_0RA0LC_1RA---/proof-status.html`](../../pages/holdouts/1RB1RE_1LC0RF_1LA0LD_1LE1LC_0RA0LC_1RA---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RE_1LC0RF_1LA0LD_1LE1LC_0RA0LC_1RA---/lean/check.sh
python3 holdouts/1RB1RE_1LC0RF_1LA0LD_1LE1LC_0RA0LC_1RA---/py/accel.py check 3e6
python3 holdouts/1RB1RE_1LC0RF_1LA0LD_1LE1LC_0RA0LC_1RA---/py/accel.py run 1e300
python3 holdouts/1RB1RE_1LC0RF_1LA0LD_1LE1LC_0RA0LC_1RA---/py/perturb.py random 7 300 150   # about 10 minutes
```
