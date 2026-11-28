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

## Long accelerated run (16 November 2026)

**No halt in 10^7387 steps** (trusted computation; the old run stopped at 10^2000). Nothing stalled in `accel.py`: it
was slow, because it re-tokenised and re-parsed the whole tape at every event (about 80% of the time), O(digits) per
event. `py/accel2.py` applies the same rules locally:

* the tape is a list of chunks (separator, block length); a bulk touches only the digits below the highest digit
  that changes, and the next bulk end is taken from a heap of the times Vb_i at which block i would drop below 1
  (Vb_i does not change during bulks: when digit i wraps, V // 4^(i+1) goes up by one and N_i down by one);
* a simulated sweep runs `rlsim` on a window of chunks only (up to the first digit below 3 plus guard chunks), and is
  redone on a larger window when the head gets near the window's edge, so it is still the exact sweep;
* the overflow (every digit 3, then the end `01`) is done in closed form:
  `C> a^n0 (0101 a^n_i)_i 01` becomes `C> 1010 a^n0 (0 a^(n_i+1))_i 01` in 6 n0 + 6 (n_1 + ... + n_k) + 10 k + 15
  steps. This was checked against `rlsim` at every overflow of the compared stretch and on 300 random counters
  (`accel2.py overtest 300`).

`python3 py/accel2.py compare 1e700` gives the same tape, step count and sweep count as `accel.py` at every
simulated sweep up to 10^700 steps. The new run reaches 10^2000 in about 50 s; the old one took about 10 minutes.

From blank tape (`python3 py/accel2.py run 1e30000 CKPT`, checkpointed) the run reached 10^4403 steps in about
10 minutes. It was then stopped and resumed from its checkpoint, and after about 55 more minutes it reached
**10^7387 steps** with no halt. At that point it had done 10^3693 sweeps, the counter had 6,135 digits, and the run
had done 97,330 bulks, 138,314 simulated sweeps and 21,566 overflows. Every irregular sweep is still one of the few
patterns of the catalogue. It is simply still running: no event the rules do not cover has occurred. The run is
CPU-bound (about 100 decades of steps every 2 to 3 minutes at the end, slowing as the number of digits grows) and
can be resumed from its checkpoint.

## Lazy-timer run to 10^70169 steps (24 November 2026)

**No halt in 10^70169 steps** from blank tape (trusted computation; the run of 16 November stopped at 10^7387).
`py/accel2.py` still did O(number of digits) Python work at almost every event: its bulk visited every digit below
the highest one that changes, and nearly every simulated sweep ended in a full recompute of the counter. But the
irregular patterns sit at the bottom of the counter (in a run to 10^800, 95% of the irregular chunks are among the
lowest 10% of the digits, most of them in chunks 1 to 5), and the long upper part only counts. `py/accel3.py`
splits the tape there:

* **L**, the low part: chunk 0 and the concrete chunks up to the topmost irregular one, run exactly as in
  `accel2.py` (bulk of its normal prefix, simulated sweeps on a window with `rlsim`). It is a handful of chunks.
* **U**, the upper part: normal digits only, kept lazily. Index the digits from the top (j = 0 is the highest),
  let K be their number, V their value and E the number of overflows. Then digit j is `(V >> 2(K-1-j)) & 3` and
  its timer is

      N_j = A_j - 4^j E - floor(V / 4^(K-j))

  with a constant A_j: between overflows digit j wraps whenever V crosses a multiple of 4^(K-j), and each overflow
  (V: 4^K - 1 to 0) wraps every digit once, so a digit wraps exactly 4^j times per overflow cycle *whatever K is*.
  Adding or removing a lowest digit (V to 4V + d, or V >> 2) leaves the floor term of every other digit unchanged,
  so A_j is never touched while the digit stays in U. Block j runs out at the moment E + V/4^K =
  (4(A_j - 2) + 3)/4^(j+1) (or (4(A_j - 1) + 1)/4^(j+1) when N_j = 1), a constant kept in a heap.
* **Steps.** w wraps of a digit whose timer was M cost 8Mw - 4w^2 - 2w steps (each wrap costs 8(N - 2) + 10). The
  run adds that when a digit leaves U and computes the pending part only when the step count is printed.

A bulk in U is then a few big-integer operations (V += t, n0 += t and the n0 part of the step count), the overflow is
the closed form of `accel2.py` with the sum of the blocks read off the sum of the A_j, and a run-out or a carry into
the irregular part moves the lowest few U digits into L and back.

Checks (all with exact equality of tape, step count and sweep count):

* `python3 py/accel3.py compare 1e3000`: the same as `accel2.py` at all 64,912 non-bulk sweeps up to 10^3000 steps;
* `python3 py/accel3.py randcheck 300 150`: 300 random counter tapes (2 to 7 digits, block i up to 4^(i+2), as in
  `perturb.py`), the same as `accel2.py` at every non-bulk sweep to 10^150 steps; 21 of them halt, each at the same
  step in both;
* `python3 py/accel3.py halttest`: the two tapes of `lean/Perturbed.lean` halt at the proved steps 309,457 and
  4,905,443.

Speed: 10^8000 steps in 139 s (`accel2.py` needed about 65 minutes for 10^7387), 10^50000 in about 2.5 hours.
From blank tape the run went to **10^70169 steps** in about 6 hours of one core, checkpointed and resumed from its checkpoint along the way.
There it had done 10^35084 sweeps; the counter had 58,272 digits; there had been 205,632 overflows and 1,315,273
simulated sweeps (about 19 per decade of steps, as before), and the digit count still grows by 0.83 per decade of
steps, the rate seen since 10^300. No halt, and no event the rules do not cover. What stops it now is memory, not
time: the timers of the low digits have about 2K bits each, so the state is about K^2 bits (the checkpoint at
58,272 digits is 1.8 GB and the process needs 7 to 11 GB). Going much further needs a large-memory machine or a
representation of the timers that is not stored digit by digit.

## Files

- `lean/Rules.lean` (generated by `py/rules.py`): `step0`..`step2`, one sweep without carry with its exact step count;
  `sweep0`..`sweep2`, one sweep with any list of carried digits (by induction on the list, `lean/Seq.lean`).
- `py/accel.py`: the accelerated simulator (`run`, `check` against the plain simulator, `fuzz`); `py/rlsim.py` the
  run-length simulator it uses. The sweep rule and the closed-form bulk were also compared with `tools/c/tmrun.c` at
  every sweep start up to 3·10^8 steps.
- `lean/Perturbed.lean`: `counter_2_0_halts`, `counter_43_33_halts`: two counter tapes with short timers that halt
  (`native_decide` on the list simulator), and `halts_of_eval`, the bridge from a bounded evaluation to `Halts`.
- `py/accel2.py`: the same accelerated run with local updates (chunked tape, windowed sweeps, closed-form overflow), checkpointed (`run 1eX CKPT`), with `compare` against `accel.py` and `overtest` against `rlsim`.
- `py/accel3.py`: the lazy-timer run (low part concrete, upper part as constants A_j with a heap of run-out times),
  checkpointed (`run 1eX CKPT`, exits to release memory when the process passes MAXRSS_MB and can be restarted
  from the checkpoint), with `compare` and `randcheck` against `accel2.py` and `halttest`.
- `py/perturb.py`: the search for halting counter tapes (`small`: all short ones; `random`: random timers, run with
  the accelerated simulator).

## Status

Open. Lean (`lean/Blank.lean`): the halting configurations (`step_none_iff`), no halt in 10,000 steps by
the kernel, in 10,000,000 by `native_decide`. Lean (`lean/Rules.lean`, kernel): the sweep rules. C
(`tools/c/triage.c`): no halt in 1,000,000,000 steps. Python (`py/accel.py`): no halt in 10^2000 steps; (`py/accel2.py`, same rules applied locally): no halt in 10^7387 steps; (`py/accel3.py`, lazy timers, checked against `accel2.py`): no halt in 10^70169 steps. Lean (`lean/Perturbed.lean`, `native_decide`): two
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
python3 holdouts/1RB1RE_1LC0RF_1LA0LD_1LE1LC_0RA0LC_1RA---/py/accel3.py halttest
python3 holdouts/1RB1RE_1LC0RF_1LA0LD_1LE1LC_0RA0LC_1RA---/py/accel3.py compare 1e3000      # about 35 minutes
python3 holdouts/1RB1RE_1LC0RF_1LA0LD_1LE1LC_0RA0LC_1RA---/py/accel3.py run 1e8000          # about 2 minutes
```
