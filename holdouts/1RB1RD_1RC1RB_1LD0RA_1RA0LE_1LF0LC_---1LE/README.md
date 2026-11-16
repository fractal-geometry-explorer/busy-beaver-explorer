# 1RB1RD_1RC1RB_1LD0RA_1RA0LE_1LF0LC_---1LE

bbchallenge id 172044, one of the six-state holdouts (group G07).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RD |
| B | 1RC | 1RB |
| C | 1LD | 0RA |
| D | 1RA | 0LE |
| E | 1LF | 0LC |
| F | --- | 1LE |

## Result

**It halts.** Proved in Lean: `halts : HaltsFromBlank` in `lean/Halt.lean`. The proof is a run-length simulator
with closed-form jumps, proved correct for every configuration (kernel), and one evaluation of it from blank tape
to the halting transition by `native_decide` (so the theorem trusts Lean's compiler besides the kernel).
Also proved in Coq on busycoq's definitions, in `coq/`, together with the exact number of steps:
`steps_172044 : halts_in tm c0 (N.to_nat K) /\ forall n, halts_in tm c0 n -> n = N.to_nat K`. It uses the same
method with two more block rules and a step count in every lemma. Its evaluation is done by Coq's kernel virtual
machine (`vm_compute`), so that proof does not rest on a compiler.

The number of steps is

    853177647932005270554892218084645935472995035642746848454477793277027802995098762076895667304703808111420498351739937140047615589683

(about 8.53·10^131; bbchallenge count, the halting transition included), and the machine stops at the left end of a
tape of about 2.9·10^66 cells. The step count is **proved in Coq**: `steps_172044` says that the machine reaches its
halting configuration after exactly K = this number minus 1 steps, and at no other time. Being exact, it is also the
best possible lower and upper bound. Before the Coq proof it was a trusted computation, and it still agrees with
three exact simulators written separately in Python: `py/accel.py`, `py/odo.py` for the jumps, and `py/leansim.py`,
the twin of the Lean simulator. The Lean proof does not count steps.

## What it does

Look at the tape each time the head, in state A, steps onto a never-visited cell at the right end (a *visit*;
there are 9.6·10^65 of them). Written with counts of the word `011` (`n` stands for `(011)^n`; `py/canon.py`) the
tape is a list of counters with short words between them, for example at visit 59

    11 01 8 01 5 01 45 0 A>          = (011)^11 01 (011)^8 01 (011)^5 01 (011)^45 0, head in A on the blank cell

**The regular part: an odometer.** Most of the time the tape ends in a *zone*

    ... n_k s_k n_(k-1) s_(k-1) ... n_1 s_1 n_0 0 A>         each s_j is 11 (read as bit 0) or 01 (bit 1)

and one visit is a binary increment of the number written by the bits s_k ... s_1 (s_1 the lowest):

- the trailing 1 bits become 0 and the lowest 0 bit, s_i, becomes 1;
- n_i loses 1; every s_m that went from 1 to 0 moves one unit from n_(m-1) to n_m; n_0 gains 2;
- the visit takes 6(n_0 + ... + n_(i-1)) + 4i + 11 steps: the head walks left through i counters and back.

In the coordinates N_0 = n_0 - s_1, N_j = n_j + s_j - s_(j+1) this is simply: N_0 gains 2 at every visit, and
N_(j-1) loses 1 each time bit s_j is set. So counter j is a fuel tank that loses one unit every 2^j visits, and the
zone can run for a number of visits exponential in its length before a tank runs low. `accel.jump` applies any
number V of such visits at once, in closed form, and `accel.jump_steps` gives the exact number of steps they take.

**The irregular part.** When a tank runs low (a count of a few units), or when the bits overflow (all of s_k ... s_1
are 1 and the carry runs into whatever is left of the zone), the visit is not of this form: the words between the
counters become other short words (`11101`, `11101111`, `1101101101`, ...), counters merge or split, and after a
few visits a zone is back, usually with other counts. These visits follow no rule that we know in closed form; the
accelerator simply runs them on a run-length tape (`py/rl.py`; `lean/Sim.lean` in the proof). Over the whole run there are 116,906 of them, and
86,729 jumps between them.

**How it ends.** The zone grows until it is the whole tape. At visit 9.6·10^65 the tape is

    1 n_214 01 n_213 01 ... 01 n_1 01 n_0 0 A>        n_214 = 91562, n_213 = 6921, ..., n_0 about 2.5·10^65

with every bit 1: the carry walks through all 215 counters, reaches the single 1 at the left end, and the machine
reads a 0 in state F there (the last 2.9·10^66 steps are one walk across the tape).

The first counter of the list is the top tank: it loses a unit about once per overflow of the whole odometer. It ran
out four times, at about 10^5, 10^14, 10^39 and 10^66 visits. The first three times the word left over at the left
end (`1101111`, then `1101`, `111011011111`, `111`) turned back, overflow by overflow, into a regular left end with
the next counter (451, 1073, 1104) as the first. The fourth time the leftover was another word,
`11101101111101111`, and the following overflows ate it: `11101101111101`, `11101101101`, `1101101`,
`11111101111`, `11111101`, `11101111`, `11101`, `1111`, `1`, while the next counter was still 91,562. With the
single 1 left, the next carry fell off the tape.

The halting transition is F0, reached as E0 -> 1LF with a 0 to the left: in the end configuration
`F> 0 1 0 (100)^91561 1 0 1 1 0 (100)^6920 ...` the head has just written the 1 and stands on blank tape.

## The Lean proof

| file | what it proves | checked by |
|---|---|---|
| `lean/Zone.lean` | `visit`: the visit rule of a zone, for every number of counters, every count and every tape left of the zone (induction on the carry; the pieces are six fixed runs of 4 to 6 steps and the two shift rules D: 011 -> 100 leftwards, C: 100 -> 011 rightwards) | kernel |
| `lean/Jump.lean` | `jump`: V visits of a zone at once, in the coordinates N_j, for every V after which the bits have not overflowed and every N_j is still at least 2 (`addV_succ`: the closed form of V increments; `inc_physP`: the increment in N coordinates is the one on the tape) | kernel |
| `lean/Sim.lean` | `mstep_sound`: one step of a run-length simulator (a transition, a run crossed when one or two copies of its word are crossed in the same state, a copy unpacked) follows the machine; the head faces left or right and the leftward half is the mirror image of the rightward one (`steps_mir`) | kernel |
| `lean/Run.lean` | `run_sound`: if the simulator with jumps answers `true` within its fuel, the machine halts from the configuration it started on | kernel |
| `lean/Halt.lean` | `run_halts`: started on blank tape the simulator answers `true` within 10^8 rounds; `halts` | `native_decide` |

The simulator's choices (how it folds cells into runs, which crossings it tries, how it reads a zone off the tape
and how many visits it jumps) are not trusted: whatever it does is covered by `mstep_sound` and by the hypotheses of
`jump`, which it checks before every jump. The evaluation takes about 88.9 million rounds (68.6 million single
transitions, 13.4 million runs crossed, 6.7 million copies unpacked, 86,734 jumps) and about 6 minutes of CPU.
`py/leansim.py` is the same algorithm in Python with step counts.

## The Coq proof

`coq/M_1RB1RD_1RC1RB_1LD0RA_1RA0LE_1LF0LC_HHH1LE.v` proves `halts_172044 : halts tm c0` and the exact step count
`steps_172044` on the definitions of busycoq's BB6 branch (`TM.v`, `BB62.v`, `Individual62.v`). It uses no axioms
(`Print Assumptions`: closed under the global context). It is a port of the Lean proof (the visit rule, the closed-form jump, a run-length simulator
proved sound, one evaluation from blank tape), with one speed-up: two **block rules** that take a whole counter
level in one round. In the overflow visits, which are 99% of the Lean simulator's rounds, the head walks left in
state D across `1 0 (011)^k 1` and comes back in state C across `(100)^m 1 0 1 1 0`; the rules

    D leftwards:  1 0 (011)^k 1 Y   ->  1 Y, with (100)^(k-1) 1 0 1 1 0 behind     (5 + 3(k-1) steps)
    C rightwards: (100)^m 1 0 1 1 0 ->  1 1 (011)^(m+1) behind                       (5 + 3m steps)

are proved for every k, m and tape, and bring the run from 88.9 to 19.0 million rounds.

Every lemma also states its exact number of steps (busycoq's `multistep`). The jump's steps are a closed form, a sum
over the odometer's levels proved by induction on V. The run carries its count and ends with
`run 2^25 start = RHalt K`.

The evaluation is `vm_compute`, checked by Coq's kernel. It takes about 8.5 minutes. A version without step counts
(busycoq fork, commit 594cece, submitted upstream as busycoq PR #76) takes 160 seconds; Lean's compiled run takes about 6 minutes. `py/coqsim.py` is the
same algorithm in Python with step counts. See `coq/README.md`.

## How the step count was obtained and checked

`py/accel.py` alternates jumps (the closed form above, only when every count stays above a margin and the bits do not
overflow) with single visits run by `py/rl.py`, an exact run-length simulator with unbounded integers: each of its
macro steps is one transition of the machine, or a run of a word crossed by a shift rule that it derives from the
table on the spot. The whole run takes about 2.5 minutes. `py/check.py` checks:

1. `rl.py` against the cell-level reference simulator `tools/py/bbtools/machine.py`: step count and whole tape at
   each of the first 3,000 visits (1.2·10^7 steps); and `c/visits.c` (the plain C simulator) gives the same step
   count and number of 1s at each of the first 20,000 visits.
2. the visit rule of a zone, step count included, against the cell-level simulator on 6,000 random zones with a
   random tape to their left and counts down to the smallest the accelerator jumps over;
3. the closed forms `jump` and `jump_steps` against `py/odo.py`, an independent evaluation that composes single
   visits by doubling, and against single visits, on 17,000 random zones;
4. the accelerated run against `rl.py` alone, visit by visit, up to visit 429,738 (2·10^11 steps);
5. in the run to the halt, every one of the 86,729 jumps against `odo.py`.

Also: the accelerated run agrees with `c/tok.c` (a run-length simulator in C written in an earlier pass) at 57
checkpoints up to step 10^15, and `py/leansim.py` (another simulator core, other jump lengths: 86,734 jumps) ends at
the same step count.

## Status

- **Coq, kernel (`vm_compute`):** the machine halts from blank tape after exactly K steps, K + 1 with the halting
  transition (`halts_172044`, `steps_172044`, `coq/`).
- **Lean, `native_decide`:** the machine halts from blank tape (`halts`, `lean/Halt.lean`).
- **Lean, kernel:** the visit rule for every zone (`visit`), V visits at once (`jump`), the soundness of the
  simulator (`mstep_sound`, `run_sound`); `lean/Blank.lean` (the halting configurations; no halt in 10^4 steps).
- **Trusted computation:** the description of the run above. The exact number of steps is now proved, and the three
  Python simulators agree with it.
- **Not known:** a closed rule for the irregular visits (they are simulated, in Lean too), and so any reason for
  the halt shorter than the run itself.

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RD_1RC1RB_1LD0RA_1RA0LE_1LF0LC_---1LE/lean/check.sh    # 10 minutes; prints the axioms
sh holdouts/1RB1RD_1RC1RB_1LD0RA_1RA0LE_1LF0LC_---1LE/coq/build.sh /path/to/busycoq   # Coq 8.18, busycoq's BB6 branch; 9 min
python3 holdouts/1RB1RD_1RC1RB_1LD0RA_1RA0LE_1LF0LC_---1LE/py/coqsim.py        # the Coq simulator's twin, 1 min
python3 holdouts/1RB1RD_1RC1RB_1LD0RA_1RA0LE_1LF0LC_---1LE/py/accel.py         # the run to the halt with step count, 2.5 min
python3 holdouts/1RB1RD_1RC1RB_1LD0RA_1RA0LE_1LF0LC_---1LE/py/leansim.py       # the Lean simulator's twin, 3 min
python3 holdouts/1RB1RD_1RC1RB_1LD0RA_1RA0LE_1LF0LC_---1LE/py/check.py quick   # checks 1-4, 15 s
python3 holdouts/1RB1RD_1RC1RB_1LD0RA_1RA0LE_1LF0LC_---1LE/py/check.py full    # all five, 5 min
(cd holdouts/1RB1RD_1RC1RB_1LD0RA_1RA0LE_1LF0LC_---1LE/c && gcc -O2 -o /tmp/visits visits.c && /tmp/visits 1RB1RD_1RC1RB_1LD0RA_1RA0LE_1LF0LC_---1LE 20000)
```

## Pages

- [`pages/holdouts/1RB1RD_1RC1RB_1LD0RA_1RA0LE_1LF0LC_---1LE/explainer.html`](../../pages/holdouts/1RB1RD_1RC1RB_1LD0RA_1RA0LE_1LF0LC_---1LE/explainer.html)
- [`pages/holdouts/1RB1RD_1RC1RB_1LD0RA_1RA0LE_1LF0LC_---1LE/proof-status.html`](../../pages/holdouts/1RB1RD_1RC1RB_1LD0RA_1RA0LE_1LF0LC_---1LE/proof-status.html)

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0LC_1LC0RE_1LD1LB_1LA1LD_1RF0RA_---1RE`](../1RB0LC_1LC0RE_1LD1LB_1LA1LD_1RF0RA_---1RE/README.md): rename A→C, B→D, C→A, D→B, E→E, F→F and exchange left and right; it is this table started in state C, in a mirror

<!-- end of related machines -->
