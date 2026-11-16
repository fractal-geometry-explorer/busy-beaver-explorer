# busycoq proof: 1RB1RD_1RC1RB_1LD0RA_1RA0LE_1LF0LC_---1LE halts, after exactly K steps

bbchallenge id 172044, a BB(6) holdout. The final theorems are

```coq
Definition K : N := 853177647932005270554892218084645935472995035642746848454477793277027802995098762076895667304703808111420498351739937140047615589682.
Theorem halts_172044 : halts tm c0.
Theorem steps_172044 : halts_in tm c0 (N.to_nat K) /\ forall n, halts_in tm c0 n -> n = N.to_nat K.
```

(in `Module M172044`, file `M_1RB1RD_1RC1RB_1LD0RA_1RA0LE_1LF0LC_HHH1LE.v`). `TM`, `halts`, `halts_in`, `c0`
and the tape notations come from busycoq's `TM.v`, instantiated to 6 states and 2 symbols by `BB62.v` and
`Individual62.v` (busycoq's BB6 branch). `tm` is the machine above, read from its TNF string by `TM_from_str`.

`halts_in tm c0 n` says that the machine reaches a halting configuration after n steps. So the machine stops after
exactly K steps, and K + 1 = 853177647932005270554892218084645935472995035642746848454477793277027802995098762076895667304703808111420498351739937140047615589683
(about 8.53·10^131) counting the halting transition, which is the bbchallenge convention. This is the number that
`../py/accel.py` computes; it is now proved. Since the count is exact, it is also the best possible lower and
upper bound.

`Print Assumptions` prints `Closed under the global context` for both theorems: no axioms, no `Admitted`. The
proof is one file of 1,599 lines in the style of busycoq's own files for this kind of machine: rules proved by
stepping the machine, an accelerated simulator proved sound, and one evaluation by `vm_compute`.

It ports the Lean proof in `../lean` and adds two things:

- two block rules for whole counter levels, which make the run 4.7 times shorter;
- step counts in every lemma.

## The proof

Every lemma states its exact number of steps, as busycoq's `multistep` (`c -[ tm ]->> n / c'`).

1. **A run-length simulator for any machine** (section Sim).
   - A tape is two stacks of items: a cell, or a run `w^n` of a word. The head faces left or right, and the
     leftward half is the rightward half applied to busycoq's `flip` of the machine.
   - One round is one transition (1 step), a run crossed in one go, or a copy unpacked (0 steps). A run is crossed
     when a copy of its word (or two copies, or a copy entered partway) is crossed in the same state; it costs n
     times the steps of one copy.
   - Lemmas: `gstep_sound_same`, `gstep_sound_turn`, `gstep_sound_halt`.
2. **The block rules** (section Mac). The Lean simulator spends 87.8 of its 88.9 million rounds in the 87,854
   overflow visits. In those, the head walks across about 73 counter levels and back, and needs several rounds per
   level. Two rules take a whole level in one round, for every count:
   - `macL_tape`: D moving left, `1 0 (011)^k 1 Y` becomes `1 Y` with `(100)^(k-1) 1 0 1 1 0` behind the head,
     in 5 + 3(k-1) steps;
   - `macR_tape`: C moving right, `(100)^m 1 0 1 1 0` becomes `1 1 (011)^(m+1)` behind the head, in 3m + 5 steps.
3. **The visit rule of a zone** (section Zone, `visit`).
   - When the tape ends in counters `(011)^n` separated by `11` (bit 0) or `01` (bit 1), one visit of the right end
     is a binary increment of the bits.
   - It takes `vcnt n0 lv` = 10 + 6 n_0 + Σ (6 n_j + 4) + 5 steps, the sum over the 1 bits the carry passes.
   - Proved for every number of counters, every count and every tape left of the zone, by induction on the carry.
4. **V visits at once** (section Jump, `jump`).
   - In the coordinates N_0 = n_0 - s_1, N_j = n_j + s_j - s_(j+1), V increments are given in closed form
     (`addV`). This holds for every V after which the bits have not overflowed and every N_j is still at least 2.
   - In these coordinates a visit takes `11 + chain ps` steps (`chain_vcnt`), with 6 N_j + 4 for each level the
     carry reaches.
   - The V visits take `Jz V ps` = 11V + 6V(V-1) + Σ_j [V_j (6(N_j + b_j) + 4) - 6 Q(V_j + b_j + 1)] steps. The
     sum runs over the levels j, V_(j+1) = ⌊(V_j + b_j)/2⌋ is the number of carries into level j+1, and
     Q(n) = Σ_{x<n} ⌊x/2⌋.
   - Proved by induction on V (`Jz_succ`, through `chain_addV`, which is again an induction over the levels). It
     needs that no count at any level drops below the carries taken from it (`ntrT`), which the simulator checks.
   - `Jf`, the form that is evaluated, takes one multiplication per level (`Gf_Gt`, `Jf_Jz`).
5. **The run** (section Run).
   - The configuration carries its step count `cnt`.
   - At every visit the tape left of the head is put in a canonical form. The simulator reads a zone off it,
     chooses a number of visits V, and checks the hypotheses of `jump` by re-encoding the zone it read and
     comparing, so the parse is not trusted.
   - `round_sound`: every round takes the configuration it stands for to the one it returns, in exactly the number
     of steps it adds to the count, or the machine is halted.
   - `run_halts_in`: if `run p start = RHalt n`, then `halts_in tm c0 (N.to_nat n)`. The fuel is a `positive`
     (recursion on its bits), so 2^25 rounds cost no unary number.
6. **The evaluation** (`run_halts : run 33554432 start = RHalt K`, by `vm_cast_no_check`).
   - The halting transition F0 is met after 19,026,768 rounds: 6,466,831 rule L, 6,317,273 rule R, 6,242,664
     ordinary rounds, 116,182 visits simulated and 86,734 jumps.
   - It takes about 8 minutes and 700 MB.
   - `steps_172044` adds uniqueness (`halts_in_unique`): a halting configuration has no next step, so the machine
     cannot also halt at another time.

`../py/coqsim.py` is the same algorithm in Python. It gives the same round counts, and the same count after 10^5
and 10^6 rounds (80,943,943 and about 2.8·10^31).

## Speed

| | rounds | evaluation | checked by | steps |
|---|---|---|---|---|
| Lean (`../lean/Halt.lean`) | 88.9 million | about 6 minutes | `native_decide` (trusts Lean's compiler) | not counted |
| halting only (busycoq fork, commit 594cece; upstream busycoq PR #76) | 19.0 million | 160 s | `vm_compute` (Coq's kernel virtual machine) | not counted |
| this file | 19.0 million | about 490 s | `vm_compute` | exact |

The block rules are the speed-up. Counting costs about 6 extra minutes, almost all of it the closed form of the
jumps. Its numbers have up to 440 bits, and multiplying `positive`s is quadratic. Writing the sum with one
multiplication per level instead of two (`Gf`) made the counted run 2.5 times faster.

Other things tried, kept out of the file:

- folding cells into runs as they are pushed: 17.6 million rounds, but the fold costs more than it saves;
- crossing single copies only: the runs in states A and B are then unpacked one copy at a time, and the run
  explodes.

## Build

```sh
git clone -b BB6 https://github.com/meithecatte/busycoq
sh build.sh busycoq          # Coq 8.18; about 15 s for busycoq's core files, then about 9 minutes
```

`build.sh` does the following:

1. copies the file into `busycoq/verify/`;
2. compiles the core files it needs with plain `coqc` (no native compiler);
3. compiles the proof, and prints the time of `run_halts` and the axioms.

`build.log` is a run of it (Coq 8.18.0, core files already built).
