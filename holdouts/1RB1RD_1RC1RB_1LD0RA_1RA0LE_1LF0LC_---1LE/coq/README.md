# busycoq proof: 1RB1RD_1RC1RB_1LD0RA_1RA0LE_1LF0LC_---1LE halts

bbchallenge id 172044, a BB(6) holdout. The final theorem is

```coq
Theorem halts_172044 : halts tm c0.      (* M172044, in M_1RB1RD_1RC1RB_1LD0RA_1RA0LE_1LF0LC_HHH1LE.v *)
```

with `TM`, `halts`, `c0` and the tape notations from busycoq's `TM.v`, instantiated to 6 states and 2 symbols by
`BB62.v` and `Individual62.v` (busycoq's BB6 branch), and `tm` the machine above, read from its TNF string by
`TM_from_str`. `Print Assumptions M172044.halts_172044` prints `Closed under the global context`: no axioms, no
`Admitted`. The proof is one file of 1,272 lines, written in the style of busycoq's own files for this kind of
machine: rules proved by `es`, an accelerated simulator proved sound, and one evaluation by `vm_compute`.

It is a port of the Lean proof in `../lean`, with one addition, two block rules for whole counter levels, that
makes the evaluation about 4.7 times shorter.

## The proof

1. **A run-length simulator for any machine** (section Sim). A tape is two stacks of items, a cell or a run
   `w^n` of a word; the head faces left or right, and the leftward half is the rightward half applied to busycoq's
   `flip` of the machine. One round is one transition, a run crossed in one go when a copy of its word (or two
   copies, or a copy entered partway) is crossed in the same state, or a copy unpacked
   (`gstep_sound_same`, `gstep_sound_turn`, `gstep_sound_halt`).
2. **The visit rule of a zone** (section Zone, `visit`): when the tape ends in counters `(011)^n` separated by `11`
   (bit 0) or `01` (bit 1), one visit of the right end is a binary increment of the bits, for every number of
   counters, every count and every tape left of the zone (induction on the carry).
3. **V visits at once** (section Jump, `jump`): in the coordinates N_0 = n_0 - s_1, N_j = n_j + s_j - s_(j+1),
   V increments are given in closed form (`addV`), for every V after which the bits have not overflowed and every
   N_j is still at least 2.
4. **The block rules** (section Mac). The Lean simulator spends 87.8 of its 88.9 million rounds in the 87,854
   overflow visits, where the head walks across about 73 counter levels and back, and needs several rounds per
   level. Two rules take a whole level in one round, for every count:
   - `macL_tape`: D moving left, `1 0 (011)^k 1 Y` becomes `1 Y` with `(100)^(k-1) 1 0 1 1 0` behind the head,
     in 5 + 3(k-1) steps;
   - `macR_tape`: C moving right, `(100)^m 1 0 1 1 0` becomes `1 1 (011)^(m+1)` behind the head, in 5 + 3m steps.
5. **The run** (section Run). At every visit the tape left of the head is put in a canonical form; the simulator
   reads a zone off it, chooses a number of visits V and checks the hypotheses of `jump` by re-encoding the zone it
   read and comparing (so the parse is not trusted). `round_next` and `round_halt`: every round takes the
   configuration it stands for to one the machine reaches, or halts. `run_sound`: if `run p start = RHalt` the
   machine halts from blank tape. The fuel is a `positive` (recursion on its bits), so 2^25 rounds cost no unary
   number.
6. **The evaluation** (`run_halts : run 33554432 start = RHalt`, by `vm_cast_no_check (eq_refl RHalt)`): the
   halting transition F0 is met after 19,026,768 rounds (6,466,831 rule L, 6,317,273 rule R, 6,242,664 ordinary
   rounds; 116,182 visits simulated and 86,734 jumps). About 160 seconds and 600 MB.

`../py/coqsim.py` is the same algorithm in Python, with step counts: it gives the same round counts and ends at
the step count of `../py/accel.py`. The proof itself does not count steps.

## Speed

| | rounds | evaluation | checked by |
|---|---|---|---|
| Lean (`../lean/Halt.lean`) | 88.9 million | about 6 minutes | `native_decide` (trusts Lean's compiler) |
| this file | 19.0 million | 160 s | `vm_compute` (Coq's kernel virtual machine) |

Other things tried, kept out of the file: folding cells into runs as they are pushed (17.6 million rounds, but the
fold costs more than it saves); crossing single copies only (the runs in states A and B are then unpacked one copy
at a time and the run explodes). Multiplying the jump's numbers as `2^j * x` rather than `x * 2^j` matters:
`Pos.mul` recurses on its first argument, and the other order made the evaluation twice as slow.

## Build

```sh
git clone -b BB6 https://github.com/meithecatte/busycoq
sh build.sh busycoq          # Coq 8.18; about 15 s for busycoq's core files, then about 3 minutes
```

`build.sh` copies the file into `busycoq/verify/`, compiles the core files it needs with plain `coqc` (no native
compiler), then the proof, and prints the time of `run_halts` and the axioms. `build.log` is a run of it (Coq
8.18.0, core files already built).
