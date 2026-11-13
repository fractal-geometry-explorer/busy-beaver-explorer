# busycoq proof: 1RB0RD_1RC0LF_1LA0LB_---1RE_1LB1RA_0LC0RA never halts

> **In this repository** the files are flat in this folder: `lib/X.v` below means `X.v` here, and the generator is `../py/coq/gen_coq.py` (it reuses `../py/replay/`). The build script works from this folder as it is.

bbchallenge id 11019, a BB(6) holdout. The final theorem is

```coq
Theorem nonhalt : ~ halts tm c0.        (* H11019.v *)
```

with `TM`, `step`, `halts` and `c0` from busycoq's `TM.v`, instantiated to 6 states and 2 symbols by `BB62.v`
and `Individual62.v`, and `tm` the machine above (`H11019_Classes.v`).
`Print Assumptions nonhalt` prints `Closed under the global context`: no axioms, no `Admitted`.

## The proof

A round end is `node B T = 0^inf A> 01001000 (01)^B T 0^inf` (the head on the first cell written), `T` a word.
A class is the set of round ends `node (r0 + m x) tail`, `x >= 0`. `H11019_ClassData.v` lists 1,144 classes;
`InSet classes B T` says that `node B T` is in one of them.

1. **Reach** (`reach_set`). The run from blank tape reaches `node 28531 startTail`, which is in the set.
2. **Closed** (`closed_set : forall B Tl, InSet classes B Tl -> exists B' Tl', InSet classes B' Tl' /\
   node B Tl -->+ node B' Tl'`). For each class, one round from `node (r0 + m x) tail` with `x` free ends at
   `node (k + c x) to` (`clsRun`), and every `k + c x` is in a class of the list with tail `to` (`covers`:
   tested for `x` below a common multiple `P` of the moduli of those classes, each class used having a modulus
   that divides `c P`).
3. `nonhalt` follows by busycoq's `progress_nonhalt` and `multistep_nonhalt` (`nonhalt_of_closed`).

The runs are runs of a symbolic executor that is proved sound against busycoq's `step` (`lib/SymExecN.v`):

- A configuration is two lists of tokens and a state. A token is a cell or a block `w^n`, the count `n` of the
  form `c + a0 x0 + a1 x1 + ...` with binary numbers (`N`) and free variables `xi`.
- One move is a shift rule (a block next to the head is crossed in one go: `u w^k -> v u` proved on a finite
  window, applied to `w^(k m)` by induction), or else one machine step. When a step brings state A to the left
  end of the tape, the right side is re-bracketed and a table of cycle rules is tried. A cycle rule is a
  template of the whole tape whose block counts go from `b0 + 3 xi` to `b1 + 3 xi`; it is applied `n` times at
  once (induction on `n`), and `n` may itself be a count with a variable.
- `run_sound`: if `run T K S = Some S'` and the tables `T` are valid, the machine goes from `den rho S` to
  `den rho S'` for every value `rho` of the variables.

The arrival is 527,489 moves. The 1,144 rounds are 132,636,430 moves in all, the longest 231,156; the first
move of each is a machine step, which gives `-->+`. The end of a run is compared with the round end in a second
normal form (`canon`), because the executor's re-bracketing does not always give the same tokens for the same
cells. The tables are 8 + 7 shift rules and 6 cycle rules, each cycle rule proved by a run of the executor
without cycle rules (9,143 to 25,749 moves).

## Files

| file | what | how it is checked | time | peak memory |
|---|---|---|---|---|
| `lib/SymExecN.v` | the executor and its soundness (`run_sound`, `moveS_sound`, `canon_spec`, `chkR_ok`, `chkL_ok`, `chkRule_ok`); not specific to this machine | ordinary proof | 3 to 7 s | 554 MB |
| `H11019_Classes.v` | the machine `tm`; `node`; `Cls`, `clsRun`, `covers`, `InSet` with `clsRun_sound`, `covers_sound`, `closed_of_checks`; `arrives_sound`; `nonhalt_of_closed` | ordinary proof | 1 s | 436 MB |
| `H11019_Data.v` | the shift rules with `shR_chk`, `shL_chk`; the 6 cycle rules with `rule0_chk` ... `rule5_chk`; the tables `T`, `T_ok` | `vm_compute` for the checks | 1 s | 429 MB |
| `H11019_ClassData.v` | the 1,144 classes in 8 lists `chunk0` ... `chunk7`, and `classes` | data only | 11 s | 754 MB |
| `H11019_Arrive.v` | `startTail`, `arrive_ok`, `start_ok` | `vm_compute` | 1 s | 439 MB |
| `H11019_Chunk0.v` ... `H11019_Chunk7.v` | `chunk_i_ok`: `clsRun` and `covers` hold for the 143 classes of the chunk, 13 to 21 million moves | `vm_compute` | 24 to 35 s each | 446 MB each |
| `H11019.v` | `classes_ok`, `reach_set`, `closed_set`, `nonhalt` | ordinary proof | 1 s | 475 MB |

`lib/SymExecN.v` and `H11019_Classes.v` are written by hand. The others are generated:

```
python3 gen/gen_H11019.py OUTDIR        # about 6 minutes
```

It needs `gen/H11019_engine.py`, `gen/H11019_replay.py` and `gen/H11019_cert.json` next to it, and gives the
committed files byte for byte. `H11019_cert.json` is the list of classes (tail, `r0`, `m`, and the announced
`to`, `k`, `c`) and the start node; `H11019_engine.py` is a Python model of the executor and `H11019_replay.py`
finds the tables and the numbers of moves with it (they are the generator of the Lean proof of the same
machine); `gen_H11019.py` prints the result as Coq terms.

## Trust

The Python scripts and the list of classes are not trusted. They propose the shift rules, the cycle rules, the
classes and the numbers of moves. Coq checks every shift rule and every cycle rule itself, runs the executor
itself for every class, and tests the coverage itself. The executor is not trusted either: its strategy (which
rule to use, how to re-bracket the tape, how many times to apply a cycle rule) is ordinary code, and
`run_sound` covers every case of it.

All computation runs in Coq's kernel through `vm_compute` (`vm_cast_no_check`, checked by the kernel at `Qed`).
Nothing uses `native_compute`. Each computed lemma has the form `test = true`:

- `shR_chk`, `shL_chk`: every shift rule holds on its window;
- `rule0_chk` ... `rule5_chk`: the executor without cycle rules goes from the template before to the template
  after, and the counts before and after are congruent modulo 3;
- `arrive_ok`: the run from blank tape ends at `node 28531 startTail`; `start_ok`: that node is in the set;
- `chunk0_ok` ... `chunk7_ok`: `clsRun T d && covers classes d` for every class `d` of the chunk.

Everything else is ordinary proof.

## Build

```
git clone https://github.com/meithecatte/busycoq
sh build_H11019.sh busycoq        # second argument: chunk files compiled at once, default 2
```

This needs Coq 8.18 (tested with 8.18.0). The script also accepts a checkout of busycoq's BB6 branch, which has
its own `BB62.v` and `Individual62.v`; `lib/BB62.v` and `lib/Individual62.v` are copied only when the checkout
has none.

## Checked

Clean builds with Coq 8.18.0 and two chunk files at a time, from a copy of the BB6 branch and from a fresh
clone of the main branch, took about 2.5 minutes each: about 120 s of wall time for the 8 chunks, 11 s for
`H11019_ClassData.v`, the rest under 20 s. The last line of both is `Closed under the global context`. The log
is `build.log`; it also has the time and peak memory of each file.
