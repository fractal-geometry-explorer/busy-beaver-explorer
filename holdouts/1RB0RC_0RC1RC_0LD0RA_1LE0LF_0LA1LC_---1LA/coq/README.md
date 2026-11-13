# busycoq proof: 1RB0RC_0RC1RC_0LD0RA_1LE0LF_0LA1LC_---1LA never halts

> **In this repository** the files are flat in this folder: `lib/X.v` below means `X.v` here, and the generator is `../py/coq/gen_coq.py` (it reuses `../py/replay/`). The build script works from this folder as it is.

bbchallenge id 65826, a BB(6) holdout. The final theorem is

```coq
Theorem nonhalt : ~ halts tm c0.        (* H65826.v *)
```

with `TM`, `step`, `halts` and `c0` from busycoq's `TM.v`, instantiated to 6 states and 2 symbols by `BB62.v`
and `Individual62.v`, and `tm` the machine above (`H65826_Data.v`).
`Print Assumptions nonhalt` prints `Closed under the global context`: no axioms, no `Admitted`.

## The proof

Let `Cyc r = 0^inf E> 0 (1011001)^59 1011 00000 1101100110110 (011)^16 001101100110 (011)^r 0^inf`
(the head on the first cell written).

1. **Reach** (`reach : c0 -->* Cyc 16797709`). The generator counts 1,818,198,163,340,705 machine steps from
   blank tape; the Coq proof does not count steps.
2. **Growth** (`grow : forall x, Cyc (65 + 2 * x) -->+ Cyc (65 + 2 * (x + 160521464))`). One period of the
   machine's growth cycle, for every value of the count of the last block (by the generator's count,
   650,373,336,347,246,654 + 8,765,861,712 x steps).
3. `16797709 = 65 + 2 * 8398822`, so `nonhalt` follows by busycoq's `progress_nonhalt_simple` and
   `multistep_nonhalt`.

Both facts are runs of a symbolic executor that is proved sound against busycoq's `step` (`lib/SymExecN.v`):

- A configuration is two lists of tokens and a state. A token is a cell or a block `w^n`, the count `n` of the
  form `c + a0 x0 + a1 x1 + ...` with binary numbers (`N`) and free variables `xi`.
- One move is a shift rule (a block next to the head is crossed in one go: `u w^k -> v u` proved on a finite
  window, applied to `w^(k m)` by induction), or else one machine step. When a step brings state E to the left
  end of the tape, the right side is re-bracketed and a table of cycle rules is tried. A cycle rule is a
  template of the whole tape whose block counts go from `b0 + 2 xi` to `b1 + 2 xi`; it is applied `n` times at
  once (induction on `n`).
- `run_sound`: if `run T K S = Some S'` and the tables `T` are valid, the machine goes from `den rho S` to
  `den rho S'` for every value `rho` of the variables.

The run of step 1 is 5,037,044 moves from blank tape (`arrive_run`). The run of step 2 is 5,581,714 moves from
`Cyc (65 + 2 x)` with `x` free (`period_run`); its first move is a machine step, which gives `-->+`. The tables
are 13 + 18 shift rules, each checked by a window run of at most 41 steps, and 12 cycle rules, each proved by a
run of the executor without cycle rules (422 to 201,007 moves).

## Files

| file | what | how it is checked | time | peak memory |
|---|---|---|---|---|
| `lib/SymExecN.v` | the executor and its soundness (`run_sound`, `runTo_sound`, `runTo1_sound`, `chkR_ok`, `chkL_ok`, `chkRule_ok`); not specific to this machine | ordinary proof | 3 to 7 s | 554 MB |
| `H65826_Data.v` | the machine `tm`; the shift rules with `shR_chk`, `shL_chk`, `T0_ok`; the 12 cycle rules; the tables `T`; `cycToks` (the right side of `Cyc`, as tokens) | `vm_compute` for the two checks | 1 s | 430 MB |
| `H65826_Rules.v` | `rule0_chk` ... `rule11_chk`, `T_ok` | `vm_compute`, one evaluation for each rule | 1 s | 429 MB |
| `H65826_Arrive.v` | `arrive_run` | `vm_compute`, 5,037,044 moves | 10 s | 429 MB |
| `H65826_Period.v` | `period_run` | `vm_compute`, 5,581,714 moves | 11 s | 429 MB |
| `H65826.v` | `Cyc`, `den_cyc`, `reach`, `grow`, `nonhalt` | ordinary proof | 1 s | 453 MB |

`lib/SymExecN.v` and `H65826.v` are written by hand. The four others are generated:

```
python3 gen/gen_H65826.py OUTDIR        # about 20 s; needs gen/H65826_engine.py and gen/H65826_replay.py
```

This gives the committed files byte for byte. `gen/H65826_engine.py` is a Python model of the executor and
`gen/H65826_replay.py` finds the tables with it (they are the generator of the Lean proof of the same machine);
`gen_H65826.py` prints the result as Coq terms.

## Trust

The Python scripts are not trusted. They propose the shift rules, the cycle rules and the numbers of moves.
Coq checks every shift rule and every cycle rule itself, and runs the executor itself. The executor is not
trusted either: its strategy (which rule to use, how to re-bracket the tape, how many times to apply a cycle
rule) is ordinary code, and `run_sound` covers every case of it.

All computation runs in Coq's kernel through `vm_compute` (`vm_cast_no_check`, checked by the kernel at `Qed`).
Nothing uses `native_compute`. Each computed lemma has the form `test = true`:

- `shR_chk`, `shL_chk`: every shift rule holds on its window;
- `rule0_chk` ... `rule11_chk`: the executor without cycle rules goes from the template before to the template
  after, and the counts before and after are congruent modulo 2;
- `arrive_run`, `period_run`: the two runs end exactly at the tokens of `Cyc`.

Everything else is ordinary proof.

## Build

```
git clone https://github.com/meithecatte/busycoq
sh build_H65826.sh busycoq
```

This needs Coq 8.18 (tested with 8.18.0). The script also accepts a checkout of busycoq's BB6 branch, which has
its own `BB62.v` and `Individual62.v`; `lib/BB62.v` and `lib/Individual62.v` are copied only when the checkout
has none.

## Checked

Clean builds with Coq 8.18.0, from a copy of the BB6 branch and from a fresh clone of the main branch, took
about 40 s each. The last line of both is `Closed under the global context`. The log is `build.log`; it also
has the time and peak memory of each file.
