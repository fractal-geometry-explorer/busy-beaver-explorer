# busycoq proofs: two BB(6) holdouts never halt

These are Coq proofs, built on [busycoq](https://github.com/meithecatte/busycoq), that two BB(6) holdout machines
never halt from blank tape:

| machine | bbchallenge id | final theorem | check time |
|---|---|---|---|
| `1RB0LF_1LC0LA_1RA0RD_---1RE_1LA1RC_0LB0RC` | 36670 | `H36670.nonhalt : ~ halts tm c0` | about 80 s |
| `1RB0LE_1RC---_1RD1RE_1LA0RF_0RC0LA_0LC0RB` | 113677 | `H113677.nonhalt : ~ halts tm c0` | about 3 min |

Both theorems use busycoq's own definitions: `TM`, `step`, `halts` and `c0` from `TM.v`, instantiated to 6 states
and 2 symbols. `Print Assumptions nonhalt` reports that each is *closed under the global context*: no axioms.

## Files

- `lib/BB62.v`, `lib/Individual62.v`: busycoq's `BB52.v` and `Individual52.v` with a sixth state `F`.
- `lib/SymRun.v` is a symbolic runner, proved sound against busycoq's semantics. A configuration is a list of
  tokens. A token is either a single cell or a run `w^n` whose count `n` is linear in some variables. `auto`
  searches for a run from one configuration to a target, and `auto_sound` proves that an answer of `true` means
  the real machine goes from one to the other in at least one step, for every value of the variables. It can:
  - take single steps;
  - cross whole runs by a shift rule found on the spot;
  - regroup runs: rotate a run (`x (y x)^n = (x y)^n x`, either way), split `w^(mq+r)` into `(w^m)^q w^r`, and
    absorb copies.

  The target is compared after a normal form. There are four normal forms, `norm01`, `normG`, `normL` and
  `normS`, each proved to keep the tape.
- `lib/SymForms.v` turns a symbolic run into a statement about the machine. It covers phase forms as templates,
  rules between forms at linear arguments (`rules_sound`), and equal forms (`formeq_sound`).
- `H36670/H36670.v` holds the certificate of the Lean proof (`lean/Cert.lean`) in Coq. It has:
  - 62 phase templates, each with a round and an end of epoch;
  - the start from blank tape;
  - the potential `j + 2k + pot t >= 215`.

  Each run is evaluated by `vm_compute`, and the glue is ordinary Coq.
- `H113677/H113677_Rules.v` holds 15 phase forms and the 27 rules of `py/macro.py`, each checked by the symbolic
  runner. It also has the 7 form identities and the 7 cycle iterates, which are proved by induction.
- `H113677/H113677_Table.v` covers the run from blank tape. The first 29,301 steps reach `O 14 37 11`, checked by
  the runner. The branch table then takes 196 moves to the last macro state before step 10^30,
  `T2 34158019330534 128092572489511 160237983842729 41908435347077`. Large numbers are written `N.to_nat n%N`.
  They are only compared by `lia` and never computed in unary.
- `H113677/H113677.v` holds the invariant `Good` from `lean/Closed.lean`, the 20 move lemmas, `good_step` and
  `nonhalt`.
- `gen/` holds the generators. `gen_m1.py` reads the Lean tables. `gen_m2.py` and `gen_m2_files.py` read the
  forms and rules from the holdout's `py/` folder. `m2_derived.v` and `m2_closed.v` are hand-written parts that are
  spliced in. Run them as `BBX=/path/to/busy-beaver-explorer python3 gen/gen_m1.py OUTDIR` (and the same for
  `gen_m2_files.py`); regenerating gives the committed `.v` files byte for byte.

## Build

```
git clone https://github.com/meithecatte/busycoq
sh build.sh busycoq          # copies the .v files into busycoq/verify and runs coqc in order
```

`build.sh` stops at the first file that fails and prints Coq's output. This needs Coq 8.18 (tested with 8.18.0). Only busycoq's core files are compiled: `LibTactics`, `Helper`,
`Pigeonhole`, `TM`, `Compute`, `Flip`, `Permute` and `Individual`.

## Trust

Every computation here runs in Coq's kernel. Most of it uses `vm_compute`, Coq's bytecode evaluator, which is part
of the kernel's conversion check. That is the analogue of Lean's `decide +kernel`, not of `native_decide`. Nothing
uses `native_compute`. The Lean proof of 36670 needed `native_decide` for its start and its 62 epoch ends (about
2.6 million symbolic moves). Here the same checks run under `vm_compute` in about a minute.

## Checked

A clean build from a fresh copy of busycoq's core files, with Coq 8.18.0, took 79 s for `H36670.v` and
19 s + 28 s + 130 s for the three `H113677` files. Both `Print Assumptions nonhalt` lines print
`Closed under the global context`. The log is `build.log`.
