# Coq (busycoq) proof

A second, independent proof that this machine never halts, in Coq on top of
[busycoq](https://github.com/meithecatte/busycoq):

```coq
Theorem nonhalt : ~ halts tm c0.        (* H32641.v *)
```

`TM`, `step`, `halts` and `c0` are busycoq's own. `Print Assumptions nonhalt` prints
`Closed under the global context`. The long computations run under `vm_compute`, inside Coq's kernel, where the
Lean proof in `../lean` uses `native_decide`.

- `H32641_Sim.v`: the machine, a window simulator and a block macro simulator, both proved sound (ordinary proof).
- `H32641_Period.v`: `Cyc X (n+1) -->+ Cyc X (n+2)` for every `n`, given three facts about two window runs
  (ordinary proof).
- `H32641_Data.v`, `H32641_Bound.v`, `H32641_Chunk1.v` ... `H32641_Chunk16.v`, `H32641_Reach.v` (generated):
  the run from blank tape to `Cyc X 7` at step 16,730,681,219, as 1,045,666,889 crossings of 16-cell blocks in
  16 chunks, each checked by `vm_compute`.
- `H32641.v`: the five computed facts about the last configuration and the two excursions, and `nonhalt`.
- `BB62.v`, `Individual62.v`: busycoq's `BB52.v` and `Individual52.v` with a sixth state.
- `macro37.c`, `gen37.py`: the C simulator and the generator of the generated files. They are not trusted: Coq
  recomputes everything they propose.

Build (Coq 8.18.0; about 7 minutes with two chunk files at a time, 500 MB of memory per chunk file):

```
git clone https://github.com/meithecatte/busycoq
sh build_H32641.sh busycoq
```

Regenerate the generated files:

```
gcc -O2 -o macro37 macro37.c
./macro37 $(python3 gen37.py --bounds) > out.txt
python3 gen37.py 16 6 out.txt .
```
