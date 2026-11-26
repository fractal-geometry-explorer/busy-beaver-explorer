# segreplay: segmented replay of a visit map, checked by Coq

This is the proof of 1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC (the machine halts after 8·10^13 visits; see
`holdouts/1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC`) turned into a tool that works for other machines. It does
three jobs:

1. **Replay.** Given a visit map, it writes a Coq development in which Coq itself follows the orbit, cut into
   segments that are checked independently and in parallel. The result is either "the orbit halts at visit N" or
   "the orbit does not halt in its first N visits".
2. **Hunt.** It writes a C program for the same map that follows the orbit fast, proposes the segment end
   points, and reports the halting visit if it meets one.
3. **Estimate.** The C program can also probe how often states near the orbit halt, which gives an estimate of
   the expected number of halts per doubling of the run. That is what ranks halt hunts (see
   `holdouts/recent-proofs/halt-hunt-ranking-nov26.md`).

Nothing the C program says is trusted. It only proposes end points; Coq recomputes every segment.

## What a visit map is

A state is a *frame* (one of finitely many tape shapes) with a few non-negative counts. One visit takes a state
to the next state or halts. The map is an ordered list of cases, and the first case whose guard holds applies:

```json
{
 "name": "visits A(a, b) = 0^inf 1^a 0 C> 1^b 0^inf",
 "machine": "1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC",
 "vars": ["a", "b"],
 "frames": ["A"],
 "start": ["A", 2, 9],
 "cases": [
  {"frame": "A", "guard": ["b == 3"], "halt": true},
  {"frame": "A", "guard": ["b == 2", "a < 3"], "to": "A", "out": ["0", "7"]},
  {"frame": "A", "guard": ["b <= a"], "to": "A", "out": ["a - b + 1", "2*b + 3"]},
  {"frame": "A", "guard": ["a % 2 == 0"], "to": "A", "out": ["2*a + 4", "b - a - 1"]},
  ...
 ]
}
```

- A guard is a list of comparisons (`==`, `!=`, `<=`, `<`, `>=`, `>`) between linear expressions in the counts.
- An expression may also use `(x + c) // m` and `(x + c) % m` for one count `x` and constants `c`, `m`.
- A case either halts (`"halt": true`), is marked as outside the description (`"stuck": true`), or names the
  next frame and one output expression per count.
- A state that no case covers is also "stuck". A stuck orbit proves nothing, and the tools say so.

`lean2spec.py` writes this description from a Lean frame map defined by pattern matching (the `next` of the
`Phases.lean` files in this repository), including results that use one `min`. Eight descriptions made this way
are in `specs/`.

The map must fit in 63-bit integers along the stretch that is replayed. Maps whose counts grow exponentially
need another tool (closed-form jumps on big integers).

## Commands

```sh
python3 lean2spec.py ../../holdouts/M/lean/Phases.lean next "g 0 1" M > specs/M.json
python3 segreplay.py coq  specs/M.json OUT          # OUT/Map.v
python3 segreplay.py c    specs/M.json OUT/run.c    # the C runner
gcc -O2 -o OUT/run OUT/run.c -lm
OUT/run 1000000000 250000000 > OUT/out.txt          # follow 10^9 visits, a line every 2.5·10^8
python3 segreplay.py segs specs/M.json OUT/out.txt OUT   # OUT/J000.v ..., OUT/Final.v
./build.sh OUT 4                                    # check everything with coqc, 4 segments at a time
```

`OUT/run N SEG ckpt` keeps a checkpoint in the file `ckpt` and resumes from it, so a replay can start anywhere on
the orbit. `segs --vm` writes segments that use `vm_compute` when no native compiler is at hand (about ten times
slower).

## What Coq proves

`coq/Core.v` is written once and does not depend on the machine:

- `zit opz k z` is k visits from z.
- `run` follows a fast step function for a given number of visits. `seg_ok` says that if the check
  `seg p n s s'` returns `true`, then `zit opz n (zs s) = zs s'`.
- `zit_chain` glues segments, and `zit_fix` says a fixed point stays put.

`Map.v` is generated for each map:

- `opz`: the map on unbounded integers. **This is the statement to read**: it is the description above, case by
  case, and it is what a proof on the tape has to match.
- `ex1`: the same cases on 63-bit machine integers.
- `ex1_ok`: `ex1` equals `opz` while every count is below a bound (2^58 or so, computed from the coefficients).
  The proof is generated and needs no hand work: it splits on the guards and closes every case with `lia`.
- `seg` and `seg_ok` for this map, and `halt_fix`: the halted state is a fixed point of `opz`.

`J000.v`, `J001.v`, ... each state one segment and prove it by `native_compute`. `Final.v` chains them into

- `orbit : zit opz N (zs first) = zs last`, and then
- `orbit_halts` (the state after N visits is the halted one), or
- `no_halt` (no state among the first N visits is halted).

Besides Coq's kernel the result rests on the primitive integer axioms of `Uint63` and, in the segment files, on
`native_compute`.

**What is not proved here** is that the machine follows the map. That is a proof on the tape, and it stays with
each machine: in Coq as in `Rules.v` of the busycoq proof, or in Lean as `next_sound` and `halts_iff` of the
`Phases.lean` files. Until the two are joined in one prover, a replay made from a Lean map is a Coq-checked
computation about a map that Lean proved.

## Speed

On one core, Coq follows about 2.5·10^7 visits per second for the two-count map of
1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC and about 10^7 for the 66-case map of
1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE. The C runner is 10 to 30 times faster. So a replay of 10^12 visits is
about 30 core-hours, and beyond 10^13 a map needs its own accelerated step.

That is what the original proof has: blocks of 12 to 36 visits taken at once from a guessed digit string
(`Block.v`, `Tab.v`, `Blk.v`, `BlkOk.v` there). The runner in `Core.v` is built to take such a step. `run` is
parametric in a function `one n i s` that may advance by any number of visits, and `seg_ok` only asks for
`one_spec`: what it returns is the right iterate of `opz`, and it never passes visit n. The plain steps here
(`one1`, `oneB`) are two instances.

## The hit estimate

```sh
OUT/run pert 2147483648 8 256 4000 1024 1 > OUT/pert.txt     # N G R T SP Q
python3 segreplay.py hits specs/M.json OUT/pert.txt 4000
```

At sample visits of the orbit (SP per doubling of the visit index) the probe makes R copies of the state, moves
every count by Q times a random amount in [-G, G], and follows each copy for T visits. If a fraction P of the
copies halt, a state "like the orbit's" halts at a rate of about -ln(1 - P) / T per visit, and the orbit is
expected to meet 2^(b-1) times that many halts while it runs from visit 2^(b-1) to visit 2^b. `hits` prints
this number for each doubling and fits its trend.

How to read it:

- **Constant per doubling.** The sum diverges like the logarithm of the run length. A halt is expected, and
  every doubling of the run buys the same chance. Hunting pays if doublings are cheap.
- **Falling geometrically.** The sum converges. If what is left is small, stop hunting and look for a
  non-halting argument.
- **The expected count so far is large and the orbit has not halted, or a fixed fraction of the copies halts at
  every size.** The orbit keeps something the copies break (a parity, a residue, a relation between counts).
  That is a lead for a non-halting proof, not a reason to hunt. Running the probe with Q = 2, 3, 6 keeps
  residues and shows which one matters.

This is a heuristic: it treats the orbit as a typical point among its neighbours. It was calibrated on the one
machine where the answer is known (see the ranking note).
