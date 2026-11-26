# Example: the end of the halting orbit of 1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC, replayed

The busycoq proof of this machine follows 79,859,656,218,974 visits in 400 segments with a checker written for
it (blocks of up to 36 visits). This folder re-checks its last segment, the 59,656,218,975 visits from visit
79,800,000,000,000 to the halt, with the checker that `segreplay.py` generates from
`../../specs/1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC.json`: one visit at a time, 12 segments of 5·10^9 visits,
about 3 minutes each on one core (`build.log`).

| file | what it is |
|---|---|
| `endpoints.txt` | the segment end points proposed by the C runner (not trusted) |
| `Visits.v` | the machine's map `op` on natural numbers, copied from the busycoq proof, which proves it on the tape |
| `Link.v` | `op_opz`: `op` and the generated `opz` are the same map; `halt_orbit`: a replay that ends halted gives `opIter j (a, b) = Some (a', 3)` |
| `Halt.v` | `tail_halts`: from the state at visit 79,800,000,000,000 the orbit of `op` reaches some (a, 3) |

`Link.v` is the only hand-written proof a machine needs on top of its tape proof, and it is short: the generated
map is the description read case by case.

To rebuild (coqc 8.20 with the native compiler):

```sh
cd tools/segreplay
D=/tmp/replay; mkdir -p $D; cp examples/1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC/*.v $D/
S=specs/1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC.json
python3 segreplay.py coq $S $D
python3 segreplay.py segs $S examples/1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC/endpoints.txt $D
./build.sh $D 4
F="-Q coq SegReplay -Q $D M"; coqc $F $D/Visits.v; coqc $F $D/Link.v; coqc $F $D/Halt.v
```

`Print Assumptions tail_halts` lists only the primitive integer axioms of `Uint63`; the segments also trust
`native_compute`.
