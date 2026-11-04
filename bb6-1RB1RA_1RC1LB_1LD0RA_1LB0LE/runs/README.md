# Long runs

Outputs of `c/passorbit.c` (built with `gcc -O3 -march=native`), in the protocol of `tools/c/parts.h`. All of them
iterate the closed form of the pass map, which is tested and not proved. See `notes/LAB_NOTES.md` (31 October 2026).

| file | command | CPU time |
|---|---|---|
| `orbit_1e11.txt` | `passorbit orbit 100000000000`: the blank orbit, checkpoints and statistics | 35 min |
| `comps28.txt` | `passorbit comps 1 28 1000`: every list of 1 to 28 ones | 9 min |
| `grid10k.txt` | `passorbit grid 10000 10000 1000`: every `[a, b]` with a, b ≤ 10⁴ | 13 min |
| `rnd_B.txt` | `passorbit random 10000000 12 B 1000 B`: 10⁷ random lists of 1 to 12 blocks in 1..B | 1 to 2 min each |

The searches ran as 48 parts, 3 at a time (`tools/c/run_parts.sh 48 3 DIR ./passorbit ...`), merged by
`tools/py/merge_parts.py`, which refuses a missing or unfinished part. Only the first 40 `event` lines are kept here.

Outputs of the Python return-map tools (31 October 2026, the long-run dynamics):

| file | command | CPU time |
|---|---|---|
| `classes72.txt` | `py/returnmap.py classes 72`: the excursions on classes down to mod 2^74, open members run concretely | 2.5 min |
| `tree72.txt` | `py/dynamics.py tree 40 48 56 64 72`: routes, open classes, worst margin by depth | 6 min |
| `dyn_orbit.txt` | `py/dynamics.py orbit 300000` and `py/dynamics.py mixing 48` | 1 min |

Outputs of `py/invsearch.py` (1 November 2026, the search for an inductive first-block bound):

| file | command | CPU time |
|---|---|---|
| `psi_triples_orbit.txt` | `orbit_triples(10**8)`: (block count, psi, stop index) on passes 31 to 10^8 of the blank orbit | 4 min |
| `psi_triples_classes.txt` | `class_triples(64)`: the same over every excursion class a = 1 mod 4 to mod 2^66 | 20 min |
