# tools/transfer: screens for "does a proved machine's invariant hold on a holdout?"

Tools and data behind [`../../followup/invariant-transfer.md`](../../followup/invariant-transfer.md). They were run
once, in one working folder, on 26 November 2026. The scripts read their inputs from the current folder under the
file names given below; they are kept as a record of what was run and are not polished.

## Inputs to prepare

- `H.txt`: the 608 holdouts, one per line (`BB6_holdouts_608.txt`).
- `dec.json`: `{machine: "open" | "nonhalt" | "halt"}` from the `status.json` files.
- `pool_raw.json`: `{table: [files]}` for every `TM_from_str "..."` in `verify/*.v` of busycoq's `BB6` branch
  (our fork, commit `4e86645`), without the `Eqv*` files.
- For the Coq runs: Coq 8.20.1 (`nix --extra-experimental-features 'nix-command flakes' profile install
  nixpkgs#coq_8_20`), and in busycoq's `verify/` folder the files `LibTactics Helper Eqb HashTable TM Compute Flip
  Permute Pigeonhole Enumerate Individual BB62 Individual62 DHTM CTL CTL62` compiled in that order with
  `coqc -Q . BusyCoq -Q ./BigInt BigInt FILE.v` (about 20 seconds). `RRBA.v` and `Ternary.v`, `Inductive.v`,
  `Inductive62.v` are needed for the halting and inductive deciders (a few minutes).

## Programs

| file | what it does |
|---|---|
| `match.c` | matches holdout tables with wildcard slots against the pool, over all 720 renamings and the mirror |
| `usage.c` | runs a machine N steps; per transition, number of uses and the last window in which it was used |
| `quiet_matches.py` | pool tables that agree with a holdout outside its quiet transitions |
| `merge.c` | do two runs of one table from two start states ever share a configuration (hash-sampled) |
| `runcert.sh MACHINE "CERT" [TIMEOUT]` | runs one busycoq `solve_cert` certificate on any machine: PASS, FAIL, TIMEOUT or ABORT (out of memory). Needs `BUSYCOQ=/path/to/busycoq/verify` |
| `sibling_certs.py` | the sibling's certificate on the holdout at late starts and every block phase |
| `cps_late.cpp` | n-gram CPS from a late configuration, optionally with a forbidden local pattern (unverified, for screening) |
| `near1.py`, `near2.py` | proved tables one and two transitions from an open holdout, start state kept |
| `lock.c` | runs a holdout and a neighbour together; at each parting searches for the next moment, within K steps of each, where tape and head agree again |
| `resync_pairs.py` | the same in Python with `tools/py/syncpair.py`, for small step counts |
| `stopped.py` | lists holdouts whose quiet transitions make them equal to a pool table |

## Data

| file | content |
|---|---|
| `data/same_table_siblings.json` | 105 pairs (open holdout, pool table with the same transitions at another start state), with the proof file. Entries from `CubicCap.v` and `HaltingCryptidCandidate1.v` are not proofs |
| `data/sibling_merge.out` | output of `merge.c` for the sibling pairs, 10^9 steps each: no shared configuration |
| `data/sibling_cert_sweep.txt` | every Coq certificate run of screen 1 with its result |
| `data/quiet_transitions.json` | per holdout, the transitions never used and those used and then quiet, in 3·10^9 steps |
| `data/quiet_matches_summary.json` | per holdout, how many pool tables agree outside the quiet transitions |
| `data/lockstep_pairs.out.gz` | output of `lock.c` for all 2,138 neighbour pairs, 10^8 steps each |
