# busycoq's accelerated-induction deciders with block hints

Experiment of 24 Nov 2026. Question: do busycoq's accelerated-induction deciders (mxdys's `Inductive.v` and
`RWLAcc.v`, BB6 branch, commit 33209bc) settle any of the open BB(6) holdouts once they are given the
block words we have already decoded, as hints?

**Answer: no.** 1,572 runs on 509 machines settled none. No run reported `nonhalting` or `halts`.

## What was run

`Inductive.v`'s simulator (`hlin_layers_steps`) and `RWLAcc.v`'s macro machine are proved correct in Coq. Their
OCaml extraction prints `nonhalting` only when the verified checker accepts. Any such machine could then be closed
in Rocq with `decide_hlin_nonhalt_spec` under the same config, as in `verify/Indv*.v`.

`IndHint_inf.v` is busycoq's `Inductive_inf.v` with more command-line flags. Each flag maps to a `SetConfig`
field that the stock `./decider` does not expose:

| flag | config field | meaning |
|---|---|---|
| `--repeaters 0010,1010,...` | `allowed_repeaters` | only these exact words may become repeaters `w^n` (the "hint" mode) |
| `--block-size k` | `fixed_block_size` | the "Fixed Length Repeater" mode |
| `--mnc n`, `--exploop` | `mnc`, `enable_exp_toplevel_loop` | the "Others" settings the SBC/BEC proofs use |
| `--side0inf k`, `--initial-steps`, `--max-period`, `--dec-min`, `--rep-rw-limit`, `--rep-step1-limit` | same names | remaining knobs |

`RWLAcc_inf.v` extracts `RWLAcc.decide_nonhalt` / `decide_halt`. Usage: `rdecider bsz mnc T machine`.

Build: `sh build.sh <busycoq BB6 checkout>` (Coq 8.18, about 5 minutes on 4 cores).

| run | machines | settings | budget | result |
|---|---|---|---|---|
| `results/res1.tsv` | 123 of F01, F05, F09 | `def` (no hints); `rep3` / `rep6x` / `rep4a`: top 3, 6 or 4 periodic words of the tape at record moments (`words.py`, every rotation and reversal), with `--mnc 4 --exploop` or `--arithseq`; `bsK`: fixed block length K = length of the top word, with `--arithseq` | maxT 300,000, 90 s | 0 decided: 322 failed, 286 timed out, 7 stack overflows |
| `results/res_so.tsv` | the 7 stack overflows again with `ulimit -s unlimited` | same | 90 s | 7 timed out |
| `results/res_rd.tsv` | 506 holdouts whose README names block words | `--repeaters` = the backticked words of the machine's README (`readmewords.py`, up to 8, every rotation and reversal), `--mnc 4 --exploop` | maxT 300,000, 90 s | 0 decided: 173 failed, 333 timed out |
| `results/res_rwl.tsv` | 123 of F01, F05, F09 | RWLAcc with block size 2, 3 and the lengths of the top 4 words, mnc 2 | T = 10^7, 120 s | 0 decided: 144 failed, 299 timed out |

"failed" means the decider stopped and gave up within its budget. "TIMEOUT" means the wall clock ran out first.

## Why it fails (as far as the runs show)

These machines are what is left after mxdys's own Inductive / RWLAcc / RRBA passes with per-machine parameter
search, so a null result was the likely outcome. Hints only narrow the repeater search; they add no reasoning
power. Each decoded mechanism needs a fact that the nested-repeater induction cannot state:

- F05: a merge of drifting base-5 markers is rare but irregular.
- F01: a reset rebuilds a block to about 4/3 or 10/3 of its old size.
- F09: counters sit inside a bouncer.

Each of these needs arithmetic over the counts (residues, ratios), not a linear rule between repeater counts.
The many timeouts come from the simulator finding layer after layer of local rules without ever closing a loop.

RRBA (`RRBA.v`) was not run: it takes per-machine record-breaking parameters, not block words, so the decoded words give it nothing to use.
