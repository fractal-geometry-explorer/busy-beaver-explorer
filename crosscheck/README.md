# Cross-check of the 85 decided holdouts (22 November 2026)

85 of the 608 BB(6) holdouts are marked decided in this repository (`decision` in their `status.json`): 53 never
halt and 32 halt. Every one of them rests on a Rocq proof, either a pull request on ccz181078/busycoq or one of our
own Coq files (the Lean proofs and DeepMind's Lean files are additional). This folder checks those results again with
methods that share no code with the proofs or with `tools/`.

## Result

**No discrepancy found.** For 84 of the 85 machines a Coq 8.20.1 build here proves exactly the claimed statement
`halts (TM_from_str "<full TNF name>") c0` (or its negation) on busycoq's own definitions, and my own parser agrees with
busycoq's `TM_from_str` on every transition of all 85 tables. That includes
`1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0LC---` (busycoq PR 100, a 4.5-hour build, closed under the global context,
[`coq/results_long.txt`](coq/results_long.txt)). The last one, `1RB0LE_1RC1RB_1LD0RA_1LA1LC_0LC0LF_0RB---` (PR 102,
about 14 hours), compiled here before (18 November); its audited rebuild was cut off by a container restart and is
running again.
A new direct simulator finds no halt in the first 10^10 steps of any of the 85, which agrees with every claim (each
halting proof puts the halt far beyond 10^11 steps).

Per machine: [`results.json`](results.json) (decision, the audits that prove it, the table check, the simulation).

## What was checked

1. **The table.** [`tnf.py`](tnf.py) parses a TNF name independently, and [`gen_table_check.py`](gen_table_check.py)
   writes [`coq/TableCheck.v`](coq/TableCheck.v): for each of the 85 machines, a lemma
   `forall q s, TM_from_str "<name>" (q, s) = table (q, s)` with the 12 transitions written out explicitly. It compiles
   in 3 s on busycoq's BB6 branch (33209bc). A control with one wrong transition fails. So `TM_from_str` reads every
   name the way the bbchallenge convention does, and an audit against `TM_from_str "<name>"` is an audit against the
   intended machine.

2. **The statement.** [`coq/audit_pr.sh`](coq/audit_pr.sh) builds a pull request's files in a fresh copy of BB6's
   `verify/`, then an audit file that imports busycoq's `Individual62` (its `halts`, `c0`, `TM_from_str`) and proves
   `[~] halts (TM_from_str "<name>") c0` by `exact` from the PR's theorem, then `Print Assumptions`. So the start (state
   A, blank tape), the meaning of halting and the table are busycoq's, whatever the proof file defines. A control with
   one transition changed is rejected by the type checker.
   - **PRs 78 to 107** (DeepMind and valu42): 27 machines, all pass, all closed under the global context except PR 81
     (`1RB---_1RC0LE_1RD1RF_1LB0LB_0RD0LD_0RC0RA`), whose only assumptions are Coq's standard axioms for primitive 63-bit
     integers (`Uint63`). The earlier compile of these PRs (`tools/coq/busycoq/prs-78-96`, `prs-97-107`) checked
     `Print Assumptions` of each PR's own `tm`; this is the first restatement on the 608 names
     ([`coq/results_78_107.txt`](coq/results_78_107.txt)).
   - **Our own proofs** as submitted to busycoq (PRs 69 to 76, 108, 109): 10 machines, all pass, all closed
     ([`coq/results_own.txt`](coq/results_own.txt)). They cover the machines whose status rests on our Lean proofs too.
   - **PRs 43 to 68**: the audit files of `tools/coq/busycoq/prs-43-68` were rebuilt from scratch: 44 audits for 41
     machines, all pass ([`coq/results_43_68_rerun.txt`](coq/results_43_68_rerun.txt)). Two use functional
     extensionality, as recorded before (PR 44's `1RB---_1LC1RF_0LE0RD_0RB0LC_1RD0LD_0RC0RA` and PR 58's
     `1RB1LC_0RC0RB_1LD0LA_1LE---_1LF1RA_1LA1LC`).
   - Every audited verdict matches the `decision` in `status.json`.

3. **Hidden weak spots.** [`scan_v.py`](scan_v.py) and [`scan_lean.py`](scan_lean.py) scan every Coq file of PRs 43 to 109
   and of this repository, and every Lean file of the decided machines and of `tools/lean`:
   - No `Admitted`, `admit`, `Axiom`, `sorry`, disabled guard/universe/positivity checking, `implemented_by` or
     `extern`. No file redefines `halts`, `c0`, `TM_from_str` or the step relation (PR 61's `RWLAccT.v` has a local
     `step` on its own accelerated states, and its audit bridges it).
   - `vm_cast_no_check` (many files) is rechecked by the kernel at `Qed`.
   - Two of our own Coq proofs (PR 74, `1RB0RC_1LA0LD_1RB0RD_1LE0RF_0LB0RB_1RC---`, and PR 75,
     `1RB1LE_0LC1RE_---1LD_0RD1LA_0RF1RF_1RA0LB`) use `native_cast_no_check`, which trusts the OCaml native compiler
     and does not show in `Print Assumptions`. The Coq here is built without the native compiler
     (`COQ_NATIVE_COMPILER_DEFAULT=no`), so it fell back to the kernel's bytecode machine: both are checked here without
     that trust.
   - The Lean proofs use `native_decide` (bounded runs in every `Blank.lean`, and the long computations of our own
     Lean proofs). That trusts Lean's compiler. Every machine whose verdict uses a Lean proof also has a Coq proof
     audited above, so no verdict depends on `native_decide` alone.
   - Each `DeepMind.lean` contains one `axiom`: a labelled citation of DeepMind's theorem. No other file uses it.

4. **The runs.** [`sim.c`](sim.c) is a new direct simulator (it reproduces BB(5): 47,176,870 steps, 4,098 ones). All
   85 machines run 10^10 steps without halting ([`sim_1e10.txt`](sim_1e10.txt)). For the 53 non-halting machines this
   is only a sanity check; for the 32 halting ones it agrees with every claim (the earliest claimed halt is beyond
   10^11 steps, most far beyond 10^100).

5. **Two proof systems.** 11 machines have both a DeepMind Lean proof (compiled here earlier, Lean v4.35.0-rc4) and an
   audited Rocq proof, and they agree. Ten of the Rocq proofs are by Alex Havrilla of DeepMind (PRs 47 x2, 48, 49 x2,
   50 x2, 51, 52, 53), so they are two checkers rather than two independent arguments; only
   `1RB1RA_0LC0RA_1RC1LD_0LB1LE_1LF0RC_---0LD` (PR 44, Alk) has proofs by different authors.

## What was not done

- **Reaching the halts by a second simulator.** [`chainsim.py`](chainsim.py) is a block macro machine with chain steps
  and big-integer counts (exact, also checked on BB(5)). In 20 s per block size it reaches 10^8 to 10^14 steps, far
  short of the claimed halts, which need the nested-counter acceleration the proofs themselves build. Partial results:
  [`chainsim_partial.jsonl`](chainsim_partial.jsonl). A faster engine in C with counter rules would be the next step.
- **Reviewing the mathematics** of each proof. The kernel checks that; the audit checks that what it checks is the
  claim.

## A bug fixed on the way

`tools/coq/busycoq/prs-43-68/check.sh` sorted the files with `coqdep -sort` and stripped `.vo`, but the coqdep of Coq
8.20.1 prints `.v` names, so the script compiled none of the PR files and every audit failed with "Cannot find a
physical path". The sed now strips `.v` or `.vo`. The results recorded on 21 November were not affected (they were
produced before), but the script as committed could not reproduce them.

## Reproduce

```sh
nix profile install nixpkgs#coq_8_20          # Coq 8.20.1
git clone https://github.com/ccz181078/busycoq bc && cd bc && git checkout BB6
git fetch origin +refs/heads/BB6:refs/remotes/up/BB6 $(for n in $(seq 43 109); do printf ' +refs/pull/%s/head:refs/remotes/up/pr%s' $n $n; done)
(cd verify && make Makefile.coq && make -f Makefile.coq Individual62.vo Longitudinal.vo ES_v2.vo BigUint.vo Helper.vo)
python3 gen_table_check.py decided.txt > coq/TableCheck.v && cp coq/TableCheck.v bc/verify/ && (cd bc/verify && coqc -Q . BusyCoq TableCheck.v)
while read N F T; do coq/audit_pr.sh bc $N $F $T; done < coq/spec_78_107.txt
while read N F T; do coq/audit_pr.sh bc $N $F $T; done < coq/spec_own.txt
bash ../tools/coq/busycoq/prs-43-68/check.sh bc
gcc -O2 -o sim sim.c && while read m; do echo "$m $(./sim $m 10000000000)"; done < decided.txt
```
`spec_78_107.txt` leaves out PRs 100 and 102 (4 and 14 hours); run them as `coq/audit_pr.sh bc 100
M_1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0LCHHH halt` and the same for 102 with `M_1RB0LE_1RC1RB_1LD0RA_1LA1LC_0LC0LF_0RBHHH`.
