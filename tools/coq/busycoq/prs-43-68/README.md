# Busycoq pull requests #43 to #68, compiled here (21 November 2026)

Every Rocq proof about a holdout in busycoq PRs #43 to #68 (github.com/ccz181078/busycoq, all open and unreviewed,
heads unchanged since 3 to 10 November) was compiled on busycoq's BB6 branch (33209bc) with Coq 8.20.1 from
nixpkgs. PR #65 decides no holdout and was skipped.

- **44 machine proofs compile**: 34 never halt, 10 halt (`results.json`, `compile_times.txt`).
- Each is re-stated by an audit file (`audit/Audit_<i>.v`, one per line of `spec.txt`) as
  `[~] halts (TM_from_str "<name in our 608>") c0` on Individual62's own `halts` and `c0`, and proved by
  `exact` from the PR's theorem, so the table, the start and the notion of halting are busycoq's.
  `Print Assumptions` on the audit lemma: 42 are closed under the global context; PR #44's proof of
  `1RB---_1LC1RF_0LE0RD_0RB0LC_1RD0LD_0RC0RA` and PR #58 use functional extensionality.
- Four proofs (PR #44's `1RB---_1LC1RF_...`, #61, #62, #63) state halting with a second instance of busycoq's `TM`
  functor on the same context BB62 (through `LongLoop62` or the PR's `RWLAccT62`). Their audit files prove that the
  copy's `step`, `multistep` and `halts` agree with Individual62's and restate the result on Individual62's.
- PR #58 proves the mirror image and transfers it with `flip_halts_c0`; the audit uses the 608 name directly.
- PR #59's three halts rest on one `vm_cast_no_check` computation, checked by the kernel at `Qed`.
- 32 of these machines were open here and are now decided (outside); the other 12 were already decided by
  DeepMind's compiled Lean proofs or by our own Coq proof.

## PR #60: framework and sample jobs only

PR #60's two halting proofs are 523 jobs (Lopsided Camper, `1RB---_0RC0RD_1LD1RB_0LE0LC_1RA0LF_1LD1LE`, about
280 core-hours) and 313 jobs (`1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA`, about 275 core-hours) of
`native_compute`. We built Coq 8.20.1 with `-native-compiler yes` (nixpkgs override, OCaml 4.14.5, no flambda),
compiled both frameworks and ran four jobs:

| job | seconds here | seconds in the PR's evidence |
|---|---|---|
| LopsidedCamper J0000 | 2584 | 1962 |
| LopsidedCamper J0522 (ends at the halt) | 224 | 155 |
| Halt_1RB0LF_1RC1RA JHalt (ends at the halt) | 1 | 1.25 |
| Halt_1RB0LF_1RC1RA J0202 | 891 | 743 |

All pass. The full runs would take about 7 days on this 4-core container, so both machines stay open here.

## Reproduce

`bash check.sh /path/to/busycoq-checkout` (Coq 8.20.1 on PATH). It fetches the PR heads, builds each PR in its own
copy of `verify/`, then the audit files.
