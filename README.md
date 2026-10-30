# busy-beaver-explorer

Explorations of six-state Busy Beaver machines.

## Contents

- [`bb6-holdout/`](bb6-holdout/): research on the holdout `1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LD1RE`, one of the
  six-state machines whose halting status is open. It contains Lean 4 proofs of the mark rules, the round theorem and
  two loop theorems, certificates with independent checkers, an exhaustive check showing that no clean tape below
  2^65 reaches a halt, the research log and the programs behind it. The question is not settled there.
  - [`bb6-holdout/README.md`](bb6-holdout/README.md): what is established and how to check it
  - [`bb6-holdout/HANDOFF.md`](bb6-holdout/HANDOFF.md): state of the work and proposed next steps
  - [`bb6-holdout/notes/LAB_NOTES.md`](bb6-holdout/notes/LAB_NOTES.md): the full research log
- [`bb6-1RB1RA_1RC1LB/`](bb6-1RB1RA_1RC1LB/): work on the open machine `1RB1RA_1RC1LB_1LD0RA_---0LE_1LC0LF_1RE0LB`,
  just started: bounded runs and shift rules in Lean, observations of its run
  ([`README.md`](bb6-1RB1RA_1RC1LB/README.md), [`notes/LAB_NOTES.md`](bb6-1RB1RA_1RC1LB/notes/LAB_NOTES.md)).
- [`bb6-1RB1RA_1LC1LD/`](bb6-1RB1RA_1LC1LD/): work on the open machine `1RB1RA_1LC1LD_1LD0LB_1RE0RF_---1RD_1RA1RB`,
  just started: the machine in Lean on the shared library, bounded runs, first observations
  ([`README.md`](bb6-1RB1RA_1LC1LD/README.md), [`notes/LAB_NOTES.md`](bb6-1RB1RA_1LC1LD/notes/LAB_NOTES.md)).
- [`tools/`](tools/): machine-agnostic tooling taken from the holdout's code: a Lean library for any machine (with
  proved bounded-run evaluation), a symbolic prover that writes Lean proofs of shift rules, C and Python simulators,
  a parallel parts runner with a checked merge, an invariant finder and a proof-status page builder
  ([`tools/README.md`](tools/README.md)).
- [`pages/`](pages/): the explanatory pages (open them in a browser): the holdout's proof status
  ([`proof-status.html`](pages/proof-status.html)), summary page
  ([`closing-gap-rule-map.html`](pages/closing-gap-rule-map.html)) and mark-rule stepper, and two pages on the BB(6)
  champion found by mxdys in 2025.

## Checking the Lean proofs

The proofs need Lean 4.34.0 (core library only, no Lake). [`scripts/setup-lean.sh`](scripts/setup-lean.sh) installs
it to `/opt/lean-4.34.0` and sets `LEAN` and `LEANLIB` in `/etc/profile.d/lean.sh`. Then:

```sh
. /etc/profile.d/lean.sh
cd bb6-holdout/lean && ./check.sh      # all 21 files, under a minute
```

The shared library and the other machines: `tools/lean/check.sh`, `bb6-1RB1RA_1RC1LB/lean/check.sh` and
`bb6-1RB1RA_1LC1LD/lean/check.sh`;
`python3 tools/tests/test_tools.py` tests every tool (CI runs it on each pull request, `.github/workflows/tests.yml`).

The two loop theorems in `bb6-holdout/lean/thm/` take 13 and 40 minutes; see `bb6-holdout/README.md`.
