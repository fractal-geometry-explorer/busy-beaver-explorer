# busy-beaver-explorer

Explorations of six-state Busy Beaver machines.

## Contents

- [`bb6-holdout/`](bb6-holdout/): research on the holdout `1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LD1RE`, one of the
  six-state machines whose halting status is open. It contains Lean 4 proofs of the mark rules, the round theorem and
  two loop theorems, certificates with independent checkers, an exhaustive check showing that no clean tape below
  2^61 reaches a halt, the research log and the programs behind it. The question is not settled there.
  - [`bb6-holdout/README.md`](bb6-holdout/README.md): what is established and how to check it
  - [`bb6-holdout/HANDOFF.md`](bb6-holdout/HANDOFF.md): state of the work and proposed next steps
  - [`bb6-holdout/notes/LAB_NOTES.md`](bb6-holdout/notes/LAB_NOTES.md): the full research log
- [`pages/`](pages/): the explanatory pages (open them in a browser): the holdout's summary page
  ([`closing-gap-rule-map.html`](pages/closing-gap-rule-map.html)) and mark-rule stepper, and two pages on the BB(6)
  champion found by mxdys in 2025.

## Checking the Lean proofs

The proofs need Lean 4.34.0 (core library only, no Lake). [`scripts/setup-lean.sh`](scripts/setup-lean.sh) installs
it to `/opt/lean-4.34.0` and sets `LEAN` and `LEANLIB` in `/etc/profile.d/lean.sh`. Then:

```sh
. /etc/profile.d/lean.sh
cd bb6-holdout/lean && ./check.sh      # all 21 files, under a minute
```

The two loop theorems in `bb6-holdout/lean/thm/` take 13 and 40 minutes; see `bb6-holdout/README.md`.
