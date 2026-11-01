#!/bin/bash
# Check this machine's Lean files with the shared library (tools/lean). LEAN, LEANLIB as for tools/lean/check.sh.
set -e
cd "$(dirname "$0")"
../../tools/lean/check.sh . Machine.lean Rules.lean Blank.lean Pass.lean Front.lean Seven.lean Window.lean Return.lean Thin.lean Psi.lean Plan.lean Run7.lean Large.lean Axioms.lean
