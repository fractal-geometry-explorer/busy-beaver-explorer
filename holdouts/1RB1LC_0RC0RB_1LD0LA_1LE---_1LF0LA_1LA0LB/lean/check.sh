#!/bin/bash
# Check this machine's Lean files with the shared library (tools/lean). LEAN, LEANLIB as for tools/lean/check.sh.
set -e
cd "$(dirname "$0")"
../../../tools/lean/check.sh . Machine.lean Blank.lean Rules.lean Rebuild.lean Phase.lean Family.lean FamilyRule.lean DeltaBound.lean StepPasses.lean StepRule.lean \
  Glue.lean StepKit.lean Steps_1001h5.lean Steps_1001h7.lean Steps_11h7.lean Steps_1h5.lean Steps_001h7.lean Steps_0001h5.lean Steps_0001h7.lean
