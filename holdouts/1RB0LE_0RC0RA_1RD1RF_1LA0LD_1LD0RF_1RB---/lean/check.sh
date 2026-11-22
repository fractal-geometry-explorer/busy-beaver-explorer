#!/bin/bash
# Check this machine's Lean files with the shared library (tools/lean). LEAN, LEANLIB as for tools/lean/check.sh.
set -e
cd "$(dirname "$0")"
../../../tools/lean/check.sh . Machine.lean Blank.lean Rules.lean Route.lean Chain.lean Rebuild.lean Front.lean Transfer.lean Copy.lean CopyS1.lean CopyS2.lean CopyS3.lean CopyS4.lean CopyS5.lean CopyS6.lean CopyS7.lean CopyS8.lean
