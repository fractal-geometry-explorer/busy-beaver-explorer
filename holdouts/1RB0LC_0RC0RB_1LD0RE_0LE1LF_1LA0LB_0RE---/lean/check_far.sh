#!/bin/bash
# The long bounded run (BoundFar.lean, about 40 minutes), with compiled code loaded for native_decide (tools/lean/check_native.sh).
set -e
cd "$(dirname "$0")"
../../../tools/lean/check_native.sh . "Machine.lean Family.lean Bound.lean" BoundFar.lean
