#!/bin/bash
# The long bounded run (BoundBig.lean), with compiled code loaded for native_decide (tools/lean/check_native.sh).
set -e
cd "$(dirname "$0")"
../../../tools/lean/check_native.sh . "Machine.lean Rules.lean Dec.lean Drain.lean Bound.lean" BoundBig.lean
