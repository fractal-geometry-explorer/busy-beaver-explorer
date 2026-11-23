#!/bin/bash
# The checked accelerated simulator to 10^8 steps (RSimBound.lean, native_decide). About 20 minutes on this machine,
# so it is kept out of check.sh.
set -e
cd "$(dirname "$0")"
../../../tools/lean/check.sh . Machine.lean RSimBound.lean
