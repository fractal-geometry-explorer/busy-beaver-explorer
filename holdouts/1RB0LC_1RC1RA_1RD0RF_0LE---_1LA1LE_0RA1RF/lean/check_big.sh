#!/bin/bash
# The long run of the checked accelerated simulator (RSimLong.lean), with compiled code loaded for native_decide
# (tools/lean/check_native.sh); RSimRun.lean is compiled with the machine so that the run is specialized to it.
set -e
cd "$(dirname "$0")"
../../../tools/lean/check_native.sh . "Machine.lean RSimRun.lean" RSimLong.lean
