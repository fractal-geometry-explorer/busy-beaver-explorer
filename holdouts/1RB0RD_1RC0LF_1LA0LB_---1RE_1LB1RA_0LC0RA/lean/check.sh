#!/bin/bash
# Check this machine's Lean files with the shared library (tools/lean). LEAN, LEANLIB as for tools/lean/check.sh.
set -e
cd "$(dirname "$0")"
../../../tools/lean/check.sh . Machine.lean Blank.lean Rules.lean Closed.lean Exec.lean Classes.lean ExecData.lean ClassData.lean Arrive.lean Chunk0.lean Chunk1.lean Chunk2.lean Chunk3.lean Chunk4.lean Chunk5.lean Chunk6.lean Chunk7.lean Replay.lean
