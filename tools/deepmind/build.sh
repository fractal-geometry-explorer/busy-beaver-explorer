#!/bin/bash
# Build and audit google-deepmind/cryptids (commit 3647718) proofs for machines on our holdout list.
# Usage: tools/deepmind/build.sh [workdir]   (default /tmp/dm). Needs ~6 GB disk, ~1 h on 4 cores.
# If cache.mathlib.org is reachable, `lake exe cache get` replaces the Mathlib build from source.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
W=${1:-/tmp/dm}; mkdir -p "$W"; cd "$W"
V=4.35.0-rc4
command -v elan >/dev/null || { curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none; }
source ~/.elan/env
if ! elan toolchain list | grep -q "v$V"; then
  # release.lean-lang.org may be blocked; take the toolchain from the GitHub release instead.
  curl -sSfL -o lean.tar.zst "https://github.com/leanprover/lean4/releases/download/v$V/lean-$V-linux.tar.zst"
  python3 -c "import zstandard" 2>/dev/null || pip install -q zstandard
  python3 -c "import zstandard,tarfile;tarfile.open(fileobj=zstandard.ZstdDecompressor().stream_reader(open('lean.tar.zst','rb')),mode='r|').extractall('tc')"
  elan toolchain link "leanprover/lean4:v$V" "tc/lean-$V-linux"
fi
[ -d cryptids ] || git clone -q https://github.com/google-deepmind/cryptids.git
cd cryptids && git checkout -q 3647718
lake exe cache get || echo "Mathlib cache unavailable: building Mathlib from source"
time lake build $(cat "$HERE/targets.txt") $(cat "$HERE/maps.txt")
lake env lean "$HERE/Audit.lean"
lake env lean "$HERE/AuditMaps.lean"
