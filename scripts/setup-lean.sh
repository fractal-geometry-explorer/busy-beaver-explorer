#!/bin/bash
# Install Lean 4.34.0 (core only, no Lake project) for bb6-holdout/lean/check.sh
set -euo pipefail
V=4.34.0
DEST=/opt/lean-$V
if [ ! -x "$DEST/bin/lean" ]; then
  cd /tmp
  curl -fsSL -o lean.zip "https://github.com/leanprover/lean4/releases/download/v$V/lean-$V-linux.zip"
  unzip -q lean.zip
  rm -rf "$DEST" && mv "lean-$V-linux" "$DEST" && rm lean.zip
fi
ln -sf "$DEST/bin/lean" /usr/local/bin/lean
cat > /etc/profile.d/lean.sh <<PROF
export LEAN=$DEST/bin/lean
export LEANLIB=$DEST/lib/lean
PROF
lean --version
