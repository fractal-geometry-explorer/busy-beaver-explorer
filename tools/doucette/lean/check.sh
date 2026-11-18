#!/bin/bash
# Check the generic shift identity (no dependencies beyond Lean core).
set -e
cd "$(dirname "$0")"
${LEAN:-lean} Shift.lean
echo "ALL CHECKED"
