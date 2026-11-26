#!/bin/sh
# Check a generated segmented replay.  usage: build.sh DIR [JOBS]
# DIR holds Map.v, J*.v and Final.v as written by segreplay.py (coq, segs).  Needs coqc 8.20 with the native
# compiler (the J files use native_compute; generate them with --vm to use vm_compute instead, about 10x slower).
# Prints one line per segment and "FINAL ok" when Final.v is accepted.
set -e
T=$(cd "$(dirname "$0")" && pwd); D=$1; J=${2:-4}
F="-Q $T/coq SegReplay -Q $D M"
q() { grep -v "native-compiler\|coqnative\|deprecated\|initial state" || true; }
[ -f "$T/coq/Core.vo" ] && [ -d "$T/coq/.coq-native" ] || (cd "$T/coq" && coqc -native-compiler yes -Q . SegReplay Core.v 2>&1 | q)
coqc -native-compiler yes $F "$D/Map.v" 2>&1 | q
ls "$D"/J*.v | xargs -P "$J" -I{} sh -c 's=$(date +%s); coqc -native-compiler yes '"$F"' {} 2>&1 | grep -v "native-compiler\|coqnative\|deprecated\|initial state"; [ -f {}o ] && echo "$(basename {} .v) ok $(( $(date +%s) - s )) s" || echo "$(basename {} .v) FAILED"'
coqc $F "$D/Final.v" 2>&1 | q
[ -f "$D/Final.vo" ] && echo "FINAL ok"
