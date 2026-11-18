#!/bin/bash
# Check that each copied map (holdouts/<M>/lean/DeepMindMap.lean) computes what DeepMind's own `next` computes: run both
# for N steps from `start` and compare the states (constructor names and numbers).
# usage: tools/deepmind/orbits.sh CRYPTIDS_DIR [N]   (CRYPTIDS_DIR built as in build.sh; LEAN, LEANLIB as for tools/lean/check.sh)
set -e
CRY="$(cd "$1" && pwd)"; N0=${2:-120}
# maps whose `next` recurses down a number one at a time are slow in the interpreter once their states grow: fewer steps
declare -A STEPS=([1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LF---_0RA1LA]=7)
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
TMP="$(mktemp -d)"
LEAN=${LEAN:-lean}
if [ -z "$LEANLIB" ]; then LEANLIB="$(dirname "$(command -v "$LEAN")")/../lib/lean"; fi
"$ROOT/tools/lean/check.sh" > /dev/null
: > "$TMP/ours.out"
echo > "$TMP/theirs.lean"
for d in "$ROOT"/holdouts/*/lean/DeepMindMap.lean; do
  dir="$(dirname "$d")"; M="$(basename "$(dirname "$dir")")"
  ns=$(sed -n 's/^namespace \(H[0-9]*\)$/\1/p' "$dir/Machine.lean")
  mod="M_${M//---/HHH}"; N=${STEPS[$M]:-$N0}
  repr=$(awk '/^inductive State/,/^$/' "$d" | grep -c Repr || true)
  mkdir -p "$dir/out"
  (cd "$dir" && LEAN_PATH="$LEANLIB:$ROOT/tools/lean/out:$dir/out" "$LEAN" Machine.lean -o out/Machine.olean \
     && LEAN_PATH="$LEANLIB:$ROOT/tools/lean/out:$dir/out" "$LEAN" DeepMindMap.lean -o out/DeepMindMap.olean)
  { echo "import DeepMindMap"
    [ "$repr" = 0 ] && echo "deriving instance Repr for $ns.DM.State"
    echo "#eval IO.println (\"$M \" ++ toString ((List.range $N).map (fun n => reprStr ($ns.DM.orbit n))))"
  } > "$TMP/ours_$ns.lean"
  (cd "$dir" && LEAN_PATH="$LEANLIB:$ROOT/tools/lean/out:$dir/out" "$LEAN" "$TMP/ours_$ns.lean") >> "$TMP/ours.out"
  sed -i "1i import BusyBeaver.BB6.$mod" "$TMP/theirs.lean"
  trepr=$(awk '/^inductive State/,/^$/' "$CRY/BusyBeaver/BB6/$mod.lean" | grep -c Repr || true)
  [ "$trepr" = 0 ] && echo "deriving instance Repr for BusyBeaver.$mod.State" >> "$TMP/theirs.lean"
  echo "#eval IO.println (\"$M \" ++ toString ((List.range $N).map (fun n => reprStr ((Option.bind · BusyBeaver.$mod.next)^[n] (some BusyBeaver.$mod.start)))))" >> "$TMP/theirs.lean"
done
(cd "$CRY" && lake env lean "$TMP/theirs.lean") > "$TMP/theirs.out"
norm() { sed -E 's/[A-Za-z0-9_.]*State\.//g' "$1" | sort; }
if diff <(norm "$TMP/ours.out") <(norm "$TMP/theirs.out") > "$TMP/diff"; then
  echo "$(wc -l < "$TMP/ours.out") maps: the same states for $N0 steps (fewer where STEPS says)"
else
  cat "$TMP/diff"; echo "MISMATCH"; exit 1
fi
