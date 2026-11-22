#!/bin/bash
# Build the Coq proof skeleton and the extracted engine for this machine.
# usage: coq/build.sh PR93.v OUTDIR
#   PR93.v  verify/M_1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0RDHHH.v of busycoq pull request 93
#           (sha256 63964df1e1da61d8d3497a0faa03ad1ffe0bf0a331dcd9da7f3957fea4930c78)
# Needs: coqc 8.20.1 with busycoq's verify/Individual62.vo on BUSYCOQ (BB6 branch, 33209bc), OCaml 4.14 + ocamlfind.
#   nix build nixpkgs#coq_8_20 nixpkgs#ocaml-ng.ocamlPackages_4_14.ocaml nixpkgs#ocaml-ng.ocamlPackages_4_14.findlib
set -e
HERE="$(cd "$(dirname "$0")" && pwd)"
PR93="$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"; OUT="$2"; BUSYCOQ=${BUSYCOQ:?set BUSYCOQ to busycoq/verify}
# M and START may be set in the environment for the other starts of the same table (see mkU.py):
#   START=B M=1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA0RF
M=${M:-1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB0LF}; START=${START:-A}
mkdir -p "$OUT"; cd "$OUT"
# 1. the proof: complete except run_ok (the engine run that would have to stop); "fast" admits run_ok
python3 "$HERE/mkU.py" "$PR93" U_$START.v $M $START 25 fast
coqc -R "$BUSYCOQ" BusyCoq U_$START.v | tail -3
# 2. the engine: the proof file's own definitions (up to run_ok), extracted to OCaml
n=$(grep -n "^Lemma run_ok" U_$START.v | cut -d: -f1)
head -n $((n-1)) U_$START.v | sed 's/^Module HU\./Module T4C./' > T4C.v
cat "$HERE/extra.v" >> T4C.v; echo "End T4C." >> T4C.v
cp "$HERE/ExtT4C.v" .
coqc -R "$BUSYCOQ" BusyCoq -R . BusyCoq T4C.v
coqc -R "$BUSYCOQ" BusyCoq -R . BusyCoq ExtT4C.v 2>/dev/null
sed -i '1i module Uint63 = struct let of_int (x:int) = x end' t4ceng.ml
sed -i '1i module Uint63 : sig val of_int : int -> int end' t4ceng.mli
sed -i 's/^type int (\* AXIOM TO BE REALIZED \*)/type int = Stdlib.Int.t/' t4ceng.ml t4ceng.mli
for d in run ev2 ev3 pk2 validateU; do
  cp "$HERE/$d.ml" .
  ocamlfind ocamlopt -O3 -package unix -linkpkg t4ceng.mli t4ceng.ml $d.ml -o $d 2>&1 | grep -i -A3 error || true
done
ls -la run ev2 ev3 pk2 validateU
