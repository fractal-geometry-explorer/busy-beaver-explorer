#!/bin/sh
# Build the T4 engine from busycoq PR 93 and compile the two OCaml drivers.
# usage: sh build.sh /path/to/busycoq
#   The checkout must hold PR 93's verify/M_1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0RDHHH.v with its dependencies
#   compiled (git fetch https://github.com/ccz181078/busycoq refs/pull/93/head; then make in verify/).
# Needs Coq 8.18, OCaml with ocamlfind. Output: ./out/run and ./out/validate.
set -e
BC=${1:?give the path of a busycoq checkout}
HERE=$(cd "$(dirname "$0")" && pwd)
V="$BC/verify"
python3 "$HERE/strip.py" "$V/M_1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0RDHHH.v" > "$HERE/engine93.v"
python3 "$HERE/patch.py" "$HERE/engine93.v" "$V/T4C.v"
cp "$HERE/ExtT4C.v" "$V/"
cd "$V"
coqc -Q . BusyCoq -Q ./BigInt BigInt T4C.v
coqc -Q . BusyCoq -Q ./BigInt BigInt ExtT4C.v
mkdir -p "$HERE/out"; mv t4ceng.ml t4ceng.mli "$HERE/out/"
cd "$HERE/out"
# The extraction leaves Coq's primitive 63-bit integers abstract; the engine never uses them, so realize them as int.
sed -i '1i module Uint63 = struct let of_int (x:int) = x end' t4ceng.ml
sed -i '1i module Uint63 : sig val of_int : int -> int end' t4ceng.mli
sed -i 's/^type int (\* AXIOM TO BE REALIZED \*)/type int = Stdlib.Int.t/' t4ceng.ml t4ceng.mli
for d in run validate; do
  cp "$HERE/$d.ml" .
  ocamlfind ocamlopt -O3 -package unix -linkpkg t4ceng.mli t4ceng.ml $d.ml -o $d 2>/dev/null
done
echo "built $HERE/out/run and $HERE/out/validate"
