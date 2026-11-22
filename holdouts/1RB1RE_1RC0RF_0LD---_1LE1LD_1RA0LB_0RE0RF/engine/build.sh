#!/bin/sh
# Build PR 93's engine for W (this machine mirrored, renamed, with the detour taken as one step) and its drivers.
# usage: sh build.sh /path/to/busycoq     (verify/ holding PR 93's M_1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0RDHHH.v, and
#        busycoq's core compiled up to Individual62.vo: make Makefile.coq && make -f Makefile.coq Individual62.vo)
# Needs Coq 8.18 and OCaml with ocamlfind (Ubuntu: apt-get install coq ocaml-findlib libcoq-core-ocaml-dev).
# Output: ./out/watch (the run with the halt check), ./out/validate (against direct simulation of W), ./out/f1.
set -e
BC=${1:?give the path of a busycoq checkout}
HERE=$(cd "$(dirname "$0")" && pwd)
T4="$HERE/../../../tools/coq/t4engine"
V="$BC/verify"
python3 "$T4/strip.py" "$V/M_1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0RDHHH.v" > "$HERE/engine93.v"
python3 "$HERE/patch.py" "$HERE/engine93.v" "$V/WC.v"
sed 's/Require Import T4C/Require Import WC/; s/t4ceng/wceng/' "$T4/ExtT4C.v" > "$V/ExtWC.v"
cd "$V"
coqc -Q . BusyCoq WC.v
coqc -Q . BusyCoq ExtWC.v
mkdir -p "$HERE/out"; mv wceng.ml wceng.mli "$HERE/out/"
cd "$HERE/out"
sed -i '1i module Uint63 = struct let of_int (x:int) = x end' wceng.ml
sed -i '1i module Uint63 : sig val of_int : int -> int end' wceng.mli
sed -i 's/^type int (\* AXIOM TO BE REALIZED \*)/type int = Stdlib.Int.t/' wceng.ml wceng.mli
for d in watch validate f1 peek; do
  cp "$HERE/$d.ml" .
  ocamlfind ocamlopt -package unix -linkpkg wceng.mli wceng.ml $d.ml -o $d 2>/dev/null
done
echo "built $HERE/out/watch, validate, f1, peek"
