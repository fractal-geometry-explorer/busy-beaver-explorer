#!/bin/sh
# Build the hint-taking native deciders from busycoq's BB6 branch (tested with Coq 8.18.0, OCaml 4.14).
# usage: sh build.sh /path/to/busycoq-BB6-checkout     (git checkout of the BB6 branch, commit 33209bc)
set -e
V=${1:?path to a busycoq BB6 checkout}/verify
HERE=$(cd "$(dirname "$0")" && pwd)
cp "$HERE/IndHint_inf.v" "$HERE/RWLAcc_inf.v" "$V/"
cd "$V"
coq_makefile -Q . BusyCoq -o Makefile.coq $(ls *.v) >/dev/null
make -f Makefile.coq -j4 Inductive.vo BBinf.vo RWLAcc.vo
coqc -Q . BusyCoq IndHint_inf.v      # writes IndHint.ml(i)
coqc -Q . BusyCoq RWLAcc_inf.v       # writes RWLAccX.ml(i)
echo 'let () = IndHint.exec (Array.to_list Sys.argv |> List.tl)' > hint_main.ml
echo 'let () = RWLAccX.rexec (Array.to_list Sys.argv |> List.tl)' > rmain.ml
ocamlfind ocamlopt -O2 -package coq-core.kernel -linkpkg IndHint.mli IndHint.ml hint_main.ml -o "$HERE/hdecider"
ocamlfind ocamlopt -O2 -package coq-core.kernel -linkpkg RWLAccX.mli RWLAccX.ml rmain.ml -o "$HERE/rdecider"
