#!/bin/bash
# The fast engine: the same Coq definitions as build.sh's engine (T4C.v, built by build.sh in OUTDIR), extracted with
# Coq's binary numbers (positive, N, Z) realized by Zarith (Coq's ExtrOcamlZBigInt plus a few comparisons and halvings
# in ExtT4CZ.v). About 30 times faster at 10^6 fast steps and far more later; full states agree with build.sh's
# engine (zdigest.ml / cksdigest.ml, see README.md).
# usage: BUSYCOQ=/path/to/busycoq/verify coq/buildz.sh OUTDIR      (after coq/build.sh PR93.v OUTDIR)
# Needs OCaml 4.14 with zarith (Ubuntu 24.04: apt-get install coq ocaml ocaml-findlib libzarith-ocaml-dev).
set -e
HERE="$(cd "$(dirname "$0")" && pwd)"; BUSYCOQ=${BUSYCOQ:?set BUSYCOQ to busycoq/verify}
cd "$1"
cp "$HERE/ExtT4CZ.v" .
coqc -R "$BUSYCOQ" BusyCoq -R . BusyCoq ExtT4CZ.v 2>/dev/null
sed -i '1i module Uint63 = struct let of_int (x:int) = x end' t4cengz.ml
sed -i '1i module Uint63 : sig val of_int : int -> int end' t4cengz.mli
sed -i 's/^type int (\* AXIOM TO BE REALIZED \*)/type int = Stdlib.Int.t/' t4cengz.ml t4cengz.mli
for d in runz zdigest; do
  sed 's/^open T4ceng$/open T4cengz/' "$HERE/$d.ml" > $d.ml
  ocamlfind ocamlopt -O3 -package unix,zarith -linkpkg t4cengz.mli t4cengz.ml $d.ml -o $d 2>&1 | grep -i -A3 error || true
done
# cksdigest: the digest of a checkpoint of build.sh's engine (run.ml), for comparison with digest's output
cp "$HERE/sdigest.ml" "$HERE/cksdigest.ml" .
ocamlfind ocamlopt -package unix,zarith -linkpkg t4ceng.mli t4ceng.ml sdigest.ml cksdigest.ml -o cksdigest 2>&1 | grep -i -A3 error || true
ls -la runz zdigest cksdigest
