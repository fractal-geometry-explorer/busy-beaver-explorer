#!/bin/sh
# Compile the Rocq proofs of busycoq pull requests #78 to #96 (DeepMind, 14-17 Nov 2026) on busycoq's BB6 branch.
# usage: sh check.sh /path/to/busycoq-checkout   (needs Coq 8.20.1; we used nixpkgs#coq_8_20)
# Fetches refs/pull/78..96/head, copies each file into verify/, appends Print Assumptions, and compiles it.
# Results of 18 Nov 2026 (BB6 at 33209bc): results.txt (seconds per file), axioms.json ([] = closed under the global context).
set -e
BC=${1:?give the path of a busycoq checkout}
cd "$BC"
git fetch -q https://github.com/ccz181078/busycoq +refs/heads/BB6:refs/remotes/up/BB6 \
  $(for n in $(seq 78 96); do printf ' +refs/pull/%s/head:refs/remotes/up/pr%s' $n $n; done)
git checkout -q up/BB6
cd verify
make Makefile.coq >/dev/null && make -f Makefile.coq Individual62.vo BigUint.vo Longitudinal.vo ES_v2.vo
for n in $(seq 78 96); do
  for p in $(git diff --name-only up/BB6...up/pr$n); do
    f=$(basename "$p" .v); git show up/pr$n:"$p" > "$f.v"
    thm=$(grep -oE "^Theorem (halt|nonhalt) " "$f.v" | awk '{print $2}' | tail -1)
    cp "$f.v" "${f}_chk.v"; printf '\nPrint Assumptions %s.\n' "$thm" >> "${f}_chk.v"
    t0=$(date +%s); coqc -Q . BusyCoq "${f}_chk.v" > "$f.log" 2>&1 && rc=0 || rc=$?
    echo "PR$n $f $thm rc=$rc $(( $(date +%s) - t0 ))s $(grep -c 'Closed under the global context' "$f.log") closed"
  done
done
