#!/bin/sh
# Compile the Rocq proofs of busycoq pull requests #110 to #112 on busycoq's BB6 branch.
# usage: sh check.sh /path/to/busycoq-checkout   (needs Coq 8.20.1; we used nixpkgs#coq_8_20)
set -e
BC=${1:?give the path of a busycoq checkout}
PRS="110 111 112"
cd "$BC"
git fetch -q https://github.com/ccz181078/busycoq +refs/heads/BB6:refs/remotes/up/BB6 \
  $(for n in $PRS; do printf ' +refs/pull/%s/head:refs/remotes/up/pr%s' $n $n; done)
git checkout -q up/BB6
cd verify
make Makefile.coq >/dev/null && make -f Makefile.coq Individual62.vo
for n in $PRS; do
  for p in $(git diff --name-only up/BB6...up/pr$n); do
    f=$(basename "$p" .v); git show up/pr$n:"$p" > "$f.v"
    thm=$(grep -oE "^Theorem (halt|nonhalt) " "$f.v" | awk '{print $2}' | tail -1)
    grep -q "^Print Assumptions" "$f.v" || printf '\nPrint Assumptions %s.\n' "$thm" >> "$f.v"
    t0=$(date +%s); coqc -Q . BusyCoq "$f.v" > "$f.log" 2>&1 && rc=0 || rc=$?
    echo "PR$n $f $thm rc=$rc $(( $(date +%s) - t0 ))s $(grep -c 'Closed under the global context' "$f.log") closed"
  done
done
# then, in verify/: coqchk -Q . BusyCoq BusyCoq.<each compiled module>
