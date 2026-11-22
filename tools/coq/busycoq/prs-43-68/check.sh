#!/bin/bash
# Compile the Rocq proofs of busycoq pull requests #43 to #68 on busycoq's BB6 branch, then the audit files.
# usage: bash check.sh /path/to/busycoq-checkout     (needs Coq 8.20.1; we used nixpkgs#coq_8_20)
# Each PR is built in its own copy of verify/ (PRs 61-63 share RWLAccT.v and PR_LongTranslatedCycler.v).
# PR 60's two proofs are 523 and 313 native_compute jobs (about 280 and 275 core-hours): this script builds
# their framework files only; see README.md for the sample jobs we ran. PR 65 decides no holdout and is skipped.
# audit/Audit_<i>.v (one per line of spec.txt) restates each result on Individual62's halts, c0 and
# TM_from_str "<the machine's name in our 608>" and prints its assumptions.
set -e
BC=${1:?give the path of a busycoq checkout}
HERE=$(cd "$(dirname "$0")" && pwd)
PRS="43 44 45 46 47 48 49 50 51 52 53 54 55 56 57 58 59 60 61 62 63 64 66 67 68"
cd "$BC"
git fetch -q https://github.com/ccz181078/busycoq +refs/heads/BB6:refs/remotes/up/BB6 \
  $(for n in $PRS; do printf ' +refs/pull/%s/head:refs/remotes/up/pr%s' $n $n; done)
git checkout -q up/BB6
(cd verify && make Makefile.coq >/dev/null && make -f Makefile.coq Individual62.vo Longitudinal.vo ES_v3.vo ES_v2.vo SimplTape.vo DivModCases.vo BinaryCounter_v2.vo LongLoop.vo)
ulimit -s unlimited
for n in $PRS; do
  W=$(mktemp -d)/verify; cp -r verify "$W"
  files=$(git diff --name-only up/BB6...up/pr$n | grep '\.v$' | grep -v /jobs/ | sed 's|^verify/||')
  for p in $files; do mkdir -p "$W/$(dirname $p)"; git show up/pr$n:verify/$p > "$W/$p"; done
  for p in $(cd "$W" && coqdep -Q . BusyCoq -sort $files | tr ' ' '\n' | sed -E 's/\.vo?$//;s|^\./||'); do
    echo "$files" | grep -qx "$p.v" || continue
    t0=$(date +%s); (cd "$W" && coqc -Q . BusyCoq "$p.v" > "$p.log" 2>&1) && rc=0 || rc=$?
    echo "PR$n $p rc=$rc $(( $(date +%s) - t0 ))s"
  done
  i=0; while read N F THM TMP K NAME; do i=$((i+1)); [ "$N" = "$n" ] || continue
    cp "$HERE/audit/Audit_$i.v" "$W/"; (cd "$W" && coqc -Q . BusyCoq Audit_$i.v > Audit_$i.log 2>&1) && rc=0 || rc=$?
    echo "  audit $i $NAME rc=$rc $(grep -q 'Closed under the global context' $W/Audit_$i.log && echo closed || grep -A1 '^Axioms:' $W/Audit_$i.log | tail -1)"
  done < "$HERE/spec.txt"
done
