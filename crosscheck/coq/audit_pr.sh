#!/bin/bash
# Compile one busycoq PR proof on busycoq's BB6 branch and restate it on Individual62's halts, c0, TM_from_str.
# usage: audit_pr.sh BUSYCOQ_CHECKOUT PR FILE THEOREM     (Coq 8.20.1 on PATH; the checkout has refs up/BB6, up/prN)
# Every .v file the PR adds (except PR 60's jobs/) is copied into a fresh copy of verify/ and compiled in
# dependency order; then Audit_FILE.v states [~] halts (TM_from_str "<name>") c0 and proves it by exact.
set -u
BC=$1; N=$2; F=$3; THM=$4
NAME=$(echo "${F#M_}" | sed 's/HHH/---/g')
W=$(mktemp -d)/verify; cp -r "$BC/verify" "$W"; cd "$W"
files=$(git -C "$BC" diff --name-only up/BB6...up/pr$N | grep '\.v$' | grep -v /jobs/ | sed 's|^verify/||')
for p in $files; do mkdir -p "$(dirname $p)"; git -C "$BC" show up/pr$N:verify/$p > $p; done
case $THM in nonhalt|*.nonhalt) NEG="~ "; KIND=nonhalt;; *) NEG=""; KIND=halt;; esac
cat > Audit_$F.v <<EOV
From BusyCoq Require Import Individual62.
From BusyCoq Require $F.
Require Import String.
Definition target : TM := TM_from_str "$NAME".
Lemma audit : ${NEG}halts target c0.
Proof. exact $F.$THM. Qed.
Print Assumptions audit.
EOV
ulimit -s unlimited
t0=$(date +%s); rc=0
for p in $(coqdep -Q . BusyCoq -sort $files | tr ' ' '\n' | sed -E 's/\.vo?$//;s|^\./||'); do
  echo "$files" | grep -qx "$p.v" || continue
  coqc -Q . BusyCoq "$p.v" > "$p.log" 2>&1 || { rc=$?; tail -3 "$p.log" | sed 's/^/    /'; }
done
coqc -Q . BusyCoq Audit_$F.v > Audit.log 2>&1; arc=$?
ax=$(grep -q 'Closed under the global context' Audit.log && echo closed || (sed -n '/^Axioms:/,$p' Audit.log | tr '\n' ' ' | cut -c1-300))
echo "PR$N $NAME $KIND proof_rc=$rc audit_rc=$arc $(( $(date +%s) - t0 ))s [$ax]"
[ $arc -ne 0 ] && tail -5 Audit.log | sed 's/^/    /'
rm -rf "$(dirname "$W")"
