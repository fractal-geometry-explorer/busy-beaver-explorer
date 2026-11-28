#!/bin/bash
# runcert.sh MACHINE "CERT" TIMEOUT  -> PASS / FAIL / TIMEOUT  (busycoq's verified deciders, Coq 8.20.1)
export PATH=$HOME/.nix-profile/bin:$PATH
D=${CERT_DIR:-./cq}; B=${BUSYCOQ:?set BUSYCOQ to the verify/ folder of a compiled busycoq BB6 checkout}; mkdir -p $D
n=T$(echo "$1 $2" | md5sum | cut -c1-12)
cat > $D/$n.v <<EOF
From BusyCoq Require Import CTL62.
Lemma t: ~halts (TM_from_str "$1") c0.
Proof. solve_cert ($2). Qed.
EOF
cd $D; s=$(date +%s)
( ulimit -v 5500000; timeout ${3:-600} coqc -Q $B BusyCoq -Q $B/BigInt BigInt $n.v > $n.log 2>&1 ); rc=$?
e=$(( $(date +%s)-s ))
if [ $rc = 0 ]; then echo "PASS $e"; elif [ $rc = 124 ]; then echo "TIMEOUT $e"; elif grep -q "expected to have type" $n.log; then echo "FAIL $e"; else echo "ABORT $e rc=$rc $(tail -c 100 $n.log | tr '\n' ' ')"; fi
rm -f $D/$n.vo $D/$n.vok $D/$n.vos $D/$n.glob $D/.$n.aux
