#!/bin/bash
# Run one shard of busycoq PR 60's native_compute jobs.  usage: bash /mnt/project-files/pr60-run/run_shard.sh S3 [PARALLEL]
# Safe to restart: a job whose .vo is already in results/ is skipped. Each finished job's .vo and .log is copied to
# results/<dir>/ at once, so work survives the container. A failed job leaves results/<dir>/<job>.FAILED.
set -u
S=$1; P=${2:-$(nproc)}
B=/mnt/project-files/pr60-run; W=$HOME/pr60; C=/nix/store/d4fx1306cl2s9rfxm2avl0pr9ylkhm5m-coq-8.20.1
if [ ! -x $C/bin/coqc ]; then
  for r in /nix/store/r3hvhzl5fxhrgn0rfy5g7rda17702pj4-glibc-2.44-57 /nix/store/gb06ygpj4a0binvb2i92k20hzz1fl6w0-ocaml-4.14.5 \
           /nix/store/c8m3w962mpi4nhb2bl7zk4xnqxhq53ln-ocaml4.14.5-findlib-1.9.8 /nix/store/f10r84amd0qjc5dp5k4abrmp8f4wx584-gmp-with-cxx-6.3.0 \
           /nix/store/cwdmgyxipaj6clwzsrz8m9prl8wqvcbq-ocaml4.14.5-zarith-1.14 /nix/store/j9jglmxykh37ky4ys613vc1wnac7h6f1-csdp-6.1.1; do
    nix-store -r $r > /dev/null || { echo "cannot fetch $r"; exit 1; }
  done
  xz -dc $B/coq-native.nar.xz | nix-store --import > /dev/null || { echo "import of native Coq failed"; exit 1; }
fi
. $B/natenv.sh
if [ ! -f $W/verify/Individual62.vo ]; then mkdir -p $W && xz -dc $B/framework.tar.xz | tar -xf - -C $W; fi
cd $W/verify; ulimit -s unlimited
export OCAMLPARAM='_,O3=1,inline=1000,unbox-closures=1' B S
run1() {
  d=$1; j=$2; R=$B/results/$d; mkdir -p $R
  [ -f $R/$j.vo ] && exit 0
  s=$(date +%s)
  if coqc -Q . BusyCoq -Q ./BigInt BigInt -native-compiler yes $d/jobs/$j.v > $d/jobs/$j.log 2>&1; then
    cp $d/jobs/$j.vo $R/$j.vo.tmp && mv $R/$j.vo.tmp $R/$j.vo; cp $d/jobs/$j.log $R/$j.log
    echo "ok $d $j $(( $(date +%s) - s ))s $S" >> $B/results/log.txt
  else
    cp $d/jobs/$j.log $R/$j.FAILED; echo "FAILED $d $j $S" >> $B/results/log.txt
  fi
}
export -f run1
xargs -P "$P" -L 1 bash -c 'run1 "$0" "$1"' < $B/shards/$S.txt
echo "shard $S finished $(date -u +%FT%TZ) $S" >> $B/results/log.txt
