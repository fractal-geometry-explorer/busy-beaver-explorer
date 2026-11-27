#!/bin/bash
# shufscreen.sh LIST OUT [extra args of shuffle_test.py]: iterated rearrangement test per machine, resumable
list=$1; out=$2; shift 2; export OUT=$out ARGS="$*"
cat $list | xargs -P${JOBS:-4} -L1 bash -c 'grep -qF "$0 DONE" $OUT 2>/dev/null && exit 0; r=$(timeout ${TMO:-600} python3 shuffle_test.py $0 $ARGS 2>&1); { echo "$r"; echo "$0 DONE"; } >> $OUT'
