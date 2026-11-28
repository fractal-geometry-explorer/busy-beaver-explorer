#!/bin/bash
# screen.sh LIST OUT "n m K R" ...   one line per (machine, configuration); resumable (skips lines already in OUT)
list=$1; out=$2; shift 2
export OUT=$out TMO=${TMO:-60} MAXST=${MAXST:-6000000}
for cfg in "$@"; do while read tm; do echo "$tm $cfg"; done < $list; done |
xargs -P${JOBS:-4} -L1 bash -c 'key="$0 n=$1 m=$2 K=$3 R=$4${START:+ start=$START}${NODROP:+ nodrop}"; grep -qF "$key:" $OUT 2>/dev/null && exit 0; r=$(RAD=$4 timeout $TMO ./patcount $0 $1 $2 $3 $MAXST | head -1); echo "$key: ${r:-TIMEOUT}" >> $OUT'
