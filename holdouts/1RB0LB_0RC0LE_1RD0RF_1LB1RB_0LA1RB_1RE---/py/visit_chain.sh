#!/bin/bash
# NOTE: written for the scratch directories of the session that produced the files (paths below); kept as a record.
# resumable chain of states: s_<k>.txt = word after k rounds
cd /home/user/f02/seg
export LEAN_PATH=/opt/lean-4.34.0/lib/lean:/home/user/busy-beaver-explorer/tools/lean/out:out
P=/mnt/project-files/f02/seg
prev=0
for k in 57000 80600 98700 114000 127400 139600 145300 150800 156100 161205 161206 161207 161208 161209 161210 161211 161212; do
  if [ ! -s $P/s_$k.txt ]; then
    r=$(lean --load-dynlib=nat/seg.so --run Gen.lean $P/s_$prev.txt $P/tmp_$k.txt $((k-prev)) 2>/dev/null | tail -1); sleep 12; [ -s $P/tmp_$k.txt ] || { echo "FAIL at $k" >> $P/chain.log; exit 1; }
    mv $P/tmp_$k.txt $P/s_$k.txt; echo "$k $r $(date +%T)" >> $P/chain.log
  fi
  prev=$k
done
echo CHAIN DONE >> $P/chain.log
