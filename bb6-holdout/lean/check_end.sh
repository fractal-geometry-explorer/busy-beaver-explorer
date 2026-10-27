#!/bin/bash
# Check the end-to-end theorem (run ./check.sh first):
#   1. the proved modules BB6/RouteTree.lean, BB6/CleanTree.lean, BB6/RouteExplore.lean, BB6/CleanRange.lean,
#      BB6/RouteEntry.lean, BB6/EntryTree.lean, BB6/CleanEntryTree.lean and BB6/SmallEnd.lean (seconds);
#   2. the exit and endgame trees and the run from blank tape to width 2^20, evaluated by Lean's kernel
#      (`decide +kernel`; no compiler is trusted): the generated modules thm/ExitPieces*.lean and
#      thm/EndgamePieces*.lean hold one theorem per subtree, thm/PrefixPieces*.lean one per stretch of 5,000 rounds;
#      they compile in parallel (JOBS at a time, default 4; about 1 GB of memory each), and thm/ExitTheorem.lean,
#      thm/EndgameTheorem.lean and thm/PrefixKernel.lean assemble them;
#   3. the BB6 modules compiled to a shared library (lean -c, leanc), loaded with --load-dynlib so that native_decide
#      runs the evaluated checks as native code (this adds the C compiler to the trusted base; without it the prefix
#      alone takes about an hour in Lean's interpreter);
#   4. the theorem files, in stages whose files are independent and compile JOBS at a time: the kernel-checked run to
#      width 2^20 (thm/PrefixKernel.lean), the loop through its passes (thm/LoopTheorem.lean), the halts after the
#      exit and the loop, the pass-start trees from a pass start to the next landing or clean tape at every depth
#      (thm/PassHalt.lean, the proved explorer of BB6/PassTree.lean, nothing evaluated), the eighth of the pass starts
#      with R = 6 that halt (thm/PassHaltR6.lean, six rounds on the class evaluated by the kernel), the eight classes
#      of pass starts that the mark model takes to a close at distance 0, each a halt (thm/PassHaltClasses.lean, the
#      model run on each class by the kernel), eight families of pass starts with R >= 178 at every width that halt
#      and that the pass-start tree for R >= 178 leaves open at every depth, and a full pass of the loop's chain onto
#      one (thm/PassOpenHalt.lean, the model run on the families by the kernel), the blank-tape prefix to width 2^32
#      (thm/Prefix.lean, about 4 minutes), the clean-tape tree at every depth
#      (thm/CleanTheorem.lean, the proved explorer, nothing evaluated), the clean tapes of width in [2^32, 2^41) run
#      one by one (thm/CleanDirect.lean, about 11 minutes), thm/EndToEnd.lean and thm/EndToEndDirect.lean, the routes
#      from two-marker states with their loop entries (thm/RouteTheorem.lean, thm/RouteEntryTheorem.lean,
#      thm/RouteEntryHalt.lean, nothing evaluated), the clean-tape tree with loop entries and its chain from blank
#      tape (thm/CleanEntryTheorem.lean, thm/CleanEntryHalt.lean, nothing evaluated), that chain joined to the
#      pass-start trees, with the plain clean-tape tree taken first where it resolves a clean tape
#      (thm/PassEntryHalt.lean), the same with loop entries from which the loop's chain ends at no small right end
#      (thm/CleanSmallTheorem.lean, thm/SmallEndHalt.lean, nothing evaluated), and the two together
#      (thm/OpenSmallHalt.lean); prints the axioms of the final theorems;
#   5. with them, the measure of the clean-tape trees' cut classes at 36 digits (thm/CleanMass.lean,
#      thm/CleanDirectMass.lean, thm/CleanKernelMass.lean, thm/CleanEntryMass.lean, thm/CleanEntryKernelMass.lean,
#      thm/CleanSmallMass.lean, about 5 minutes each), and with --deep also at 40 digits
#      (thm/CleanMass40.lean, thm/CleanDirectMass40.lean, about half an hour each).  No theorem about the machine uses
#      them.
# usage: LEAN=/path/to/lean LEANLIB=/path/to/lib/lean [JOBS=4] ./check_end.sh [--interpreted] [--deep]
set -e
cd "$(dirname "$0")"
LEAN=${LEAN:-lean}
LEANC=${LEANC:-$(dirname "$LEAN")/leanc}
export LEAN_PATH="$LEANLIB:$PWD/out"
JOBS=${JOBS:-4}
INTERP=""; DEEP=""
for a in "$@"; do
  case $a in --interpreted) INTERP=1 ;; --deep) DEEP=1 ;; *) echo "unknown option $a"; exit 1 ;; esac
done
for f in RouteTree CleanTree RouteExplore CleanRange RouteEntry EntryTree CleanEntryTree SmallEnd; do
  echo "== BB6/$f.lean"; $LEAN BB6/$f.lean -o out/BB6/$f.olean
done
for f in ExitStart EndgameStart PrefixBase; do echo "== thm/$f.lean"; $LEAN thm/$f.lean -o out/$f.olean; done
PIECES=$(cd thm && ls PrefixPieces*.lean ExitPieces*.lean EndgamePieces*.lean | sed 's/\.lean$//')
echo "== thm/PrefixPieces*.lean, thm/ExitPieces*.lean, thm/EndgamePieces*.lean (kernel, $JOBS at a time)"
start=$(date +%s)
printf '%s\n' $PIECES | xargs -P "$JOBS" -I{} "$LEAN" thm/{}.lean -o out/{}.olean
echo "   $(( $(date +%s) - start )) s"
DYN=""
if [ -z "$INTERP" ]; then
  MODS="Basic Cycles Rules Iter Rows Rows2 Marks Model Mid Pkt Pkt2 Gap2 Blk Contact Events PktRun Round SymForm SymRound SymSplit Meets HaltClose HaltStretch Loop Ends RouteTree CleanTree RouteExplore CleanRange RouteEntry EntryTree CleanEntryTree SmallEnd"
  mkdir -p cbuild/so
  OBJS=""
  for f in $MODS; do
    # regenerate the C code and recompile only where it changed (a module's code can change with its imports)
    $LEAN BB6/$f.lean -c cbuild/so/$f.c.new > /dev/null
    if [ ! -f cbuild/so/$f.o ] || ! cmp -s cbuild/so/$f.c.new cbuild/so/$f.c; then
      mv cbuild/so/$f.c.new cbuild/so/$f.c
      $LEANC -O2 -fPIC -DLEAN_EXPORTING -c cbuild/so/$f.c -o cbuild/so/$f.o
    else
      rm cbuild/so/$f.c.new
    fi
    OBJS="$OBJS cbuild/so/$f.o"
  done
  $LEANC -shared -o cbuild/so/libBB6all.so $OBJS
  DYN="--load-dynlib=cbuild/so/libBB6all.so"
fi
# one theorem file; its output is printed when it is done
compile() {
  local s=$(date +%s)
  if $LEAN $DYN thm/$1.lean -o out/$1.olean > out/$1.log 2>&1; then
    echo "== thm/$1.lean ($(( $(date +%s) - s )) s)"; cat out/$1.log
  else
    echo "== thm/$1.lean FAILED"; cat out/$1.log; return 1
  fi
}
export -f compile
export LEAN DYN
stage() { printf '%s\n' "$@" | xargs -P "$JOBS" -I{} bash -c 'compile {}'; }
stage PrefixKernel EndgameTheorem ExitTheorem Prefix CleanTheorem RouteTheorem
stage CleanEntryTheorem CleanSmallTheorem
DEEPMASS=""
[ -n "$DEEP" ] && DEEPMASS="CleanMass40 CleanDirectMass40"
stage $DEEPMASS CleanDirect CleanMass CleanDirectMass CleanKernelMass CleanEntryMass CleanEntryKernelMass \
  CleanSmallMass ExitHalt LoopTheorem RouteEntryTheorem
stage LoopHalt
stage EndToEnd RouteEntryHalt PassHalt PassHaltR6
stage EndToEndDirect PassHaltClasses
stage CleanEntryHalt PassOpenHalt
stage PassEntryHalt
stage SmallEndHalt
stage OpenSmallHalt
$LEAN thm/EndToEndAxioms.lean
echo "END TO END CHECKED"
