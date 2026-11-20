"""Set digit IDX (default 1, the oldest segment) of a state to K blocks and run on with lean.advance, to see what
that digit running out does (20 November 2026).

    python3 py/probe.py b2 ../data/b2_lean_last.txt 0 14000        # b2: oldest segment -> 0
    python3 py/probe.py b1 ../data/b1_lean_last.txt 0 14000 2      # b1: second segment -> 0
"""
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import lean
mach, line_file, k, secs = sys.argv[1], sys.argv[2], int(sys.argv[3]), float(sys.argv[4])
idx = int(sys.argv[5]) if len(sys.argv) > 5 else 1
lean.C.use(mach)
st, T, nsw = lean.parse_shown(open(line_file).readline())
dig = list(st[1]); w, r = dig[idx]
print('orig far:', lean.far_view(st, 6), flush=True)
dig[idx] = (w, k)
st = (st[0], dig, st[2], st[3])
lean.C.register(st)
print('start far:', lean.far_view(st, 6), flush=True)
try:
    st, T, nsw, P = lean.advance(st, T, nsw, None, seconds=secs, log=sys.stdout)
    print('END far:', lean.far_view(st, 8), '%.4e' % T, flush=True)
except Exception as e:
    print('EXC', type(e).__name__, e, flush=True)
