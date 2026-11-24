"""Run py/blockmap.py with and without its jump across runs of equal blocks, and compare the whole lists (and sweep
counts) at every refill.  usage: check_jump.py REFILLS"""
import os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import blockmap as B
A = B.Map(B.START); J = B.Map(B.START)


def next_refill(M, usejump):
    while True:
        if not (usejump and B.jump(M)): M.fast()
        if M.left and M.left[0][0] == 0: return


for r in range(int(sys.argv[1])):
    t = time.time(); next_refill(A, False); t1 = time.time() - t
    next_refill(J, True)
    if A.sweeps != J.sweeps or B.canon_rle(A) != B.canon_rle(J):
        print('DIFFERENT at refill', r + 1); sys.exit(1)
    print(r + 1, A.sweeps, round(t1, 2), flush=True)
print('equal at all', sys.argv[1], 'refills')
