"""Checks of py/qsim.py against plain simulation.

usage: python3 qsim_check.py direct NSAMPLES   # level 1 (macro rules, no jumps) against a cell-by-cell simulator:
                                               # tape and step count at every visit of the right end
       python3 qsim_check.py jumps STEPS       # jumps on against jumps off: the tape at every visit of the right end
                                               # the jumping run stops at, up to STEPS steps (3e10 takes some minutes)
"""
import sys, time
from qsim import Sim


def direct(nsamples):
    s = Sim(accel=False)
    T = s.T
    tape = {}; pos = 0; st = 0; n = 0; hi = 0; lo = 0
    for k in range(nsamples):
        s.trip()
        while True:          # the plain machine, to the next time state B has only blank cells from the head on
            tr = T[st][tape.get(pos, 0)]
            tape[pos] = tr[0]; pos += tr[1]; st = tr[2]; n += 1
            hi = max(hi, pos); lo = min(lo, pos)
            if st == 1 and all(tape.get(i, 0) == 0 for i in range(pos, hi + 1)): break
        cells = ''.join(str(tape.get(i, 0)) for i in range(lo, pos)).lstrip('0')
        if cells != s.cells().lstrip('0') or n != s.steps:
            print('MISMATCH at visit', k, 'plain steps', n, 'qsim steps', s.steps)
            return False
    print('ok:', nsamples, 'visits of the right end,', n, 'steps, tape and step count equal at each')
    return True


def jumps(N):
    r = Sim(accel=False); ref = {}
    t0 = time.time()
    while r.steps < N:
        r.trip(); ref[r.steps] = hash(r.cells())
    print('without jumps: %d visits, %.1f s' % (r.nraw, time.time() - t0))
    a = Sim(accel=True); logs = []
    a.log = logs.append
    t0 = time.time(); bad = 0
    while a.steps < N:
        a.trip(); a.sample(); a.check_pending(); a.try_jump()
        if a.steps > N: break
        if a.steps not in ref or ref[a.steps] != hash(a.cells()):
            if a.pending is None:       # while a jump is still being validated the state may be rolled back
                bad += 1
    print('with jumps: %d visits simulated, %d jumps, %d rollbacks, %d mismatches, %.1f s' % (
        a.nraw, a.njump, sum(1 for l in logs if l.startswith('rollback')), bad, time.time() - t0))
    return bad == 0


if __name__ == "__main__":
    ok = direct(int(float(sys.argv[2]))) if sys.argv[1] == 'direct' else jumps(int(float(sys.argv[2])))
    sys.exit(0 if ok else 1)
