"""Run the macro map from the first tick boundary of the blank-tape run for SECONDS of wall time; print every event
(the state before and after, and its steps), and the state once a minute.

usage: python3 longrun.py SECONDS [MACHINE] [verify] [checkshifted=N]
"""
import os
import sys
import time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import macro as M  # noqa: E402


def summ(st):
    return '%d K=%d xs=%s ss=%s tail=%s' % (st[0], len(st[1]), st[1], st[2], st[3])


def main():
    TL = float(sys.argv[1])
    for a in sys.argv[2:]:
        if '_' in a: M.use_machine(a)
        if a == 'verify': M.VERIFY = True
        if a.startswith('checkshifted='): M.CHECK_SHIFTED = int(a.split('=')[1])
    t, n, w = M.START
    st = M.state(n, w)
    t0 = time.time(); moves = 0; last = t0; nev = 0
    while time.time() - t0 < TL:
        before = summ(st)
        d, e = M.move(st); moves += 1
        if isinstance(d, tuple):
            print('HALT-EVENT', t, moves, before, d, flush=True); break
        t += d
        if e:
            nev += 1
            print('EV', t, moves, 'FROM', before[:3000], 'TO', summ(st)[:3000], 'STEPS', d, flush=True)
        if time.time() - last > 60:
            last = time.time(); print('AT', t, moves, nev, M.SHIFTED, M.WALL, summ(st)[:3000], flush=True)
    print('END', t, moves, nev, M.SHIFTED, M.WALL, summ(st)[:5000])


if __name__ == '__main__':
    main()
