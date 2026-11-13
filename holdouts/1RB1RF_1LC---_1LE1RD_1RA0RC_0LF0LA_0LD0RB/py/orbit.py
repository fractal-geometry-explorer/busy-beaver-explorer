"""Iterate the left-end map (emap.py) of 1RB1RF_1LC---_1LE1RD_1RA0RC_0LF0LA_0LD0RB from blank tape: the first
left-end state is D(3, 0) after 11 steps.  Counts the epochs (all-ones states D(N, 0), the README's `1 A>0 0 1^N`).

usage: python3 orbit.py SECONDS [epochs.txt]     python3 orbit.py epochs K     (the first K epoch values N)
"""
import os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from emap import jump


def main():
    if sys.argv[1] == 'epochs':
        x, out = ('D', 3, 0), []
        while len(out) < int(sys.argv[2]):
            x = jump(*x)
            if x[2] == 0 and x[0] == 'D':
                out.append(x[1])
        print(*out)
        return
    T = float(sys.argv[1])
    out = open(sys.argv[2], 'w') if len(sys.argv) > 2 else None
    x = ('D', 3, 0)
    t0 = time.time(); steps = ep = near = bits = 0
    while True:
        x = jump(*x); steps += 1
        if x == 'HALT':
            print('HALT after', steps, 'map steps,', ep, 'epochs'); return
        if x[2] == 0 and x[0] == 'D':
            ep += 1; bits = x[1].bit_length()
            if out:
                out.write(f'{x[1]}\n')
        if x[2] == 1:
            near += 1
        if steps % 4096 == 0 and time.time() - t0 > T:
            break
    print('no halt in', steps, 'map steps (a run of drain steps counted once),', ep, 'epochs; states with k = 1:', near,
          '(all with n even); the last epoch value N has', bits, 'bits')


main()
