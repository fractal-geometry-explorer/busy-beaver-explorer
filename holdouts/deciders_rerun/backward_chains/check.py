"""Check each witness: run the machine forward from the window and confirm it halts after exactly the claimed number
of steps without the head leaving the window. Usage: python3 check.py  (run from this folder or give the folder)."""
import os, sys, glob
d = sys.argv[1] if len(sys.argv) > 1 else os.path.dirname(os.path.abspath(__file__))
for path in sorted(glob.glob(os.path.join(d, '*.txt'))):
    name = os.path.basename(path)[:-4]; m = name.split('_')
    f = open(path).read().split(); D = int(f[2]); q = ord(f[4]) - 65; h = int(f[6]); t = [int(c) for c in f[8]]
    n = 0
    while True:
        assert 0 <= h < len(t), name + ': head left the window'
        tr = m[q][3*t[h]:3*t[h]+3]
        if tr[2] == '-': break
        t[h] = int(tr[0]); h += 1 if tr[1] == 'R' else -1; q = ord(tr[2]) - 65; n += 1
    assert n == D, name
    print(f'{name}: halts after exactly {n} steps inside a window of {len(t)} cells')
