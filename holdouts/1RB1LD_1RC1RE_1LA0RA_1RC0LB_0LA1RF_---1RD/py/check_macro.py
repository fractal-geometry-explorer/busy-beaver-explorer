"""Check the macro map against the machine: reads the P1 rows "step n word" printed by c/rword.c (the rows
with n even) and checks that every row follows from the previous one by one move of the map, state and step count.

usage: rword MACHINE STEPS | awk '$2%2==0' | python3 check_macro.py [MACHINE] [verify]
"""
import re
import sys
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import macro as M  # noqa: E402


def expand(s):
    return re.sub(r'<(\d+)>', lambda m: '010' * int(m.group(1)), s)


def main():
    if len(sys.argv) > 1 and '_' in sys.argv[1]: M.use_machine(sys.argv[1])
    M.VERIFY = 'verify' in sys.argv
    st = None; t = 0; moves = 0; events = 0
    for line in sys.stdin:
        a = line.split()
        s, n, w = int(a[0]), int(a[1]), (a[2] if len(a) > 2 else '')
        if st is None:
            st = M.state(n, expand(w)); t = s; continue
        d, e = M.move(st); moves += 1; events += e
        if isinstance(d, tuple):
            print('the map halts but the machine goes on at step', s); sys.exit(1)
        t += d
        if not (t == s and st[0] == n and M.tostr(st[1], st[2], st[3]) == expand(w)):
            print('MISMATCH at step', s, 'row', n, w[:80], 'map', t, st[0], M.comp(st[1], st[2], st[3])[:80])
            sys.exit(1)
    print('OK: %d moves (%d events), every state and step count as the machine, last step %d' % (moves, events, t))


if __name__ == '__main__':
    main()
