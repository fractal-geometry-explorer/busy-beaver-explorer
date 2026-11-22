"""Check the merge rule of lean/LeftoverRules.lean on the visits round_check.py leaves over.

usage:  ./vdump 280000000 420000000 1 > vd.txt   (c/vdump.c)
        python3 holdouts/MACHINE/py/leftover_check.py vd.txt

For each visit that meets a leftover 100 (kind 'd0' of round_check.py) of the form  S_x S_0 100 1 S_y S_z,  the
predicted next tape is: those blocks replaced by S_(x+y+3) S_0 S_0 S_(z-1) (S_(-1) = 1), the next wall on the left
worn down as in a round (three 1s, or 0111 -> 00 for a wall of three), and the right end as in a round.
"""
import collections
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from round_check import predict, RI, SBLOCKS  # noqa: E402


def S(n):
    return '1' + '01' * (n + 1)


def main():
    st = collections.Counter()
    rows = [line.split() for line in open(sys.argv[1])]
    for a, b in zip(rows, rows[1:]):
        kind, _ = predict(a[5])
        if 'd0' not in kind:
            continue
        T, U = a[5], b[5]
        m = RI.search(T)
        if m:
            i = m.start()
            body = T[:i]

            def end(B):
                return B + '010101' + '101101' + T[i + 6:]
        else:
            body = T[:-2]

            def end(B):
                return B + T[-2:-1] + '0110110'
        s0 = SBLOCKS.search(body).start()
        q = body.rfind('1011001', 0, s0 + 4)
        my = re.match(r'((?:01)+)', body[q + 8:]) if q >= s0 - 8 else None
        if not my:
            st['other leftover 100 (sweep turns at it)'] += 1
            continue
        mx = re.search(r'1((?:01)+)$', body[:q])
        x, xs = len(mx.group(1)) // 2 - 1, mx.start()
        y = len(my.group(1)) // 2 - 1
        r2 = q + 8 + len(my.group(1))
        mz = re.match(r'1((?:01)+)', body[r2:])
        z, r3 = len(mz.group(1)) // 2 - 1, r2 + len(mz.group(0))
        B = body[:xs] + S(x + y + 3) + S(0) + S(0) + S(z - 1) + body[r3:]
        mw = re.search(r'0(1{3,})((?:01)+(?:1(?:01)+)*)$', B[:xs])
        if not mw:
            st['merge, no wall on the left'] += 1
            continue
        w, K = mw.start(1), len(mw.group(1))
        B = B[:w] + '1' * (K - 3) + B[w + K:] if K >= 4 else B[:w] + '0' + B[w + K + 1:]
        st['merge, predicted exactly' if end(B) == U else 'merge, MISMATCH'] += 1
    for k, v in sorted(st.items()):
        print(f"{v:6d}  {k}")


if __name__ == "__main__":
    main()
