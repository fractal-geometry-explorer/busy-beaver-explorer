"""Follow the events of 1RB0LE_0LC0RA_1LE0RD_0RB---_0LF0LD_1LA0LF (usage: python3 track.py STEPS).

An event: state A, the tape  0^inf [left counter: 3-cell digits 000 = 0, 100 = 1] ENGINE A> 0 PREFIX [M: 2 digits
1000 = 0, 1010 = 1, low first] rest, with ENGINE and PREFIX the fixed words of events.py.  Prints the first event,
every event that is not "left + 1, M + 1" (or M wraps) from the previous one, and a summary.  Plain Python."""
import sys
ENG = "00101001010100"
PRE = "1001010100100101010010001001000100100010101010"
G = "1RB0LE_0LC0RA_1LE0RD_0RB---_0LF0LD_1LA0LF"
TR = bytes.maketrans(b'\x00\x01', b'01')


def main(n):
    t = {}
    for i, s in enumerate(G.split('_')):
        for r in range(2):
            x = s[3 * r:3 * r + 3]
            if x[0] != '-':
                t[(i, r)] = (int(x[0]), 1 if x[1] == 'R' else -1, ord(x[2]) - 65)
    size = 1 << 21
    tape = bytearray(size)
    p = lo = hi = size // 2
    st, steps, prev, good, bad, wraps = 0, 0, None, 0, 0, 0
    L, R = len(ENG), len(PRE)
    while steps < n:
        if st == 0 and tape[p] == 0 and bytes(tape[p - L:p]).translate(TR).decode() == ENG \
                and bytes(tape[p + 1:p + 1 + R]).translate(TR).decode() == PRE:
            left = bytes(tape[lo:p - L]).translate(TR).decode().lstrip('0')
            left = '0' * (-len(left) % 3) + left
            mm = bytes(tape[p + 1 + R:p + 9 + R]).translate(TR).decode()
            if all(left[i:i + 3] in ('000', '100') for i in range(0, len(left), 3)) and mm[0:4] in ('1000', '1010') and mm[4:8] in ('1000', '1010'):
                v = int(''.join(left[i] for i in range(0, len(left), 3)) or '0', 2)
                m = (mm[2] == '1') + 2 * (mm[6] == '1')
                ok = prev is not None and v == prev[0] + 1 and m == (prev[1] + 1) % 4
                if ok:
                    good += 1
                    wraps += m == 0
                else:
                    bad += 1
                    print(f"step {steps}: left counter {v}, M {m}" + ("" if prev is None else "   <- not left+1, M+1"))
                prev = (v, m)
        k = (st, tape[p])
        if k not in t:
            print('halt at step', steps + 1)
            break
        w, d, st = t[k]
        tape[p] = w
        p += d
        steps += 1
        lo, hi = min(lo, p), max(hi, p)
    print(f"{steps} steps: {good} events are left+1, M+1 from the previous one ({wraps} of them wraps of M), {bad} are not; last {prev}")


if __name__ == '__main__':
    main(int(sys.argv[1]))
