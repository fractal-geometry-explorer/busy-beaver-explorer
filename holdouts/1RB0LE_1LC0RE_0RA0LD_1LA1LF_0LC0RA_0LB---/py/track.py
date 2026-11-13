"""Follow the events of a two-word sweeper machine and check them against the event rule.

Usage: python3 track.py MACHINE MAX_STEPS

An event is the head in state A on a 0 with the tape  0^inf 1 0 [N] A> 0 [M] 1 [R] 1 0 1 0^inf  (encodings as in
events.py; here R must be followed by `1 0 1` and blank tape, the shape of the first regime).  For each pair of
consecutive events the rule (N + 1, M + 1, R + 3 when M wraps) is checked; a line is printed for the first event,
for every event that does not follow from the previous one by the rule, and at the end.  Plain Python simulator.
"""
import re
import sys

D3 = {'100': 0, '110': 1, '010': 2}
PAT = re.compile(r'^0((?:0010|1010)+)1((?:1000|1010)*)1010*$')
TR = bytes.maketrans(b'\x00\x01', b'01')


def parse(m):
    t = {}
    for i, s in enumerate(m.split('_')):
        for r in range(2):
            x = s[3 * r:3 * r + 3]
            if x[0] != '-':
                t[(i, r)] = (int(x[0]), 1 if x[1] == 'R' else -1, ord(x[2]) - 65)
    return t


def main(m, n):
    tr = parse(m)
    size = 1 << 21
    tape = bytearray(size)
    p = lo = hi = size // 2
    st = 0
    steps = 0
    prev = None
    good = bad = 0
    while steps < n:
        if st == 0 and tape[p] == 0 and bytes(tape[p - 3:p]).translate(TR).decode() in D3:
            r = bytes(tape[p:hi + 1]).translate(TR).decode()
            mm = PAT.match(r)
            if mm:
                s = bytes(tape[lo:p]).translate(TR).decode()
                v = w = 0
                pw = 1
                while len(s) >= 3 and s[-3:] in D3:
                    v += D3[s[-3:]] * pw
                    pw *= 3
                    w += 1
                    s = s[:-3]
                if s.lstrip('0') == '10':
                    md, rd = mm.group(1), mm.group(2)
                    a, b = len(md) // 4, len(rd) // 4
                    mv = sum(1 << i for i in range(a) if md[4 * i] == '1')
                    rv = sum(1 << i for i in range(b) if rd[4 * i + 2] == '1')
                    ev = (v, w, mv, a, rv, b)
                    ok = False
                    if prev:
                        pv, pw_, pm, pa, pr, pb = prev
                        nv, nw = (pv + 1, pw_) if pv + 1 < 3 ** pw_ else (0, pw_ + 1)
                        nm = (pm + 1) % (1 << pa)
                        nr = pr + (3 if nm == 0 else 0)
                        ok = ev == (nv, nw, nm, pa, nr, pb)
                    if ok:
                        good += 1
                    else:
                        bad += 1
                        print(f"step {steps}: N={v} ({w} digits) M={mv} ({a} digits) R={rv} ({b} digits)"
                              + ("" if prev is None else "   <- not by the rule"))
                    prev = ev
        k = (st, tape[p])
        if k not in tr:
            print('halt at step', steps + 1)
            break
        w_, d, st = tr[k]
        tape[p] = w_
        p += d
        steps += 1
        lo, hi = min(lo, p), max(hi, p)
    print(f"{steps} steps: {good} events follow the rule from the previous one, {bad} do not; last {prev}")


if __name__ == '__main__':
    main(sys.argv[1], int(sys.argv[2]))
