"""Check the binary-counter configurations of 1RB0RF_1LC1LF_1RD1LC_---1RE_0RC1RF_1RA0LB against a direct run.

At every step C reading 0 -> D reading 1 (C0 -> 1RD), test whether the tape around the head is
    ... W(n-1) 1 1 D>1 1 1 1 1 V(n) ...
with V(n) the bits of n, least significant first, as 1011 (1) / 1111 (0), read rightwards up to the first other
word, and W the bits of n-1, least significant nearest the head, as 1111 (1) / 1010 (0), read leftwards; the left
value must equal n-1 modulo 2^(number of left words).  Consecutive matches are grouped into runs where n goes up by
exactly one each time at a fixed head position; each run is printed: first step, last step, position, first n,
last n, the right and left widths at the end.
"""
import sys
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from sim import TM  # noqa: E402
m = '1RB0RF_1LC1LF_1RD1LC_---1RE_0RC1RF_1RA0LB'
T = int(float(sys.argv[1])); MINRUN = int(sys.argv[2]) if len(sys.argv) > 2 else 64
t = TM(m, 1 << 16); tape = t.tape
O4, Z4R, Z4L = b'\x01\x01\x01\x01', b'\x01\x00\x01\x01', b'\x01\x00\x01\x00'
def parse(p):
    if bytes(tape[p:p + 5]) != b'\x01' * 5 or tape[p - 1] != 1 or tape[p - 2] != 1: return None
    q = p + 5; n = 0; i = 0
    while True:
        w = bytes(tape[q:q + 4])
        if w == Z4R: n |= 1 << i
        elif w != O4: break
        q += 4; i += 1
    q = p - 2; mv = 0; j = 0
    while True:
        w = bytes(tape[q - 4:q])
        if w == O4: mv |= 1 << j
        elif w != Z4L: break
        q -= 4; j += 1
    return n, i, mv, j
run = None; runs = 0; total = 0
def flush():
    global runs
    if run and run[4] - run[3] + 1 >= MINRUN:
        runs += 1
        print('run', *run, flush=True)
while t.k < T:
    st = t.st
    if not t.step(): print('halt', t.k); break
    if st == 2 and t.st == 3 and tape[t.p] == 1:
        r = parse(t.p)
        if r is None: continue
        n, wr, mv, wl = r
        if n < 1 or mv != (n - 1) % (1 << wl): continue
        total += 1
        if run and run[2] == t.p - len(tape) // 2 and n == run[4] + 1:
            run[1] = t.k; run[4] = n; run[5] = wr; run[6] = wl
        else:
            flush(); run = [t.k, t.k, t.p - len(tape) // 2, n, n, wr, wl]
flush()
print('end', t.k, 'matches', total, 'long runs', runs)
