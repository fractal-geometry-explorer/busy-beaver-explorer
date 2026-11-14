"""1RB1LE_0RC1RC_0RD0RB_1RE0RF_1LA0LE_---1RB: the tape at chosen visits of the right end, written in units
[j,a] = 0 1^(2j) 0 0 1 1 0 (10)^a (a countdown: j counts up, a counts down), other cells as they are.

usage: python3 units.py VISIT [VISIT ...]     (direct simulation in Python; visit 2070 takes about 15 seconds)
"""
import sys, re
U=re.compile(r'0((?:11)+)00110((?:10)*)')
def tok(bits):
    out=[];i=0;raw=""
    while i<len(bits):
        m=U.match(bits,i)
        if m:
            if raw: out.append(raw); raw=""
            out.append("[%d,%d]"%(len(m.group(1))//2,len(m.group(2))//2)); i=m.end()
        else:
            m2=re.match(r'(?:10){3,}',bits[i:])
            if m2:
                if raw: out.append(raw); raw=""
                out.append("(10)^%d"%(len(m2.group(0))//2)); i+=len(m2.group(0))
            else: raw+=bits[i]; i+=1
    if raw: out.append(raw)
    return " ".join(out)

M = "1RB1LE_0RC1RC_0RD0RB_1RE0RF_1LA0LE_---1RB"


def tapes(visits):
    T = {}
    for s in range(6):
        for b in range(2):
            t = M[s * 7 + b * 3:s * 7 + b * 3 + 3]
            if t[0] != '-':
                T[(s, b)] = (int(t[0]), 1 if t[1] == 'R' else -1, ord(t[2]) - 65)
    N = 1 << 20
    tape = bytearray(N); p = N // 4; lo = hi = p; s = 0; vis = 0; step = 0; want = set(visits); last = max(visits)
    while vis < last:
        w, d, s = T[(s, tape[p])]
        tape[p] = w; p += d; step += 1
        if p < lo: lo = p
        if p > hi:
            hi = p
            if s == 4:
                vis += 1
                if vis in want:
                    yield vis, step, "".join(map(str, tape[lo:hi]))


if __name__ == "__main__":
    for vis, step, bits in tapes([int(x) for x in sys.argv[1:]]):
        print("visit", vis, "step", step, ":", tok(bits))
