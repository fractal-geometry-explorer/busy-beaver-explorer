"""Phase map of 1RB0RE_1RC---_0RD0RC_1LE1LF_1LD1RA_1RC0LF.

A phase start is P(pre, x): the tape [1] (10)^x 1 1 1 0 with D at the right end on blank tape (pre = 1 when the
leading 1 is there).  run(pre, x) simulates to the next phase start.  F(pre, x) is the observed map:
  F(0, x) = (x mod 2, 3*floor(x/2) + 6),   F(1, 2i+1) = (0, 3i + 6),
  F(1, 4i+2) = (1, 9i + 15),               F(1, 8i) = (1, 27i + 18),     F(1, 8i+4): not a single formula.
usage: python3 phasemap.py           checks F against run() for x <= 120 and prints the orbit from P(1, 3).
"""
import sys
def parse(M):
    T = {}
    for i, g in enumerate(M.split("_")):
        for b in range(2):
            t = g[3 * b:3 * b + 3]
            T[(i, b)] = None if t[2] == "-" else (int(t[0]), 1 if t[1] == "R" else -1, ord(t[2]) - 65)
    return T
M='1RB0RE_1RC---_0RD0RC_1LE1LF_1LD1RA_1RC0LF'
T=parse(M)
def run(pre,x,maxsteps=10**8):
    pad=1<<20
    w=([1] if pre else [])+[1,0]*x+[1,1,1,0]
    tape=bytearray(2*pad+len(w)); tape[pad:pad+len(w)]=bytes(w)
    p=pad+len(w); s=3; n=0; hi=p
    while n<maxsteps:
        t=T[(s,tape[p])]
        if t is None: return ('HALT',n+1)
        tape[p]=t[0]; p+=t[1]; s=t[2]; n+=1
        if p>hi: hi=p
        if s==3 and p==hi and tape[p-4:p]==b'\x01\x01\x01\x00':
            # parse left part
            k=p-4; j=k
            while tape[j-2:j]==b'\x01\x00': j-=2
            xx=(k-j)//2
            if not any(tape[pad-2000:j-1]) and tape[j-1] in (0,1):
                pre2=tape[j-1]==1
                if not any(tape[pad-200000:j-1 if pre2 else j]): return ('S',int(pre2),xx,n)
    return ('?',n)



def F(pre, x):
    if pre == 0:
        return (x % 2, 3 * (x // 2) + 6)
    if x % 2:
        return (0, 3 * (x - 1) // 2 + 6)
    if x % 4 == 2:
        return (1, 9 * (x // 4) + 15)
    if x % 8 == 0:
        return (1, 27 * (x // 8) + 18)
    return None

def orbit():
    s = (1, 3); out = [s]
    while F(*s) is not None:
        s = F(*s); out.append(s)
    return out


if __name__ == "__main__":
    bad = n = 0
    for pre in (0, 1):
        for x in range(1, 121):
            f = F(pre, x)
            if f is None:
                continue
            r = run(pre, x, 10**8); n += 1
            if r[0] != "S" or (r[1], r[2]) != f:
                bad += 1; print("MISMATCH", pre, x, r, f)
    print("checked", n, "mismatches", bad)
    o = orbit()
    print(len(o) - 1, "phases from P(1, 3); last", o[-1])
