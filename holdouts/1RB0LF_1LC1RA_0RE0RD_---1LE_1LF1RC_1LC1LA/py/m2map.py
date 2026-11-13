# Collatz-like map of 1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA on Z(t) = 1^t, head B at right end (heuristic, fitted)
def H(j): return 2**(j+1)-2*j-7
def band(t):
    j=3
    while H(j)<t: j+=1
    return j   # H(j-1) < t <= H(j)
def reduce(x,y):
    return y+3*x if x%2==0 else y+3*x-2
def G(t):
    if t%2==0:
        k=t//2
        return 3*k+3 if k%2 else 3*k+1
    j=band(t)
    if t==H(j): return None   # halts
    if t==H(j)-2: return reduce((t+5)//2, 4*j)
    x=(H(j)-t)//2-2; y=2*t-2*H(j-1)+4
    return reduce(x,y)
if __name__=='__main__':
    import sys
    t=int(sys.argv[1]); n=int(sys.argv[2])
    for i in range(n):
        print(i,t); t=G(t)
        if t is None: print('HALT'); break
