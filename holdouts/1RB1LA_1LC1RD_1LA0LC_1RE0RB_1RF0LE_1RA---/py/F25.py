"""The round map F of 1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RF0LE_1RA--- and 1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RF1RC_1RA---
(busycoq pull request 40, verify/SOC25_Iter.v: F_spec), with the marker test of coq/SOC25_Marker.v.

A round state is (L, X). F(L, X) is None exactly when the machine halts during that round.
1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RF0LE_1RA--- starts at (8, 145), 1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RF1RC_1RA--- at (1, 3).
marked(m): m has a 1 bit at an even position. Proved in Coq (F_marker): if X is odd and div2 X is marked,
F(L, X) is defined and odd. So a halt needs a round with X odd and div2 X unmarked (M1c/M1d_needs_unmarked).

usage: python3 F25.py L X ROUNDS     (prints a line every 10,000 rounds; stops at a halt)
"""
import sys
sys.set_int_max_str_digits(0)


def v2(x): return (x & -x).bit_length()-1
def split(x):
    i=v2(x); return (x>>(i+1), i)
def F_loop(L1,k1,i,x):
    while True:
        a=i//2
        if i%2==0: return (L1+1+(a*5+1), (k1*2+1)*2**(a*5+1)+(x*2+1))
        L2=L1+1+(a*5+4); k2=(k1*2+1)*2**(a*5+4)-1
        if x==0: return (L2,k2+1)
        x2,i2=split(x)
        L1,k1,i,x = L2, k2-((2**i2-1)*2+1), i2, x2
def F(L,X):
    if X==2**L:
        l=L-1;a=l//2
        if l%2==0: return (l+3+a*5+2, (2**(l+1)*2+1)*2**(a*5+2))
        else: return (l+3+a*5+4, (2**(l+1)*2+1)*2**(a*5+4)-1+2)
    m,h=split(X); k=2**L-1-(2**h-1)*2; a=h//2
    if h%2==1:
        if m==0: return (L+1+a*5+3,(k*2+1)*2**(a*5+3))
        return None
    L1=L+1+a*5; k1=(k*2+1)*2**(a*5)-1
    if m==0: return (L1,k1+2)
    x,i=split(m)
    return F_loop(L1,k1-(2**i-1)*2,i,x)

def marked(m):
    """True when m has a 1 bit at an even position (0, 2, 4, ...)."""
    return m & int('01' * (m.bit_length() // 2 + 1), 2) != 0


if __name__ == "__main__":
    L, X, N = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    minmark = None  # fewest 1 bits at even positions of div2 X over odd rounds
    for t in range(N):
        if X % 2 == 1 and t >= 7:  # X after t rounds; the claim counts from round 7
            m = X >> 1
            k = bin(m & int('01' * (m.bit_length() // 2 + 1), 2)).count('1')
            minmark = k if minmark is None else min(minmark, k)
        r = F(L, X)
        if r is None:
            print("HALT in round", t, "L =", L)
            break
        L, X = r
        if t % 10000 == 0 or t == N - 1:
            print(t, "L =", L, "X odd" if X % 2 else "X even", "fewest even-position bits of div2 X since round 7:", minmark, flush=True)
