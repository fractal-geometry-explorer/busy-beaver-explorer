"""The run of 1RB1RA_1LC1LD as a map on two blocks, and a fast counted pass map.

At most pass starts of the run the tape is two blocks, `1^x 0 1^b A>0` (87% of the first 95,000 passes).  For a
recursive pass (b = 3j) the offset of `lean/Formula.lean` depends only on `pre([x])`, and `pre1` gives it in closed
form: affine in x on each residue mod 18, except x = 14 mod 18, where with t = (x - 5)/9 = 3^k s (s not divisible by 3)
the result follows k and s mod 6.  The step cost of `pre([x])` is a quadratic in x on each residue (`PRE_COST`).

`run` is `pre` of py/macro.py (and with `j` the whole recursive pass `K ls (3j - 1)`) on stacks, linear time, with the
step costs of `astepC'` in lean/Count.lean; `pass_counted` is `passC` of lean/Count.lean, the tail loop over the
words `0 1 1` in closed form (`tail_cost`).  From blank tape it reproduces `blank_reaches_1e12` exactly (8,257 passes,
step 1,000,110,302,407).

usage:
  python3 py/twoblock.py verify X        pre1 and its cost against the block machine for every x < X
  python3 py/twoblock.py check N         run, pass_full and pass_counted agree on N random lists; tail_cost exact
  python3 py/twoblock.py lean X J         the theorems of lean/TwoBlock.lean against pass_full, x < X, j <= J
  python3 py/twoblock.py run N [EVERY]   the counted run from blank tape for N passes, a line every EVERY passes
"""
import os
import random
import sys
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import macro as M  # noqa: E402

def run(ls, j=None, fuel=10**9):
    """Without j: `pre(ls)` as in py/macro.py, returning (L, p, u, steps) or None.  With j: the whole recursive pass
    from `K ls (3j - 1)`, returning ("pass", ls', n', steps), "halt" or None."""
    full = j is not None
    L=list(ls[:1] or [0])+list(ls[1:])
    Ls=L[::-1]
    Ws=([2]*j if full else [])+[1,0]
    nb=[2]; q,h,u='B',0,0; cost=7*j if full else 0
    def push(w):
        Ws.append(w); nb[0]+=(w!=2)
    def pop():
        w=Ws.pop(); nb[0]-=(w!=2); return w
    def tw(a,jj,k):
        if jj==0: push(a+k)
        else: push(2+k); Ws.extend([2]*(jj-1)); push(a)
    def done(M,n):
        return ('pass',M,n,cost)
    for _ in range(fuel):
        if not full:
            if q=='A' and h==0 and nb[0]==0:
                L=Ls[::-1]; return (L+[0,0])[:max(2,len(L))],len(Ws),u,cost
            if not Ws or (q=='C' and len(Ws)==1 and Ws[0]==1):
                Ws.insert(0,2); u+=1; continue
        while len(Ls)<4: Ls.insert(0,0)
        a=Ls[-1]; has=bool(Ws)
        if q=='A' and h>0:
            Ls[-1]=a+h; cost+=h; h=0; continue
        if q=='A':
            if not has:
                if a>0: cost+=3; Ls.pop(); return done(Ls[::-1],a-1)
                return None
            k=pop()
            if k<=0: return None
            cost+=3*k+1; Ls.extend([0]*(k-1)); Ls.append(1); q='B'; continue
        if q in 'DE' and h==(0 if q=='D' else 1):
            if not has: return 'halt'
            e=q=='E'; a2=a+(3 if e else 2); k=pop(); h=0
            if k==1: Ls[-1]=a2; q='D'; cost+=2+e
            elif k==2: Ls[-1]=a2; Ls.append(0); q='F'; cost+=3+e
            elif k>2: Ls[-1]=a2; Ls.extend([0]*(k-3)); Ls.append(1); q='B'; cost+=3*k-5+e
            else: return None
            continue
        if q=='F' and h==0:
            if not has:
                cost+=4; Ls.pop(); return done(Ls[::-1],a)
            k=pop(); Ls[-1]=a+k+1; q='A'; cost+=k+1; continue
        if q=='C' and h==0 and has:
            k=Ws[-1]
            if a>0 and k==1 and len(Ws)>1:
                Ls[-1]=0; pop(); w=pop(); push(w+a); push(1); cost+=9*a; continue
            if a>0:
                pop(); Ls[-1]=a-1; Ls.extend([0]*k); Ls.append(1); q='B'; cost+=3*k+3; continue
            if k==0: return None
            pop(); Ls.pop(); Ls[-1]+=2
            if k==1: Ls.append(0); q='F'; cost+=4
            else: Ls.extend([0]*(k-2)); Ls.append(1); q='B'; cost+=3*k-1
            continue
        if q=='B' and h==0:
            if not has:
                if Ls[-1]==1 and Ls[-2]==0:
                    y=Ls[-3]; x=Ls[-4]; cost+=10*y+12
                    M=Ls[:-4][::-1]
                    return done([x+2]+M,y+1)
                return None
            k=pop(); n=Ls.pop(); c=Ls.pop(); d=Ls[-1]; j3=n//3
            if n%3==1:
                Ls.append(c); tw(1,j3,k); push(0); q='B'; cost+=7*j3+2
            elif n==2:
                Ls.append(c+3); q='E'; h=k+1; cost+=6
            elif n%3==2:
                Ls.append(c+3); q='E'; h=1; tw(2,j3-1,k); cost+=7*(j3-1)+13
            elif k==0:
                Ls.append(c); q='C'; tw(1,j3,0); cost+=7*j3+1
            elif n==0:
                Ls.append(c); q='C'; push(k+1); cost+=1
            elif n==3:
                Ls[-1]=d+2; Ls.append(c+2); q='A'; h=k+1; cost+=10*c+14
            else:
                Ls[-1]=d+2; Ls.append(c+2); q='A'; h=1; tw(2,j3-2,k); cost+=10*c+7*(j3-1)+14
            continue
        return None
    return None


def pre1(x):
    """`pre([x])` in closed form for x >= 3: (blocks left of the head, nearest first, without padding zeros, u); p is
    always 0."""
    r = x % 18
    if r in (0, 6, 12):
        return [2 * x // 3 + 2, x // 3 + 2], 0
    if r in (4, 10, 16):
        return [(2 * x + 7) // 3, (x + 8) // 3], 0
    if r in (5, 11, 17):
        return [(2 * x - 4) // 3, (x + 13) // 3], 0
    if r == 7:
        return [(7 * x + 59) // 9, (2 * x + 22) // 9], 1
    if r == 13:
        return [(2 * x + 19) // 3, (x + 11) // 3], 1
    if r == 2:
        return [(4 * x - 8) // 9, (5 * x + 62) // 9], 1
    if r == 15:
        return [(4 * x + 12) // 9, (5 * x + 51) // 9], 1
    if r == 1:
        return [4, (4 * x + 5) // 9, (5 * x + 49) // 9], 2
    if r == 3:
        return [4, (7 * x + 42) // 9, (2 * x + 12) // 9], 2
    if r == 8:
        return [4, (7 * x + 43) // 9, (2 * x + 2) // 9], 2
    if r == 9:
        return [4, (2 * x + 15) // 3, (x + 9) // 3], 2
    t = (x - 5) // 9                         # r == 14: t odd; t = 3^k s
    s, k = t, 0
    while s % 3 == 0:
        s, k = s // 3, k + 1
    if s % 6 == 1:                           # a carry down the powers of 3: k + 4 blocks, offset 0
        return [4, 4 * t + 2] + [10 * t // 3 ** i for i in range(1, k + 1)] + [(13 * s + 20) // 3, (2 * s + 4) // 3], 2
    a = ((2 * 3 ** (k + 2) - 2) * s + 7 + 3 * k) // 3   # s = 5 mod 6: two blocks, total x + 7 + k
    return [a, x + 7 + k - a], 1


# steps of pre([x]), x >= 3 and x != 14 mod 18: C x^2 + B x + A by residue mod 18
_Q0, _Q4, _Q5 = (F(5, 9), F(7), F(7)), (F(5, 9), F(68, 9), F(125, 9)), (F(5, 9), F(13, 9), F(-19, 9))
PRE_COST = {0: _Q0, 6: _Q0, 12: _Q0, 4: _Q4, 10: _Q4, 16: _Q4, 5: _Q5, 11: _Q5, 17: _Q5,
            1: (F(65, 81), F(320, 81), F(2936, 81)), 2: (F(65, 81), F(-215, 81), F(980, 81)),
            3: (F(95, 81), F(275, 27), F(323, 9)), 7: (F(95, 81), F(1280, 81), F(4043, 81)),
            8: (F(95, 81), F(235, 81), F(2489, 81)), 9: (F(10, 9), F(101, 9), F(50)),
            13: (F(10, 9), F(47, 3), F(509, 9)), 15: (F(65, 81), F(145, 27), F(62, 9))}


def pre1_cost(x):
    C, B, A = PRE_COST[x % 18]
    c = C * x * x + B * x + A
    assert c.denominator == 1
    return int(c)


def tail_cost(a, P):
    """Steps of the final loop of a recursive pass over P words 0 1 1 (tail_end in lean/Formula.lean), a the block
    before the head."""
    return 3 - P + 5 * a * P + 5 * P * P if P % 2 == 0 else 5 + 5 * a + 9 * P + 5 * a * P + 5 * P * P


def aph(t, y):
    return t * (10 * y + 18) + 20 * t * (t - 1)


def kd_cost(c, t):
    if t == 0:
        return 10 * c + 24 + (10 * (c + 3) + 15)
    s = t - 1
    return 10 * c + 14 * (s + 1) + 24 + (10 * (c + 3) + 21) + aph(s, c + 7) + (10 * (c + 7 + 4 * s) + 12)


def pass_counted(ls, n):
    """`passC` of lean/Count.lean on `K ls n` (blocks nearest first, last block n + 1): (ls', n', steps), the
    recursive passes through `pre` and `recur_sound`."""
    x = ls[0] if ls else 0
    d = ls[1] if len(ls) > 1 else 0
    if n == 3:
        return [x + 6] + ls[1:], 0, 19
    if n % 6 == 3:
        t = (n - 9) // 6
        return [x + 2 * t + 8] + ls[1:], 4 * t + 4, 14 * t + 32 + aph(t, 3) + 7 + 10 * (3 + 4 * t) + 12
    if n % 6 == 0 and n > 0:
        t = (n - 6) // 6
        return [x + 2 * t + 6] + ls[1:], 4 * t + 2, 14 * t + 24 + 1 + aph(t, 3) + 3
    if n % 6 == 1:
        t = n // 6
        return [d + 2 * t + 2] + ls[2:], x + 4 * t + 2, 10 * x + 14 * t + 12 + 1 + aph(t, x + 3) + 3
    if n % 6 == 4:
        t = n // 6
        return [d + 2 * t + 4] + ls[2:], x + 4 * t + 4, kd_cost(x, t)
    if n % 3 != 2:
        return None                                   # n = 0: the last block 1 halts
    j = n // 3 + 1
    if len(ls) == 1 and x % 18 != 14 and x > 2:
        L, u = pre1(x)
        L, p, c = L + [0, 0], 0, pre1_cost(x)
    else:
        r = run(ls)
        if r is None:
            return None
        L, p, u, c = r
    P = p + j - u
    a, b, rest = L[0], L[1], L[2:]
    if j < u or P < 2:                                # outside recur_sound's range, or a short loop: run it all
        f = run(ls, j)
        return None if f is None or f == "halt" else (_strip(f[1]), f[2], f[3])
    ls2 = [b + 2 * ((P + 1) // 2)] + rest
    while ls2 and ls2[-1] == 0:
        ls2.pop()
    return ls2, a + 2 * P - 1, 7 * j + c + tail_cost(a, P)


def _strip(L):
    L = list(L)
    while L and L[-1] == 0:
        L.pop()
    return L


def verify(X):
    bad = 0
    for x in range(3, X):
        L, p, u, c = run([x])
        if (_strip(L), p, u) != tuple([pre1(x)[0], 0, pre1(x)[1]]) or (x % 18 != 14 and c != pre1_cost(x)):
            bad += 1
            print("differs", x)
    print(f"pre1 and its cost agree with the block machine for x = 3..{X - 1}" if not bad else f"{bad} differ")
    return bad


def check(N, seed=1):
    rnd = random.Random(seed)
    n = 0
    for _ in range(N):
        ls = [rnd.randint(2, 60) for _ in range(rnd.randint(1, 5))]
        j = rnd.randint(1, 40)
        a, b = M.pre(ls), run(ls)
        assert (a is None) == (b is None), ls
        if a is not None:
            assert (_strip(a[0]), a[1], a[2]) == (_strip(b[0]), b[1], b[2]), ls
        r, f = M.pass_full(ls, 3 * j - 1), run(ls, j)
        if r is None or r == M.HALT:
            continue
        assert (_strip(r[1]), r[2]) == (_strip(f[1]), f[2]), (ls, j)
        c = pass_counted(ls, 3 * j - 1)
        assert c is not None and (_strip(c[0]), c[1], c[2]) == (_strip(f[1]), f[2], f[3]), (ls, j)
        n += 1
    print(f"run, pass_full and pass_counted agree on {n} recursive passes")
    return n


def counted_run(N, every=1000, out=sys.stdout):
    """From blank tape: K [10] 2 at step 183 (`blank_passesC`), then N passes."""
    ls, n, S = [10], 2, 183
    for i in range(1, N + 1):
        r = pass_counted(ls, n)
        if r is None:
            print("not covered or halt at pass", i, ls, n, file=out)
            return None
        ls, n, s = r
        S += s
        if i % every == 0 or i == N:
            print(i, S, len(ls) + 1, sum(ls) + n + 1, n + 1, file=out, flush=True)
    return ls, n, S


def g14(r):
    """`g14` of lean/TwoBlock.lean: (word 3 left?, a, b, M) after the levels of the carry from the block 6r + 8."""
    m, c = divmod(r, 3)
    if c == 2:
        return (False, 32 * m + 29, 22 * m + 28, [0])
    if c == 0:
        return (True, 24 * m + 4, 26 * m + 11, [4 * m + 2])
    t, a, b, M = g14(m)
    if t:
        return (True, 24 * m + 12, a + 12 * m + 6, [b] + M)
    return (False, a + 24 * m + 13, b + 12 * m + 6, M)


def lean_one(x, j):
    """The next pass start after `1^x 0 1^(3j) A>0` as the theorems of lean/TwoBlock.lean (and `recur_two` for x = 2)
    state it, blocks left to right with zero blocks dropped; None where no theorem applies (j too small)."""
    c2 = lambda v: 2 * ((v + 1) // 2)        # 2 ceil(v/2)
    i = j - 1                                 # K [x] (3i + 2): last block 3j
    r = x // 18
    def out(ls, n):                           # K ls n, ls nearest first
        bl = list(reversed(ls)) + [n + 1]
        while bl and bl[0] == 0:
            bl.pop(0)
        return tuple(bl)
    if x == 2:
        return out([8 + c2(j - 2)], 2 * j - 2) if j >= 2 else None
    if x == 5:
        return out([6 + 2 * ((i + 2) // 2)], 2 + 2 * (i + 1) - 1)
    if x % 6 == 0:
        q = x // 6 - 1
        return out([2 * q + 4 + 2 * ((i + 2) // 2)], 4 * q + 6 + 2 * (i + 1) - 1)
    if x % 6 == 4:
        q = x // 6
        return out([2 * q + 4 + 2 * ((i + 2) // 2)], 4 * q + 5 + 2 * (i + 1) - 1)
    if x % 6 == 5:
        q = (x - 11) // 6
        return out([2 * q + 8 + 2 * ((i + 2) // 2)], 4 * q + 6 + 2 * (i + 1) - 1)
    k = x % 18
    if k == 2:
        r = (x - 20) // 18
        return out([10 * r + 18 + c2(i)], 8 * r + 8 + 2 * i - 1)
    if k == 7:
        return out([4 * r + 4 + c2(i)], 14 * r + 12 + 2 * i - 1)
    if k == 13:
        return out([6 * r + 8 + c2(i)], 12 * r + 15 + 2 * i - 1)
    if k == 15:
        return out([10 * r + 14 + c2(i)], 8 * r + 8 + 2 * i - 1)
    if k == 14:
        t, a, b, M = g14(r)
        if not t:
            return out([b + c2(i)] + M, a + 2 * i - 1)
        i -= 1
        return out([a + 2 + c2(i), b] + M, 4 + 2 * i - 1) if i >= 0 else None
    i -= 1                                    # the rest take two supply words: last block 3(i + 1) + 3
    if i < 0:
        return None
    if k == 1:
        r = (x - 19) // 18
        return out([8 * r + 9 + c2(i), 10 * r + 16], 4 + 2 * i - 1)
    if k == 8:
        return out([14 * r + 11 + c2(i), 4 * r + 2], 4 + 2 * i - 1)
    if k == 3:
        return out([14 * r + 7 + c2(i), 4 * r + 2], 4 + 2 * i - 1)
    if k == 9:
        return out([12 * r + 11 + c2(i), 6 * r + 6], 4 + 2 * i - 1)
    return None


def check_lean(X, J):
    """lean_one against the block machine (pass_full) for every x in 2..X-1 and j in 1..J: the number compared."""
    n = 0
    for x in range(2, X):
        for j in range(1, J + 1):
            p = lean_one(x, j)
            if p is None:
                continue
            assert p == M.next_full((x, 3 * j)), (x, j, p, M.next_full((x, 3 * j)))
            n += 1
    return n


if __name__ == "__main__":
    a = sys.argv[1:]
    if not a:
        print(__doc__)
    elif a[0] == "verify":
        verify(int(a[1]))
    elif a[0] == "check":
        check(int(a[1]))
    elif a[0] == "lean":
        print("lean/TwoBlock.lean agrees with the block machine on", check_lean(int(a[1]), int(a[2])), "passes")
    elif a[0] == "run":
        counted_run(int(a[1]), int(a[2]) if len(a) > 2 else 1000)
