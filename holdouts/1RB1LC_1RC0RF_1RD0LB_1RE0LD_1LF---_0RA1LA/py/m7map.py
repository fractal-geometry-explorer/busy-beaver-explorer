# 1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LF---_0RA1LA: the phase map on (n, r, t), with exact step counts.
# A phase end is the record  0^inf B> 0 0 1 (1100)^n (10110110)^r 10 (1110)^t 1 0^inf  with r < 5.
# Resets (measured on constructed tapes, see README): r = 1: n + 12, t - 1; r = 2: n + 32, t - 4 (both then r = 0);
# r = 0, 3, 4: a new phase  (10, m', t - 4, - 3, - 2), m' = ceil((n+4)/2), floor((n+25)/2), floor((n+26)/2), whose
# floor(m'/5) periods (Lean: periods) give n = 10 + 31 floor(m'/5), r = m' mod 5.
import sys
RS={(0,0):(151,1560),(0,1):(151,1605),(1,0):(192,1374),(1,1):(192,1374),(2,0):(512,8840),(2,1):(512,8840),
    (3,0):(471,8170),(3,1):(471,8215),(4,0):(471,8286),(4,1):(471,8241)}
def periods(n,q): return q*(448*n+6952)+448*31*q*(q-1)//2
def step(n,r,t):
    a,b=RS[(r,n%2)]; s=a*n+b
    if r==1: return n+12,0,t-1,s
    if r==2: return n+32,0,t-4,s
    mp={0:(n+5)//2,3:(n+25)//2,4:(n+26)//2}[r]; dt={0:4,3:3,4:2}[r]
    q=mp//5; return 10+31*q, mp%5, t-dt, s+periods(10,q)
if __name__=='__main__':
    n,r,t,S=map(int,sys.argv[1:5]); K=int(sys.argv[5]); tmin=int(sys.argv[6]) if len(sys.argv)>6 else 6
    for i in range(K):
        if t<tmin: print('stop: t =',t); break
        n,r,t,s=step(n,r,t); S+=s
        if i<40 or i%100==0: print(i+1, S if S<10**30 else '~10^%d'%(len(str(S))-1), n if n<10**30 else '~10^%d'%(len(str(n))-1), r, t)
    print('last', i+1, 'steps ~10^%d'%(len(str(S))-1), 'n ~10^%d'%(len(str(n))-1), 'r', r, 't', t)
