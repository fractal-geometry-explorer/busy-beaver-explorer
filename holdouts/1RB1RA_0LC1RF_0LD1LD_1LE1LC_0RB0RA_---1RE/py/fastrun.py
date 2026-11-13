"""An exact accelerated run of 1RB1RA_0LC1RF_0LD1LD_1LE1LC_0RB0RA_---1RE: the block list of blocks.py, run-length
coded (runs of equal blocks as [value, count]), with many visits applied at once:

* a target eating its left neighbour x: min(x, z/2) visits at once (x - k, e + 4k, z - 2k);
* a target eating a run of n equal blocks v whole: each costs v + 1 visits and leaves 4v + 3 behind;
* the front target: k visits insert 2 3^(k-1) at the front;
* z odd: its left neighbour y drained at once (y visits, z + 2y).

Each visit costs 2D + 5 steps (2D + 4 when z = 0 disappears), D the number of cells from the target block to the
right end, and D grows by 2 a visit between events, so a batch of k visits costs k(2D + 5) + 2k(k - 1) steps.
Halts are detected exactly as in blocks.step.  Checked against blocks.step (every block, at random visits) and
against the machine's step count (check).

usage:
  python3 fastrun.py check VISITS        blocks and step counts against blocks.py and the machine
  python3 fastrun.py far DIGITS SECONDS  run until 10^DIGITS steps (or the time is up); print events
"""
import sys, time
class Halt(Exception): pass
class RLE:
    def __init__(s, blocks, steps=0, visits=0):
        s.r=[]
        for x in blocks: s._app(x,1)
        s.v=visits; s.steps=steps; s.t=None; s.D=None; s.ev={'pop':0,'jump':0,'refuel':0,'front':0}
        s.log=None
    def _app(s,x,c):
        if s.r and s.r[-1][0]==x: s.r[-1][1]+=c
        else: s.r.append([x,c])
    def blocks(s):
        out=[]
        for x,c in s.r: out+= [x]*c
        return out
    def split_last(s, i):
        """make run i have count 1 by splitting off its last copy; return index of that copy"""
        x,c=s.r[i]
        if c>1:
            s.r[i][1]=c-1; s.r.insert(i+1,[x,1]); return i+1
        return i
    def norm(s):
        # merge adjacent equal runs (cheap local version run occasionally)
        out=[]
        for x,c in s.r:
            if c==0: continue
            if out and out[-1][0]==x: out[-1][1]+=c
            else: out.append([x,c])
        s.r=out
    def findtarget(s):
        """index of target run (count made 1) and set D; raise Halt"""
        r=s.r; z=r[-1][0]
        if z%2:
            i=s.split_last(len(r)-1); s.t=i; s.D=z; return
        # z even: z is single? split z off
        i=s.split_last(len(r)-1)
        j=i-1; 
        # also z run copies left of z (if count>1 they were split off: those are even -> target)
        while j>=0 and r[j][0]%2==1:
            if r[j][0]<3: raise Halt('short odd',s.v)
            j-=1
        if j<0: raise Halt('left end',s.v)
        s.ev['jump']+=1
        if s.log is not None and j < len(r)-2:
            seg=r[j+1:len(r)-1]
            s.log.append((s.v, sum(c for x,c in seg), min(x for x,c in seg)))
        j=s.split_last(j); s.t=j
        s.D=sum(x*c for x,c in r[j:]) + sum(c for x,c in r[j:]) - 1
    def addsteps(s,k,pop=False):
        # k ordinary visits starting at D
        s.steps += k*(2*s.D+5) + 2*k*(k-1); s.D += 2*k; s.v+=k
    def run(s, maxv=None, maxsteps=None):
        r=s.r
        while True:
            if maxv is not None and s.v>=maxv: return
            if maxsteps is not None and s.steps>=maxsteps: return
            r=s.r
            if s.t is None: s.findtarget()
            t=s.t; m=len(r)
            z=r[-1][0]
            rem = None if maxv is None else maxv-s.v
            if t==m-1:
                # z odd target (or z is the target as last)
                assert z%2==1 and r[t][1]==1
                if t==0:
                    r.insert(0,[2,1]); r[-1][0]-=1; s.addsteps(1); s.t=None; continue
                ii=s.split_last(t-1); r=s.r; t=ii+1
                y=r[ii][0]
                if y>0:
                    k=y if rem is None else min(y,rem)
                    r[ii][0]-=k; s.addsteps(k); r[t][0]+=2*k; s.D=r[t][0]; s.t=t; continue
                r[ii][0]=2; s.addsteps(1); r[t][0]-=1; s.ev['refuel']+=1
                s.t=ii; s.D=3+r[t][0]; s.norm(); s.t=None if False else s.t
                # norm may merge runs: recompute target index
                s.t=None; s.findtarget_after_refuel(); continue
            # z even, target t (count 1), even
            T=r[t][0]
            assert T%2==0 and r[t][1]==1
            zi=len(r)-1
            if r[zi][1]>1: zi=s.split_last(zi); 
            r=s.r; z=r[-1][0]
            if t==0:
                # front target
                if T==0: raise Halt('e=0,x=0 front',s.v)
                if z>=2:
                    k=z//2 if rem is None else max(1,min(z//2,rem))
                    st=s.D
                    r[0]=[T+1,1]; 
                    if k>1: r.insert(0,[3,k-1])
                    r.insert(0,[2,1])
                    r[-1][0]-=2*k; s.addsteps(k); s.ev['front']+=1
                    s.norm(); s.t=0; continue
                # z==0: pop visit with front x virtual
                r[0]=[T+1,1]; r.insert(0,[2,1]); s.steps+=2*s.D+4; s.v+=1
                s._pop(); continue
            xi=t-1; x,c=r[xi]
            if z==0:
                # pop visit
                if x==0:
                    if T==0: raise Halt('e=0,x=0',s.v)
                    xi=s.split_last(xi); r=s.r; t=xi+1
                    r[xi][0]=2; r[t][0]+=1
                else:
                    xi=s.split_last(xi); r=s.r; t=xi+1
                    r[xi][0]-=1; r[t][0]+=4
                s.steps+=2*s.D+4; s.v+=1
                s._pop(); continue
            if x==0:
                if T==0: raise Halt('e=0,x=0',s.v)
                xi=s.split_last(xi); r=s.r; t=xi+1
                r[xi][0]=2; r[t][0]+=1; r[-1][0]-=2; s.addsteps(1); s.t=xi
                # merge converted block with right neighbour run if equal
                if t+1<len(r) and r[t+1][0]==r[t][0] and t+1<len(r)-1:
                    r[t][1]+=r[t+1][1]; del r[t+1]
                continue
            # x>=1
            if c>1 and z>=2*(x+1) and (rem is None or rem>=x+1):
                # eat whole copies of run (x,c): each costs x+1 visits
                n=min(c, z//(2*(x+1)))
                if rem is not None: n=min(n, rem//(x+1))
                if n>=2:
                    # result: [x, c-n] [2] [4x+3, n-1] [T+4x+1]
                    newT=T+4*x+1
                    seg=[]
                    if c-n>0: seg.append([x,c-n])
                    seg.append([2,1])
                    seg.append([4*x+3,n-1])
                    seg.append([newT,1])
                    r[xi:t+1]=seg
                    s.addsteps(n*(x+1)); r[-1][0]-=2*n*(x+1)
                    s.t = xi+ (1 if c-n>0 else 0)
                    continue
            xi=s.split_last(xi); r=s.r; t=xi+1
            k=min(x,z//2) if rem is None else min(x,z//2,rem)
            r[xi][0]-=k; r[t][0]+=4*k; r[-1][0]-=2*k; s.addsteps(k); s.t=t
    def findtarget_after_refuel(s):
        s.findtarget_dist_ok=True
        r=s.r
        # target is the 2 just left of z
        i=len(r)-1
        if r[i][1]>1: i=s.split_last(i)
        j=s.split_last(i-1); s.t=j
        assert s.r[j][0]==2
    def _pop(s):
        r=s.r; s.ev['pop']+=1
        r.pop()   # z=0 (count 1)
        i=s.split_last(len(r)-1); r=s.r
        if r[i][0]<3: raise Halt('z0 short',s.v)
        r[i][0]-=2
        while r and r[0][0]==0:
            r[0][1]-=1
            if r[0][1]==0: r.pop(0)
        s.norm(); s.t=None


def main():
    what = sys.argv[1]
    if what == 'check':
        import random
        from blocks import step, RL
        N = int(float(sys.argv[2]))
        r = RL(); v = 0; S = {}; B = {}
        want = set(random.Random(1).sample(range(2, N), min(200, N - 2)))
        b = None
        while v < N:
            r.step()
            if r.at_visit():
                v += 1
                if v in want:
                    S[v] = r.steps; B[v] = r.blocks()
        g = RLE([1], steps=1, visits=1)
        for V in sorted(want):
            g.run(maxv=V)
            if g.v != V or g.blocks() != B[V] or g.steps != S[V]:
                print('MISMATCH at visit', V); return
        print('%d sample visits up to %d (%d steps): blocks and step counts agree with the machine' % (len(want), N, r.steps))
    elif what == 'far':
        digits, secs = int(sys.argv[2]), float(sys.argv[3])
        g = RLE([1], steps=1, visits=1); g.log = []
        t0 = time.time(); nxt = 10
        try:
            while nxt <= 10 ** digits and time.time() - t0 < secs:
                g.run(maxsteps=nxt)
                print('steps >= 10^%d: visits ~10^%d, %d runs of blocks, events %s, %.1fs' % (
                    len(str(nxt)) - 1, int(g.v.bit_length() * 0.30103), len(g.r), g.ev, time.time() - t0), flush=True)
                nxt *= 10 if nxt < 10 ** 100 else 10 ** 100
        except Halt as h:
            print('HALT', h)
        print('jumps over a stretch of odd blocks (visit ~10^k, blocks skipped, smallest skipped):')
        for v, n, mn in g.log:
            print('  10^%d %d %s' % (int(v.bit_length() * 0.30103), n, ('~10^%d' % int(mn.bit_length() * 0.30103)) if mn > 10 ** 6 else mn))


if __name__ == '__main__':
    main()
