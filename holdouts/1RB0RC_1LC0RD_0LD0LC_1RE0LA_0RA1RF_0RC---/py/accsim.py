"""Accelerated simulator for the odometer machines 1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA?RF_F---.

usage: python3 accsim.py run STEPS SECONDS LOG [CHECKPOINT]   run from step 20 (or a checkpoint) to STEPS or SECONDS
       python3 accsim.py validate STEPS                        compare every round with ../c/odo.c (the plain machine)

The state is the tape at the moments the head arrives in D at the left end on `1000` (the samples of c/odo.c):
a list [s0, n0, s1, n1, ..., s_m] of stretches s_i (bit strings) and block lengths n_i >= 1 (b = 1000), blank after
s_m.  A round (to the next such moment) is computed by bbtools.symtm on a prefix of the list with the blocks made
symbolic (exact below 2, `v+2` otherwise, raised when the run needs it), followed by an unknown context R (or the
blank end); the result (new prefix and step count, affine in the block lengths) is cached by the shape of the prefix
and reused for every later round of that shape whose blocks meet the thresholds.  Rounds whose result depends on
small exact values are recomputed with all prefix blocks exact.  So every round, regular or irregular, is the
machine's own behaviour on that tape; nothing is assumed about the odometer.  `validate` checks tape and step count
of every round against the plain simulation.
"""
import functools, json, os, subprocess, sys, tempfile, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', '..', '..', 'tools', 'py'))
from bbtools.symtm import Config, run, Machine, Rep, Blank, Ctx, canon, Lin, TouchContext, NeedSplit, Halted, STATES
def at_left_D(c):
    if c.steps.is_zero() or STATES[c.state]!='D': return False
    L=canon(c.left)
    if not (L==[Blank()] or L==[]): return False
    cells=[]
    for t in c.right:
        if isinstance(t,int): cells.append(t)
        elif isinstance(t,Rep):
            if not t.n.surely_ge(1): return False
            cells+=list(t.word)
        else: break
        if len(cells)>=4: break
    return cells[:4]==[1,0,0,0]

B=(1,0,0,0)
def cfg_of(prefix, tail):
    """prefix: list alternating Lin/int blocks and stretch strings, starting with a block; tail 'R' or 'END'"""
    toks=[Blank()]
    for x in prefix:
        if isinstance(x,str): toks+= [int(c) for c in x]
        else: toks.append(Rep(B, x if isinstance(x,Lin) else Lin(x)))
    toks.append(Ctx('R') if tail=='R' else Blank())
    return toks
def subs_toks(toks, v, e):
    out=[]
    for t in toks:
        if isinstance(t,Rep) and v in t.n.vars():
            out.append(Rep(t.word, t.n.subs({v:e}) if hasattr(t.n,'subs') else t.n))
        else: out.append(t)
    return out
def lsub(L, v, e):
    env={x:(e if x==v else Lin(x)) for x in L.vars()}
    r=Lin(L.k)
    for x,a in L.c.items(): r=r+a*env[x]
    return r
def norm_b(right):
    """rebracket rotations of 1000 to (1000)^n; returns list of ints and Rep(B,..), plus tail"""
    R=list(right)
    tail=None
    if R and isinstance(R[-1],Ctx): tail='R'; R=R[:-1]
    elif R and isinstance(R[-1],Blank): tail='END'; R=R[:-1]
    else: raise ValueError('bad tail %r'%(R[-1:],))
    out=[]
    i=0
    # expand constant reps
    E=[]
    for t in R:
        if isinstance(t,Rep):
            if t.n.is_const(): E+=list(t.word)*t.n.k
            else:
                if t.n.k: E.append(Rep(t.word,Lin(0,t.n.c))); E+=list(t.word)*t.n.k
                else: E.append(t)
        else: E.append(t)
    changed=True
    while changed:
        changed=False
        for j,t in enumerate(E):
            if isinstance(t,Rep) and t.word!=B:
                w=t.word
                r=next((r for r in range(1,4) if B[r:]+B[:r]==w),None)
                if r is None: raise ValueError('non-b rep %r'%(t,))
                pre=tuple(B[:r]); post=tuple(B[r:])
                if j>=r and all(isinstance(x,int) for x in E[j-r:j]) and tuple(E[j-r:j])==pre:
                    E[j-r:j+1]=[Rep(B,t.n)]+list(pre); changed=True; break
                if all(isinstance(x,int) for x in E[j+1:j+1+len(post)]) and tuple(E[j+1:j+1+len(post)])==post:
                    E[j:j+1+len(post)]=list(post)+[Rep(B,t.n)]; changed=True; break
                raise ValueError('cannot rebracket %r'%(E,))
    return E, tail
def parse_right(right):
    E,tail=norm_b(right)
    # string with placeholders
    out=[]; cur=''
    for t in E:
        if isinstance(t,int): cur+=str(t)
        else: out.append(cur); out.append(t.n); cur=''
    out.append(cur)
    def split_bits(s):
        parts=[]; i=0; cur=''
        while i<len(s):
            if s.startswith('1000',i):
                n=0
                while s.startswith('1000',i): n+=1; i+=4
                parts.append(cur); parts.append(Lin(n)); cur=''
            else: cur+=s[i]; i+=1
        parts.append(cur); return parts
    flat=[]
    for x in out:
        if isinstance(x,str): flat+=split_bits(x)
        else: flat.append(x)
    merged=[]
    for x in flat:
        if isinstance(x,str):
            if merged and isinstance(merged[-1],str): merged[-1]+=x
            else: merged.append(x)
        else:
            if len(merged)>=2 and merged[-1]=='' and not isinstance(merged[-2],str):
                merged.pop(); merged[-1]=merged[-1]+x
            else: merged.append(x)
    return merged, tail
def round_(M, prefix, tail, maxm=200000):
    m=Machine.parse(M)
    c=Config([], 3, cfg_of(prefix,tail))
    c.left=[Blank()]; c.right=c.right[1:]
    try:
        f=run(m,c,at_left_D,max_moves=maxm)
    except TouchContext as e: return ('touch',None)
    except NeedSplit as e: return ('split',e.args[0])
    except Halted as e: return ('halt',str(e))
    except RuntimeError as e: return ('loop',str(e)[:200])
    return ('ok',f)

T = 2   # blocks >= T are symbolic v+T

class Shape:
    pass

def strip0(s):
    return s.rstrip('0') if s else s

class Sim:
    def __init__(self, M):
        self.M = M
        self.cache = {}
        self.misses = 0
        self.hits = 0
        self.exact = 0
        self.xcache = {}
    def key(self, cfg, d):
        """cfg = [s0, n0, s1, n1, ..., s_m]; d = number of blocks in the prefix; tail R if d < m blocks else END"""
        nb = (len(cfg) - 1) // 2
        end = d >= nb
        items = []
        for i in range(2 * d + 1 if end else 2 * d):
            x = cfg[i]
            items.append(x if isinstance(x, str) else (x if x < T else -1))
        return (tuple(items), end)
    def compute(self, cfg, d, exact=False):
        nb = (len(cfg) - 1) // 2
        end = d >= nb
        pre = []
        vars_ = []
        thr = {}
        for i in range(2 * d + 1 if end else 2 * d):
            x = cfg[i]
            if isinstance(x, str): pre.append(x)
            elif x < T or exact: pre.append(Lin(x))
            else:
                v = 'v%d' % (i // 2); vars_.append((i, v)); thr[v] = T
                pre.append(Lin(v) + T)
        tail = 'END' if end else 'R'
        while True:
            r, info = round_(self.M, pre, tail)
            if r == 'split':
                v = list(info.n.vars())[0]
                # concrete guidance: actual value of the block
                idx = int(v[1:]) * 2 + 1
                actual = cfg[idx] - thr[v]
                if actual > 0:
                    pre = [x if isinstance(x, str) else lsub(x, v, Lin(v) + 1) for x in pre]
                    thr[v] += 1
                    continue
                return ('needexact', None)
            if r == 'touch':
                return ('deeper', None)
            if r == 'halt':
                return ('halt', info)
            if r != 'ok':
                return (r, info)
            res, rt = parse_right(info.right)
            # result blocks must be >=1 for every value satisfying thresholds; if a block could be 0, need exact
            for x in res:
                if not isinstance(x, str) and not x.surely_ge(1):
                    return ('needexact', None)
            if rt == 'R' and res[-1] != '':
                return ('deeper', None)     # last block before R became empty
            # compile
            def comp(L):
                c = L.k; terms = []
                for v, a in L.c.items():
                    terms.append((a, int(v[1:]) * 2 + 1))
                    c -= a * thr[v] if False else 0
                return (L.k, tuple(terms), )
            # Lin is in terms of v where block = v + thr[v]; value v = cfg[idx]-thr[v]
            out = []
            for x in res:
                if isinstance(x, str): out.append(x)
                else: out.append(('L', x.k, tuple((a, int(v[1:]) * 2 + 1, thr[v]) for v, a in x.c.items())))
            st = info.steps
            stc = ('L', st.k, tuple((a, int(v[1:]) * 2 + 1, thr[v]) for v, a in st.c.items()))
            conds = tuple((int(v[1:]) * 2 + 1, t) for v, t in thr.items())
            return ('ok', (out, rt, stc, conds, 2 * d + 1 if end else 2 * d))
    @staticmethod
    def ev(e, cfg):
        _, k, terms = e
        return k + sum(a * (cfg[i] - t) for a, i, t in terms)
    def round(self, cfg):
        """returns (newcfg, steps) or raises"""
        nb = (len(cfg) - 1) // 2
        d = 1 if nb >= 1 else 0
        while True:
            key = self.key(cfg, d)
            ents = self.cache.get(key)
            ent = None
            if ents is not None:
                for e in ents:
                    if e[0] != 'ok': ent = e; break
                    if all(cfg[i] >= t for i, t in e[1][3]): ent = e; break
            if ent is None:
                self.misses += 1
                ent = self.compute(cfg, d)
                if ent[0] == 'needexact':
                    self.exact += 1
                    ent = self.compute(cfg, d, exact=True)
                    if ent[0] == 'needexact': raise RuntimeError('exact run inconsistent')
                    if ent[0] == 'ok':
                        # valid only for these exact values: condition on equality is checked by the exact key
                        xkey = (key, tuple(cfg[i] for i in range(1, ent[1][4], 2)))
                        self.xcache[xkey] = ent
                    # do not cache under the abstract key
                    ent = ent
                else:
                    self.cache.setdefault(key, []).append(ent)
            else:
                self.hits += 1
            if ent[0] == 'deeper':
                d += 1
                if d > nb: raise RuntimeError('deeper beyond end')
                continue
            if ent[0] == 'halt': return ('halt', ent[1])
            if ent[0] != 'ok': raise RuntimeError(str(ent))
            out, rt, stc, conds, used = ent[1]
            new = []
            for x in out:
                new.append(x if isinstance(x, str) else self.ev(x, cfg))
            steps = self.ev(stc, cfg)
            rest = cfg[used:]
            if rt == 'R':
                # new ends with '' before R; rest begins with a stretch
                new[-1] = new[-1] + rest[0]
                new += rest[1:]
            else:
                new[-1] = strip0(new[-1])
            # merge zero blocks
            m = [new[0]]
            for x in new[1:]:
                if isinstance(x, str):
                    if isinstance(m[-1], str): m[-1] += x
                    else: m.append(x)
                elif x == 0:
                    continue
                else:
                    if not isinstance(m[-1], str): m.append('')
                    m.append(x)
            return (m, steps)
    def compute_exact(self, cfg, d):
        raise RuntimeError('needexact at ' + repr(cfg[:2 * d + 2]))


M = os.path.basename(os.path.dirname(HERE))
STD = {"1001": "g0", "1001100": "g1", "100110": "g2", "10011": "g3", "10010": "g4", "0": "s"}
ATOMS = {**STD, "1": "1", "10": "10", "100": "100", "1001101": "a7", "10011010": "a8", "10011011": "a8'",
         "100110110": "a9", "1001101100": "a10"}


@functools.lru_cache(None)
def split(s):
    """the decomposition of a stretch into atoms (an empty block between consecutive atoms) with the fewest
    irregular atoms, then the fewest atoms; None if there is none"""
    if s == "":
        return ()
    best = None
    for w, a in ATOMS.items():
        if s.startswith(w):
            r = split(s[len(w):])
            if r is not None:
                c = (a,) + r
                if best is None or cost(c) < cost(best):
                    best = c
    return best


def cost(c):
    return (sum(1 for a in c if a not in STD.values()), len(c))


def main_run(LIM, SECS, OUT, CK=None):
    s = Sim(M)
    cfg, t, n = ['', 1, '1001'], 20, 0
    if CK:
        ck = json.load(open(CK))
        cfg, t, n = ck['cfg'], ck['t'], ck['n']
    log = open(OUT, 'w')
    seen, multi, first_multi, ten_adj, maxgad = {}, 0, None, 0, 0
    t0 = last = time.time()
    while t < LIM and time.time() - t0 < SECS:
        r = s.round(cfg)
        if r[0] == 'halt':
            log.write(f'HALT in the round after step {t}: {r[1]}\n')
            json.dump({'cfg': cfg, 't': t, 'n': n}, open(OUT + '.halt', 'w'))
            break
        cfg, dt = r
        t += dt
        n += 1
        for x in cfg[2::2]:
            if x not in STD:
                sp = split(x)
                k = x if sp is None else ' '.join(sp)
                if k not in seen:
                    seen[k] = 0
                    log.write(f'{t} new stretch {k}: ' + ' '.join(map(str, cfg[:40])) + '\n')
                    log.flush()
                seen[k] += 1
                if sp is None or len(sp) >= 3:
                    multi += 1
                    first_multi = first_multi or t
                if sp and '10' in sp[:-1]:
                    ten_adj += 1
        maxgad = max(maxgad, len(cfg) // 2)
        if time.time() - last > 60:
            last = time.time()
            log.write(f'# step {t:.4e} rounds {n} gadgets {len(cfg) // 2} k0 {cfg[1]} cache {len(s.cache)}\n')
            log.flush()
            json.dump({'cfg': cfg, 't': t, 'n': n}, open(OUT + '.ckpt', 'w'))
    log.write(f'END step {t} rounds {n} time {time.time() - t0:.0f}s cache {len(s.cache)} maxgadgets {maxgad}\n')
    log.write('stretch counts ' + json.dumps(seen) + '\n')
    log.write(f'rounds with >=3 atoms in a stretch (two adjacent empty blocks): {multi}, first at {first_multi}; '
              f'rounds with the atom 10 before an empty block: {ten_adj}\n')
    log.write('final ' + ' '.join(map(str, cfg)) + '\n')
    json.dump({'cfg': cfg, 't': t, 'n': n}, open(OUT + '.ckpt', 'w'))


def parse(line):
    a, b = line.split('|')
    st, toks = int(a.split()[0]), b.split()
    cfg = ['']
    for i, tk in enumerate(toks):
        if i % 2 == 0:
            k = int(tk)
            if k:
                cfg.append(k)
                cfg.append('')
        else:
            cfg[-1] += tk
    cfg[-1] = cfg[-1].rstrip('0')
    return st, cfg


def main_validate(N):
    exe = os.path.join(tempfile.mkdtemp(), "odo")
    subprocess.run(["gcc", "-O2", "-o", exe, os.path.join(HERE, "..", "c", "odo.c")], check=True)
    p = subprocess.Popen([exe, M, N, '0'], stdout=subprocess.PIPE, text=True)
    s, cur, t, n, bad = Sim(M), None, None, 0, 0
    for line in p.stdout:
        if '|' not in line:
            print('odo:', line.strip())
            continue
        st, cfg = parse(line)
        if cur is None:
            cur, t = cfg, st
            continue
        r = s.round(cur)
        if r[0] == 'halt':
            print('the simulator halts after step', t)
            break
        cur, dt = r
        t += dt
        n += 1
        if t != st or cur != cfg:
            bad += 1
            print('MISMATCH', n, 'sim', t, cur[:12], 'odo', st, cfg[:12])
            cur, t = cfg, st
    print(f'{n} rounds compared (tape and step count), {bad} mismatches, last step {t}, {len(s.cache)} cached shapes')


if __name__ == "__main__":
    if sys.argv[1] == "run":
        main_run(int(float(sys.argv[2])), float(sys.argv[3]), sys.argv[4], *sys.argv[5:6])
    else:
        main_validate(sys.argv[2])
