"""Cross-check of the record transducer of busycoq PR 64 (Halt_1RB0RB_0LC1RA.v, module Sim356)
against direct simulation of 1RB0RB_0LC1RA_1RD1LC_1LA1LE_1LF0LD_---0LA.

Record: 0^inf encL(U) 1 B> 0^inf, U a list of pairs (head of list = rightmost pair), a = 11, b = 01.
`sweep` is a transcription of the Coq definitions (dscan, sig, ovf/oscan).

  python3 pr64_sweep.py test [steps]     compare every record of the direct run with the model
  python3 pr64_sweep.py levels [sweeps]  iterate the model and print the level ends (overflows)
"""
import sys
TM = "1RB0RB_0LC1RA_1RD1LC_1LA1LE_1LF0LD_---0LA"
La, Lb = 'a', 'b'
LC = {La: 1, Lb: 0}
LCP = {'Pa': 1, 'Pb': 0, 'Pc': 1}
RCP = {'Pa': 1, 'Pb': 1, 'Pc': 0}
SIG = {'Pa': Lb, 'Pb': La, 'Pc': Lb}

def dscan(s, w, v):
    # iterative transcription; w, v python lists with head at index 0
    i = 0
    while True:
        if i == len(w):
            return ('turn', [La], v) if s == 0 else (('halt',) if s == 1 else ('ovf', v))
        x = w[i]
        if x == La:
            if s == 0: v = ['Pb'] + v
            elif s == 1: return ('turn', [Lb, Lb] + w[i+1:], v)
            else: v = ['Pa'] + v
        else:
            if s == 0: s = 1; i += 1; continue
            elif s == 1: s = 2; v = ['Pc', 'Pa'] + v; i += 1; continue
            else: s = 0; v = ['Pb'] + v; i += 1; continue
        i += 1

def oscan(carry, v, acc):
    AL = {(0, 1): La, (1, 1): Lb, (1, 0): Lb}
    for x in v:
        y = AL.get((carry, LCP[x]))
        if y is None: return None
        acc = [y] + acc
        carry = RCP[x]
    return acc if carry == 0 else None

def sweep(U):
    if not U or U[0] != Lb: return ('stuck',)
    r = dscan(0, U[1:], ['Pb', 'Pc'])
    if r[0] == 'turn':
        w, v = r[1], r[2]
        return ('next', [SIG[x] for x in reversed(v)] + w, False)   # rev_append (map sig v) w
    if r[0] == 'halt': return ('halt',)
    v = r[1]
    if v and LCP[v[0]] == 1:
        U2 = oscan(0, v, [La])
        return ('next', U2, True) if U2 is not None else ('stuck',)
    return ('stuck',)

def parse_tm(s):
    t = {}
    for i, part in enumerate(s.split('_')):
        for b in (0, 1):
            tr = part[3*b:3*b+3]
            t[(i, b)] = None if tr[2] == '-' else (int(tr[0]), 1 if tr[1] == 'R' else -1, ord(tr[2]) - 65)
    return t

def records(steps):
    t = parse_tm(TM); tape = {}; pos = 0; st = 0; maxp = 0
    for n in range(steps):
        if st == 1 and pos > maxp - 1 and tape.get(pos, 0) == 0 and all(tape.get(p, 0) == 0 for p in range(pos, maxp + 1)):
            yield n, tape, pos
        tr = t[(st, tape.get(pos, 0))]
        if tr is None:
            yield ('HALT', n); return
        tape[pos] = tr[0]; pos += tr[1]; st = tr[2]; maxp = max(maxp, pos)

def decode(tape, pos):
    lo = min(p for p, v in tape.items() if v) if any(tape.values()) else pos
    cells = [tape.get(p, 0) for p in range(lo, pos)]
    if cells[-1] != 1: return None
    cells = cells[:-1]
    if len(cells) % 2: cells = [0] + cells
    U = []
    for i in range(0, len(cells), 2):
        c = (cells[i], cells[i+1])
        if c == (1, 1): U.append(La)
        elif c == (0, 1): U.append(Lb)
        else: return None
    return U[::-1]

def test(steps):
    U = None; k = 0; ovfs = []
    for rec in records(steps):
        if rec[0] == 'HALT': print('halt at', rec[1]); return False
        n, tape, pos = rec
        D = decode(tape, pos)
        if D is None: continue
        if U is None:
            if D == [Lb, Lb, La, La]: U = D; print('first record U0 = bbaa (PR: after 31 steps) at step', n)
            continue
        r = sweep(U)
        assert r[0] == 'next', r
        if r[2]: ovfs.append(n)
        if r[1] != D:
            print('MISMATCH at step', n); return False
        U = D; k += 1
    print('test ok: %d consecutive records agree with the PR-64 sweep, %d steps; level ends (records after an overflow) at steps %s' % (k, steps, ovfs))
    return True

def levels(nsweeps):
    U = [Lb, Lb, La, La]
    for i in range(nsweeps):
        r = sweep(U)
        if r[0] != 'next': print('sweep', i, r[0], 'len', len(U)); return
        if r[2]: print('level end after sweep', i, 'new length', len(r[1]), 'prefix', ''.join(reversed(r[1]))[:60])
        U = r[1]
    print('after', nsweeps, 'sweeps: length', len(U))

if __name__ == '__main__':
    if sys.argv[1] == 'test': test(int(float(sys.argv[2])) if len(sys.argv) > 2 else 700000)
    else: levels(int(float(sys.argv[2])))
