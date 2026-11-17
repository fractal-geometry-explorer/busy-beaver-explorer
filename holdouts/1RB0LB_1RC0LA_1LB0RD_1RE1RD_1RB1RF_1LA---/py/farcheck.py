#!/usr/bin/env python3
"""Cross-check of py/tacc.py against the independent exact run data/b1_far.txt (or b2_far.txt) of c/msim.c.

tacc.py (counter macros on the digit model of cdigits.py) is run from blank tape (via the direct run to START) to
the last left-end sample before the first record of data/<m>_far.txt that lies after FROM; that state is written in
the machine's own orientation as a run-length tape and c/msimev.c (an exact macro simulator, independent of
cdigits.py and tacc.py) is run from it.  Every later record of data/<m>_far.txt (msim: the head enters a fresh
blank block on the right) must then appear in the msimev output (every new rightmost cell, cell-exact) at most 64
steps before the msim step, with the same tape (compared as runs of 1s, m2runs.py, up to the last marker run 5: the
end run after it is what the head is writing in between).  The step count of the tacc state is part of the check: msimev counts from it.

usage: python3 py/farcheck.py b1|b2 [FROM]      (FROM default 1e19)
"""
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', '..', '..', 'tools', 'py'))
os.environ.setdefault('BLAST', '1000')
which = sys.argv[1]
os.environ['BMACH'] = which
import tacc as T  # noqa: E402
from m2runs import convert, fmt  # noqa: E402
from lawev import exe, MACH  # noqa: E402

C = T.C
C.use(which)


def far_records(path):
    out = []
    for line in open(path):
        f = line.split()
        if not f or not f[0].isdigit():
            continue
        i = f.index('|')
        out.append((int(f[0]), f[1], f[2:i] + f[i + 1:]))
    return out


def runs_repr(toks):
    toks = list(toks)
    while toks and set(toks[0].split('^')[0]) == {'0'}:
        toks.pop(0)
    while toks and set(toks[-1].split('^')[0]) == {'0'}:
        toks.pop()
    return fmt(convert(toks))


def original_rle(state, path, K=4):
    """the state (mirrored digits) as the machine's own tape: blanks, head (state A of b1 / C of b2) on a 0, then
    the cells, reversed; written for msimev 'rle:' (blocks of K cells, head on the first cell of a block).  The
    visited part is taken to end at the last 1, as it does at almost every sample of the direct run."""
    ctx, digits, last, end = state
    segs = []                                  # mirrored, left to right: (word, count)
    for sh, r in digits:
        segs.append(('1000', r))
        for a, b in C.SPEC.shapes[sh]:
            segs.append(('1' * a + '0' * b, 1))
    segs.append(('1000', last))
    segs.append((C.SPEC.ends[end], 1))
    # original orientation: head cell 0, then the mirrored cells reversed
    orig = [('0', 1)] + [(w[::-1], n) for w, n in reversed(segs) if n and w]
    blocks = []                                # (word, count)
    buf = '0' * (8 * K)                        # blank cells left of the head; head = first cell after them
    head_block = len(buf) // K

    def emit(w, n=1):
        if blocks and blocks[-1][0] == w:
            blocks[-1][1] += n
        else:
            blocks.append([w, n])

    def flush():
        nonlocal buf
        while len(buf) >= K:
            emit(buf[:K])
            buf = buf[K:]
    for w, n in orig:
        if len(w) == K and n > 8:
            need = (K - len(buf)) % K
            buf += (w * 2)[:need]
            flush()
            rot = (w * 2)[need:need + K]
            cells = n * K - need
            whole = cells // K
            emit(rot, whole)
            buf += (rot * 2)[:cells - whole * K]
            flush()
        else:
            buf += w * n
            flush()
    visited = 8 * K + sum(len(w) * n for w, n in orig)   # up to the last 1 (every word of segs starts with a 1)
    buf += '0' * ((-len(buf)) % K + K)
    flush()
    with open(path, 'w') as f:
        f.write('%s %d %d %d\n' % ('A' if which == 'b1' else 'C', head_block, len(blocks), visited))
        for w, n in blocks:
            f.write('%s %d\n' % (w, n))
    return 'rle:' + path


def main():
    frm = float(sys.argv[2]) if len(sys.argv) > 2 else 1e19
    recs = [r for r in far_records(os.path.join(HERE, '..', 'data', which + '_far.txt')) if r[0] > frm]
    first = recs[0][0]
    st, t, _ = T.load('1e6')
    T.LEVEL[0] = 0
    while True:
        st2, s2, n = T.advance(st)
        assert s2 is not None, st2
        if t + s2 >= first:
            break
        st, t = st2, t + s2
    # plain sweeps to the last sample before the record (the macro may have jumped past several)
    while True:
        r = C.SPEC.sweep(st, carry=C.CARRY)
        assert r[0] == 'ok', r
        if t + r[2] >= first:
            break
        st, t = r[1], t + r[2]
    print('tacc state at step', t, C.DG.show(st)[:200], flush=True)
    path = os.path.join(tempfile.gettempdir(), 'farcheck_%s.rle' % which)
    cfg = original_rle(st, path)
    last = recs[-1][0]
    p = subprocess.run([exe('msimev'), MACH[which][0], '4', str(last - t + 1), cfg, 'ABCDEF', '7200'],
                       capture_output=True, text=True)
    events = []                                # msimev: every new rightmost cell, cell-exact
    for line in p.stdout.splitlines():
        f = line.split()
        if f and f[0].isdigit():
            events.append((int(f[0]) + t, f[2:]))
    ok = True
    for step, stt, toks in recs:
        # msim reports at the end of the macro step that enters the fresh block, a few steps after the head
        # reached its first cell; take the last msimev event at most 64 steps before, and compare the tapes as
        # runs of 1s up to the last marker 5 (after it: the end run, which the head is writing in between)
        near = [(e, tk) for e, tk in events if 0 <= step - e < 64]
        if not near:
            print('MISSING record at step', step)
            ok = False
            continue
        e, tk = near[-1]
        a, b = runs_repr(toks).split(), runs_repr(x for x in tk if x != '|').split()
        cut = lambda r: r[:len(r) - r[::-1].index('5')] if '5' in r else r
        same = cut(a) == cut(b)
        ok &= same
        print('record at step %d: msimev event %d steps before, %s (%d runs)' % (
            step, step - e, 'same tape' if same else 'DIFFERENT\n  %s\n  %s' % (' '.join(a)[:300], ' '.join(b)[:300]),
            len(a)))
    print('ALL AGREE' if ok else 'DISAGREEMENT')
    return ok


if __name__ == '__main__':
    sys.exit(0 if main() else 1)
