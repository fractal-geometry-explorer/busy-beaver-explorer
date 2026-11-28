#!/usr/bin/env python3
"""Turn a Lean frame map written by pattern matching into a segreplay description.

usage: lean2spec.py FILE.lean DEF START [MACHINE] > spec.json
   DEF     name of the definition, e.g. next   (`def next : Ph -> Option Ph` followed by `| .f a b => some (.g ..)` lines)
   START   the first frame, e.g. "g 0 1"

Patterns may be a literal, a name, `(name + c)` or `_`; a result is `none` (halt) or `some (.frame args)`.
Lean tries the alternatives in order, and so does the description, so the two agree case by case.
"""
import json, re, sys

def split_args(s):
    out, depth, cur = [], 0, ''
    for ch in s.strip():
        if ch == '(':
            depth += 1
        if ch == ')':
            depth -= 1
        if ch.isspace() and depth == 0:
            if cur:
                out.append(cur)
            cur = ''
        else:
            cur += ch
    if cur:
        out.append(cur)
    return out

def main():
    path, name, start = sys.argv[1], sys.argv[2], sys.argv[3]
    machine = sys.argv[4] if len(sys.argv) > 4 and not sys.argv[4].startswith('--') else ''
    lines = open(path).read().splitlines()
    k = next(i for i, l in enumerate(lines) if re.match(r'\s*def\s+%s\b' % re.escape(name), l))
    rows, cur = [], None
    for l in lines[k + 1:]:
        if re.match(r'\s*\|', l):
            if cur is not None:
                rows.append(cur)
            cur = l
        elif cur is not None and l.strip() and l[0].isspace() and not l.strip().startswith('--'):
            cur += ' ' + l.strip()
        else:
            break
    if cur is not None:
        rows.append(cur)
    rows = [re.match(r'\s*\|\s*\.(\w+)\s*(.*?)\s*=>\s*(.*?)\s*$', l).groups() for l in rows]
    arity, frames = {}, []
    for f, pats, res in rows:
        if f not in arity:
            arity[f] = len(split_args(pats)); frames.append(f)
    nv = max(arity.values())
    cases = []
    for f, pats, res in rows:
        guard, env = [], {}
        for i, p in enumerate(split_args(pats)):
            p = p.strip()
            if p.startswith('(') and p.endswith(')'):
                p = p[1:-1].strip()
            if re.fullmatch(r'\d+', p):
                guard.append('x%d == %s' % (i, p))
            elif p == '_':
                pass
            elif re.fullmatch(r'_\s*\+\s*(\d+)', p):
                guard.append('x%d >= %s' % (i, p.split('+')[1].strip()))
            elif re.fullmatch(r'[A-Za-z_]\w*', p):
                env[p] = 'x%d' % i
            else:
                m = re.fullmatch(r'([A-Za-z_]\w*)\s*\+\s*(\d+)', p)
                assert m, ('pattern', p)
                guard.append('x%d >= %s' % (i, m.group(2)))
                env[m.group(1)] = '(x%d - %s)' % (i, m.group(2))
        if res == 'none':
            # a catch-all `none` row means "not one of the described configurations", not a halt
            if guard or '--catchall-halts' in sys.argv:
                cases.append(dict(frame=f, guard=guard, halt=True))
            else:
                cases.append(dict(frame=f, guard=guard, stuck=True))
            continue
        m = re.fullmatch(r'some\s*\(\s*\.(\w+)\s*(.*)\)', res)
        assert m, ('result', res)
        if m.group(1) not in arity:
            arity[m.group(1)] = len(split_args(m.group(2))); frames.append(m.group(1))
        sub = lambda a: re.sub(r'\b(?!min\b)[A-Za-z_]\w*', lambda t: env[t.group(0)], a).replace('/', '//')
        args = [sub(a) for a in split_args(m.group(2))]
        # `min (A) (B)` (one such term, possibly repeated): two cases, A <= B and B < A
        mins = set()
        for a in args:
            p = a.find('min')
            while p >= 0:
                q, parts = p + 3, []
                for _ in range(2):
                    while a[q].isspace():
                        q += 1
                    assert a[q] == '(', ('min argument', a)
                    d, s0 = 0, q
                    while True:
                        d += a[q] == '('
                        d -= a[q] == ')'
                        q += 1
                        if d == 0:
                            break
                    parts.append(a[s0:q])
                mins.add((a[p:q], parts[0], parts[1]))
                p = a.find('min', q)
        assert len(mins) <= 1, ('several min terms', res)
        variants = [(guard, args)]
        if mins:
            whole, A, B = mins.pop()
            variants = [(guard + ['%s <= %s' % (A, B)], [a.replace(whole, A) for a in args]),
                        (guard, [a.replace(whole, B) for a in args])]
        for g, outs in variants:
            cases.append(dict(frame=f, guard=g, to=m.group(1), out=outs + ['0'] * (nv - len(outs))))
    st = start.split()
    spec = dict(name='%s of %s' % (name, path.split('/')[-1]), machine=machine, source=path, lean_def=name, lean_start=start,
                vars=['x%d' % i for i in range(nv)], frames=frames,
                start=[st[0]] + [int(v) for v in st[1:]] + [0] * (nv - len(st) + 1), cases=cases)
    print(json.dumps(spec, indent=1))

if __name__ == '__main__':
    main()
