#!/usr/bin/env python3
"""Check the digit-list sweeps of lean/Dsweep.lean (py/dsweep_lean.py) against the exact sweeps of py/cdigits.py
(28 November 2026).

The digit rules of Dsweep.lean are matched here in Python, from the same case list that writes the Lean file.  For
each state given, the next `--sweeps N` sweeps are run with cdigits (C.SPEC.sweep, a symbolic run of the machine),
and each one is compared with the unique matching digit rule: the same next digit list and the same step count.
A state that no rule matches is reported (that is where a closed set would have to stop).

    python3 py/dsweep_check.py b1|b2 STATES.txt [--sweeps N] [--every K]
        STATES.txt: lines `sweeps steps [r]W ... [z] END` (the STATELOG of py/lean.py, or a FULLLOG of py/tacc.py)
"""
import collections
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import dsweep_lean as D  # noqa: E402

E_END = {'E': ('blk', 1, 2), 'E0': ('blk', 1, 4)}


def wall_of(name):
    if name == 'Z':
        return ('blk', 1, 5)
    if name == 'T':
        return ('blk', 3, 3)
    if name == 'O':
        return ('O',)
    a, b = name[1:].split('_')
    return ('blk', int(a), int(b))


def to_digits(st):
    """a cdigits state (flag, digits far-first, end run, end) -> digit list, nearest the head first.  cdigits counts
    the E0 end `00001 (0001)^z` as `0 (0001)^(z+1)`."""
    return [(E_END[st[3]], st[2] - (1 if st[3] == 'E0' else 0))] + [(wall_of(w), r) for w, r in reversed(st[1])]


def canon(ds):
    """merge b1_1 (no run) followed by b1_1 into O, as the cut does"""
    out = []
    for w, r in ds:
        if w == ('blk', 1, 1) and out and out[-1][0] == ('blk', 1, 1) and out[-1][1] == 0:
            out[-1] = (('O',), r)
        else:
            out.append((w, r))
    return out


def lin_eval(d, env):
    return sum(x * (1 if k == '' else env[k]) for k, x in d.items())


def wall_eval(w, env):
    if w[0] == 'O':
        return w
    return ('blk',) + tuple(x if isinstance(x, int) else eval_str(x, env) for x in w[1:])


def eval_str(s, env):
    return int(eval(re.sub(r'\b([a-z])\b', lambda m: str(env[m.group(1)]), s.replace('+', ' + '))))


def chain_pat(txt):
    """'rs ++ [s + 1]' -> list of lin patterns for the top part"""
    m = re.fullmatch(r'\s*\(?rs\)? \+\+ \[(.*)\]\s*', txt)
    if m:
        return [D.lin_parse(x.replace('(', '').replace(')', '')) for x in m.group(1).split(',')]
    assert txt.strip() == 'rs', txt
    return []


def bind(pat, val, env):
    """match a linear pattern (at most one variable, coefficient 1) against a number"""
    vs = D.lin_vars(pat)
    c = D.lin_const(pat)
    if not vs:
        return val == c
    v, = vs
    assert pat[v] == 1
    x = val - c
    if x < 0:
        return False
    if v in env:
        return env[v] == x
    env[v] = x
    return True


class Rule:
    def __init__(self, th, suf, sub, tail, ind, outd):
        self.name = 'd_%s%s' % (th['name'], suf)
        self.th, self.sub, self.tail, self.ind, self.outd = th, sub, tail, ind, outd
        self.count = D.subst_text(th['count'], sub)

    def match(self, ds):
        env = {}
        i = 0
        for tok in self.ind[0]:
            if tok[0] == 'Tc':
                tops = chain_pat(tok[1])
                j = i
                while j < len(ds) and ds[j][0] == ('blk', 3, 3):
                    j += 1
                ch = [r for _, r in ds[i:j]]
                if len(ch) < len(tops):
                    return None
                for p, r in zip(tops, ch[len(ch) - len(tops):]):
                    if not bind(p, r, env):
                        return None
                env['rs'] = ch[:len(ch) - len(tops)]
                i = j
                continue
            if i >= len(ds):
                return None
            w, r = ds[i]
            pw = tok[1]
            if pw[0] == 'O':
                if w != ('O',):
                    return None
            elif w != pw:
                return None
            if not bind(tok[2], r, env):
                return None
            i += 1
        rest = ds[i:]
        t = self.tail
        if t == 'nil':
            if rest:
                return None
        elif t != 'L':
            if not rest:
                return None
            w, q = rest[0]
            if t[0] == 'O':
                if w != ('O',):
                    return None
            else:
                if w[0] != 'blk':
                    return None
                env['a'], env['b'] = w[1], w[2]
            env['q'] = q
            rest = rest[1:]
        env['L'] = rest
        return env

    def apply(self, env):
        out = []
        for tok in self.outd[0]:
            if tok[0] == 'Zc':
                out += [(('blk', 1, 5), r) for r in env['rs']]
            elif tok[0] == 'Tc':
                raise AssertionError
            else:
                out.append((wall_eval(tok[1], env), lin_eval(tok[2], env)))
        tl = self.outd[1]
        if tl[0] == 'tail':
            t = tl[1]
            if t == 'L':
                pass
            elif t == 'nil':
                pass
            elif t[0] == 'blk':
                out.append((('blk', env['a'], env['b']), env['q']))
            else:
                out.append((('O',), env['q']))
        elif tl[0] == 'cons':
            out.append((('blk', env['a'], env['b'] + int(tl[1][2].split('+')[1])), env['q']))
        elif tl[0] == 'consO':
            out += [(('blk', 1, tl[1] + 1), 0), (('blk', 1, 1), env['q'])]
        out += env['L'] if self.tail != 'nil' else []
        return out

    def steps(self, env):
        rs = env.get('rs', [])
        s = self.count.replace('costE rs', str(sum(10 * r + 14 for r in rs))).replace(
            'cost rs', str(sum(12 * r + 16 for r in rs)))
        return eval_str(s, env)


def rules(which):
    out = []
    for th in D.theorems(which):
        for suf, sub, tail, ind, outd in D.cases(th):
            out.append(Rule(th, suf, sub, tail, ind, outd))
    return out


def step(R, ds):
    """the matching rules: [(rule, next digits, steps)]"""
    res = []
    for r in R:
        env = r.match(ds)
        if env is not None:
            res.append((r, r.apply(env), r.steps(env)))
    return res


def show(ds, k=8):
    def w(x):
        return 'O' if x[0] == 'O' else {(1, 5): 'Z', (3, 3): 'T', (1, 2): 'b1_2', (1, 4): 'b1_4'}.get(
            x[1:], 'b%d_%d' % x[1:])
    return ' '.join('[%s]%s' % (r if r < 10 ** 6 else '%.2e' % r, w(x)) for x, r in ds[:k]) + (
        ' ...' if len(ds) > k else '')


def main():
    which, path = sys.argv[1], sys.argv[2]
    nsw = int(sys.argv[sys.argv.index('--sweeps') + 1]) if '--sweeps' in sys.argv else 1
    every = int(sys.argv[sys.argv.index('--every') + 1]) if '--every' in sys.argv else 1
    import caccel as C
    import lean as LN
    C.use(which)
    R = rules(which)
    used = collections.Counter()
    bad = nomatch = n = 0
    for k, line in enumerate(open(path)):
        if k % every:
            continue
        st, T, _ = LN.parse_shown(line)
        for _ in range(nsw):
            ds = to_digits(st)
            m = step(R, ds)
            r = C.SPEC.sweep(st, carry=C.CARRY)
            if r[0] != 'ok':
                print('cdigits sweep failed at step %d: %s' % (T, r[0]))
                break
            st2, s2 = r[1], r[2]
            exp = canon(to_digits(st2))
            n += 1
            if not m:
                nomatch += 1
                print('NO RULE at step %.6e: %s' % (float(T), show(ds, 12)))
            elif len(m) > 1 and len({(tuple(x[1]), x[2]) for x in m}) > 1:
                bad += 1
                print('AMBIGUOUS at step %.6e: %s' % (float(T), [x[0].name for x in m]))
            else:
                rule, got, s = m[0]
                used[rule.name] += 1
                if canon(got) != exp or s != s2:
                    bad += 1
                    print('MISMATCH %s at step %.6e:\n  from %s\n  rule %s (%d steps)\n  exact %s (%d steps)' % (
                        rule.name, float(T), show(ds, 12), show(got, 12), s, show(exp, 12), s2))
            st, T = st2, T + s2
    print('%d sweeps compared: %d mismatches, %d with no rule; %d of %d rules used' % (
        n, bad, nomatch, len(used), len(R)))
    for name, c in sorted(used.items(), key=lambda x: -x[1]):
        print('  %8d  %s' % (c, name))
    sys.exit(0 if bad == 0 and nomatch == 0 else 1)


if __name__ == '__main__':
    main()
