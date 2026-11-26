#!/usr/bin/env python3
"""Segmented replay of a visit map: generator.

A *visit map* describes a Turing machine at a coarse grain: a state is a frame (one of finitely many tape
shapes) with a few non-negative integer counts, and one visit takes a state to the next one, or halts.  The map
is given as an ordered list of cases (first match wins), each with a guard (linear comparisons and residues of
the counts) and either `halt` or a target frame with affine outputs.

From such a description (a JSON file, see README.md) this program writes

  coq    Map.v: the map on integers (`opz`, the specification), the same map on 63-bit machine integers
         (`ex1`), a generated proof that the two agree (`ex1_ok`), and the segment check `seg` with `seg_ok`.
  c      a C runner for the same map: segment end points, the halting visit if one is met, and near-miss
         counts for every halting case (see `hits`).
  segs   from the C runner's output: one Coq file per segment (J000.v ...) and Final.v, which chains them.
  hits   from the C runner's near-miss counts: an estimate of how many exact hits of each halting case were
         to be expected so far, and per doubling of the run.

Nothing here is trusted by the Coq proof: the C runner only proposes segment end points, and Coq recomputes
each segment.
"""
import ast, json, math, os, re, sys

# ---------------------------------------------------------------- expressions
# A linear form is a dict {atom: coefficient}; an atom is 1 (the constant), ('v', i), ('div', i, m) or
# ('mod', i, m)  (count i divided by / modulo the constant m).

def lin_add(a, b, s=1):
    r = dict(a)
    for k, c in b.items():
        r[k] = r.get(k, 0) + s * c
    return {k: c for k, c in r.items() if c != 0}

def lin_scale(a, s):
    return {k: c * s for k, c in a.items() if c * s != 0}

class Spec:
    def __init__(self, d):
        self.d = d
        self.name = d['name']
        self.machine = d.get('machine', '')
        self.vars = d['vars']
        self.nv = len(self.vars)
        self.frames = d['frames']
        self.nf = len(self.frames)
        self.HALT = self.nf          # tag of the halted state
        self.STUCK = self.nf + 1     # tag for "no case applies" (a gap in the description)
        self.start = d['start']      # [frame, v0, v1, ...]
        self.cases = []
        for n, c in enumerate(d['cases']):
            g = [self.atom(s) for s in c.get('guard', [])]
            if c.get('halt') or c.get('stuck'):
                self.cases.append(dict(n=n, frame=self.frames.index(c['frame']), guard=g, halt=True,
                                       tag=self.HALT if c.get('halt') else self.STUCK, src=c))
            else:
                out = [self.lin(s) for s in c['out']]
                assert len(out) == self.nv, c
                self.cases.append(dict(n=n, frame=self.frames.index(c['frame']), guard=g, halt=False,
                                       to=self.frames.index(c['to']), out=out, src=c))
        # the bound on the counts under which the machine arithmetic is exact
        m = 1
        for c in self.cases:
            for a in c['guard']:
                m = max(m, sum(abs(v) for v in a[1].values()), sum(abs(v) for v in a[2].values()))
            if not c['halt']:
                for o in c['out']:
                    m = max(m, sum(abs(v) for v in o.values()))
        self.bits = 62 - max(1, math.ceil(math.log2(m + 1)))
        self.B = 1 << self.bits

    # --- parsing
    def lin(self, s):
        if isinstance(s, int):
            return {1: s} if s else {}
        return self._lin(ast.parse(str(s), mode='eval').body)

    def _lin(self, e):
        if isinstance(e, ast.Constant) and isinstance(e.value, int):
            return {1: e.value} if e.value else {}
        if isinstance(e, ast.Name):
            return {('v', self.vars.index(e.id)): 1}
        if isinstance(e, ast.UnaryOp) and isinstance(e.op, ast.USub):
            return lin_scale(self._lin(e.operand), -1)
        if isinstance(e, ast.BinOp):
            if isinstance(e.op, ast.Add):
                return lin_add(self._lin(e.left), self._lin(e.right))
            if isinstance(e.op, ast.Sub):
                return lin_add(self._lin(e.left), self._lin(e.right), -1)
            if isinstance(e.op, ast.Mult):
                l, r = self._lin(e.left), self._lin(e.right)
                if set(l) <= {1}:
                    return lin_scale(r, l.get(1, 0))
                if set(r) <= {1}:
                    return lin_scale(l, r.get(1, 0))
            if isinstance(e.op, (ast.FloorDiv, ast.Mod)):
                # (count + c) // m or (count + c) % m, m a constant: one atom.  A negative c is moved up by a
                # multiple of m (floor((x - c) / m) = floor((x + m k - c) / m) - k), so the atom itself never
                # subtracts.
                l = self._lin(e.left)
                vs = [k for k in l if k != 1]
                if (isinstance(e.right, ast.Constant) and e.right.value > 1 and len(vs) == 1 and vs[0][0] == 'v'
                        and l[vs[0]] == 1):
                    m, c = e.right.value, l.get(1, 0)
                    k = -(c // m) if c < 0 else 0
                    if isinstance(e.op, ast.FloorDiv):
                        r = {('div', vs[0][1], m, c + m * k): 1}
                        if k:
                            r[1] = -k
                        return r
                    return {('mod', vs[0][1], m, c + m * k): 1}
        raise ValueError('not a linear expression: ' + ast.dump(e))

    def atom(self, s):
        """A guard atom 'lhs OP rhs' -> (op, L, R) with op in ==, !=, <=, < and L, R with coefficients >= 0."""
        e = ast.parse(s, mode='eval').body
        assert isinstance(e, ast.Compare) and len(e.ops) == 1, s
        l, r = self._lin(e.left), self._lin(e.comparators[0])
        op = {ast.Eq: '==', ast.NotEq: '!=', ast.LtE: '<=', ast.Lt: '<', ast.GtE: '>=', ast.Gt: '>'}[type(e.ops[0])]
        if op in ('>=', '>'):
            l, r = r, l
            op = '<=' if op == '>=' else '<'
        d = lin_add(l, r, -1)      # l - r
        L = {k: c for k, c in d.items() if c > 0}
        R = {k: -c for k, c in d.items() if c < 0}
        return (op, L, R)

    # --- rendering
    def term(self, k, zmode, names):
        if k == 1:
            return None
        if k[0] == 'v':
            return names[k[1]]
        inner = names[k[1]] if k[3] == 0 else '(%s + %d)' % (names[k[1]], k[3])
        return '(%s %s %d)' % (inner, '/' if k[0] == 'div' else 'mod', k[2])

    def show(self, f, names):
        """A linear form as Coq text (same text in Z and in int scope; subtraction last)."""
        pos = [(k, c) for k, c in f.items() if c > 0 and k != 1]
        neg = [(k, -c) for k, c in f.items() if c < 0 and k != 1]
        c0 = f.get(1, 0)
        parts = []
        for k, c in pos:
            t = self.term(k, None, names)
            parts.append(t if c == 1 else '%d * %s' % (c, t))
        if c0 > 0:
            parts.append(str(c0))
        s = ' + '.join(parts) if parts else '0'
        for k, c in neg:
            t = self.term(k, None, names)
            s += ' - ' + (t if c == 1 else '%d * %s' % (c, t))
        if c0 < 0:
            s += ' - %d' % (-c0)
        return s

    def simple(self, f):
        """A form that needs no rewriting: one count or a constant."""
        return len(f) == 0 or (len(f) == 1 and (1 in f or (list(f.values()) == [1] and list(f)[0][0] == 'v')))

    def guard_text(self, g, names):
        if not g:
            return 'true'
        out = []
        for op, L, R in g:
            l, r = self.show(L, names), self.show(R, names)
            if op == '==':
                out.append('(%s =? %s)' % (l, r))
            elif op == '!=':
                out.append('negb (%s =? %s)' % (l, r))
            elif op == '<=':
                out.append('(%s <=? %s)' % (l, r))
            else:
                out.append('(%s <? %s)' % (l, r))
        return ' && '.join(out)

    def consts(self):
        s = {0, 1, self.B, self.HALT, self.STUCK} | set(range(self.nf + 2))
        for c in self.cases:
            for op, L, R in c['guard']:
                for f in (L, R):
                    if set(f) <= {1}:
                        s.add(f.get(1, 0))
                    for k in f:
                        if k != 1 and k[0] in ('div', 'mod'):
                            s.add(k[2])
        return sorted(s)

    # ------------------------------------------------------------ Python (reference interpreter)
    def ev(self, f, x):
        r = 0
        for k, c in f.items():
            if k == 1:
                r += c
            elif k[0] == 'v':
                r += c * x[k[1]]
            elif k[0] == 'div':
                r += c * ((x[k[1]] + k[3]) // k[2])
            else:
                r += c * ((x[k[1]] + k[3]) % k[2])
        return r

    def py_step(self, t, x):
        """One visit on Python integers: (tag, counts)."""
        if t >= self.nf:
            return t, x
        for c in self.cases:
            if c['frame'] != t:
                continue
            ok = True
            for op, L, R in c['guard']:
                l, r = self.ev(L, x), self.ev(R, x)
                ok = ok and {'==': l == r, '!=': l != r, '<=': l <= r, '<': l < r}[op]
            if ok:
                if c['halt']:
                    return c['tag'], x
                y = [self.ev(o, x) for o in c['out']]
                assert min(y) >= 0, ('negative count', c['src'], x)
                return c['to'], y
        return self.STUCK, x

    # ------------------------------------------------------------ Coq
    def coq_map(self, lib='SegReplay', vm=False):
        nv, xs = self.nv, ['v%d' % i for i in range(self.nv)]
        phis = ['φ v%d' % i for i in range(nv)]
        prj = ' '.join('x%d' % i for i in range(nv))
        w = []
        w.append('(** Generated by tools/segreplay/segreplay.py from the visit map "%s"%s.\n'
                 '    [opz] is the map on integers (the specification); [ex1] is the same map on 63-bit machine\n'
                 '    integers; [ex1_ok] proves that they agree while every count is below 2^%d; [seg p n s s\'] checks\n'
                 '    that n visits from s end at s\'.  Tags: %s; %d = halted, %d = no case applies. *)'
                 % (self.name, ' of ' + self.machine if self.machine else '', self.bits,
                    ', '.join('%d = %s' % (i, f) for i, f in enumerate(self.frames)), self.HALT, self.STUCK))
        w.append('From Coq Require Import ZArith Lia Uint63 Bool PArith ZifyUint63.')
        w.append('From %s Require Import Core.' % lib)
        w.append('Local Open Scope Z_scope.')
        w.append('Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).')
        w.append('')
        w.append('Record St := mk { tg : int; %s }.' % '; '.join('x%d : int' % i for i in range(nv)))
        w.append('Record ZS := zmk { ztg : Z; %s }.' % '; '.join('z%d : Z' % i for i in range(nv)))
        w.append('Definition zs (s : St) : ZS := zmk φ (tg s) %s.' % ' '.join('φ (x%d s)' % i for i in range(nv)))
        w.append('')
        w.append('(** The map on integers, frame by frame. *)')
        for f in range(self.nf):
            w.append('Definition opz_%d (%s : Z) : ZS :=' % (f, ' '.join(xs)))
            for c in self.cases:
                if c['frame'] != f:
                    continue
                res = ('zmk %d %s' % (c['tag'], ' '.join(xs)) if c['halt'] else
                       'zmk %d %s' % (c['to'], ' '.join('(%s)' % self.show(o, xs) for o in c['out'])))
                if not c['guard']:
                    w.append('  %s.' % res)
                    break
                w.append('  if %s then %s else' % (self.guard_text(c['guard'], xs), res))
            else:
                w.append('  zmk %d %s.' % (self.STUCK, ' '.join(xs)))
        w.append('Definition opz (s : ZS) : ZS :=')
        w.append('  let \'(zmk t %s) := s in' % ' '.join(xs))
        for f in range(self.nf):
            w.append('  if t =? %d then opz_%d %s else' % (f, f, ' '.join(xs)))
        w.append('  s.')
        w.append('')
        w.append('(** The same map on machine integers. *)')
        w.append('Local Open Scope uint63_scope.')
        for f in range(self.nf):
            w.append('Definition ex_%d (%s : int) : St :=' % (f, ' '.join(xs)))
            for c in self.cases:
                if c['frame'] != f:
                    continue
                res = ('mk %d %s' % (c['tag'], ' '.join(xs)) if c['halt'] else
                       'mk %d %s' % (c['to'], ' '.join('(%s)' % self.show(o, xs) for o in c['out'])))
                if not c['guard']:
                    w.append('  %s.' % res)
                    break
                w.append('  if %s then %s else' % (self.guard_text(c['guard'], xs), res))
            else:
                w.append('  mk %d %s.' % (self.STUCK, ' '.join(xs)))
        w.append('Definition ex1 (s : St) : St :=')
        w.append('  let \'(mk t %s) := s in' % ' '.join(xs))
        for f in range(self.nf):
            w.append('  if t =? %d then ex_%d %s else' % (f, f, ' '.join(xs)))
        w.append('  s.')
        w.append('Definition bnd (s : St) : bool := %s.' % ' && '.join('(x%d s <? %d)' % (i, self.B) for i in range(nv)))
        w.append('Definition eqs (s t : St) : bool := (tg s =? tg t) && %s.'
                 % ' && '.join('(x%d s =? x%d t)' % (i, i) for i in range(nv)))
        w.append('Local Close Scope uint63_scope.')
        w.append('')
        w.append('Ltac datom c := lazymatch c with')
        w.append('  | (?c1 && _)%bool => datom c1')
        w.append('  | negb ?c1 => datom c1')
        w.append('  | (?x =? ?y) => destruct (Z.eqb_spec x y)')
        w.append('  | (?x <=? ?y) => destruct (Z.leb_spec x y)')
        w.append('  | (?x <? ?y) => destruct (Z.ltb_spec x y)')
        w.append('  end; cbn [andb negb].')
        w.append('Ltac split1 := lazymatch goal with |- zs (if ?c then _ else _) = _ => datom c end.')
        w.append('Ltac leaf := unfold zs; cbn [tg %s]; f_equal; first [reflexivity | lia].' % prj)
        cs = self.consts()
        chg = '; '.join('change (φ %d) with %d in *' % (c, c) for c in cs)
        w.append('Ltac consts := %s.' % chg)
        w.append('')
        for f in range(self.nf):
            w.append('Lemma ex_%d_ok %s : %s -> zs (ex_%d %s) = opz_%d %s.'
                     % (f, ' '.join(xs), ' -> '.join('φ %s < %d' % (x, self.B) for x in xs), f, ' '.join(xs), f,
                        ' '.join(phis)))
            w.append('Proof.')
            w.append('  intros. %s' % ' '.join('pose proof (to_Z_bounded %s).' % x for x in xs))
            w.append('  unfold ex_%d, opz_%d. rewrite ?eqb_Z, ?ltb_Z, ?leb_Z.' % (f, f))
            seen = set()
            for c in self.cases:
                if c['frame'] != f:
                    continue
                for op, L, R in c['guard']:
                    for frm in (L, R):
                        if self.simple(frm):
                            continue
                        t = self.show(frm, xs)
                        if t in seen:
                            continue
                        seen.add(t)
                        w.append('  replace (φ (%s)%%uint63) with (%s) by (consts; lia).' % (t, self.show(frm, phis)))
            w.append('  consts.')
            w.append('  repeat split1; leaf.')
            w.append('Qed.')
        w.append('')
        w.append('Lemma ex1_ok s : bnd s = true -> zs (ex1 s) = opz (zs s).')
        w.append('Proof.')
        w.append('  destruct s as [t %s]. unfold bnd, ex1, opz, zs at 2. cbn [tg %s]. intros Hb.' % (' '.join(xs), prj))
        w.append('  rewrite ?andb_true_iff, ?ltb_Z, ?Z.ltb_lt in Hb. rewrite ?eqb_Z. consts.')
        w.append('  repeat (split1; [apply ex_%s; lia|]).' % '_ok || apply ex_'.join(str(f) for f in range(self.nf)) if False else
                 '  repeat (split1; [first [%s]|]).' % ' | '.join('apply ex_%d_ok; lia' % f for f in range(self.nf)))
        w.append('  reflexivity.')
        w.append('Qed.')
        w.append('')
        w.append('Lemma eqs_ok s t : eqs s t = true -> zs s = zs t.')
        w.append('Proof.')
        w.append('  destruct s, t. unfold eqs, zs. cbn [tg %s]. rewrite ?andb_true_iff, ?eqb_Z, ?Z.eqb_eq.' % prj)
        w.append('  intros H. f_equal; lia.')
        w.append('Qed.')
        w.append('')
        w.append('(** The halted state stays put, so "not halted after n visits" covers every earlier visit. *)')
        w.append('Lemma halt_fix z : ztg z = %d -> opz z = z.' % self.HALT)
        w.append('Proof. destruct z. cbn [ztg]. intros ->. reflexivity. Qed.')
        w.append('')
        w.append('Definition one := oneB ex1 bnd.')
        w.append('Definition seg (p : positive) (n : int) (s s\' : St) : bool := Core.seg one eqs p n s s\'.')
        w.append('Theorem seg_ok p n s s\' : seg p n s s\' = true -> zit opz (Z.to_nat φ n) (zs s) = zs s\'.')
        w.append('Proof. exact (Core.seg_ok zs opz one (oneB_ok zs opz ex1 bnd ex1_ok) eqs eqs_ok p n s s\'). Qed.')
        return '\n'.join(w) + '\n'

    # ------------------------------------------------------------ C
    def cexpr(self, f):
        names = ['x[%d]' % i for i in range(self.nv)]
        parts = []
        for k, c in f.items():
            if k == 1:
                parts.append('(%dLL)' % c)
            elif k[0] == 'v':
                parts.append('(%dLL)*(i64)%s' % (c, names[k[1]]))
            else:
                parts.append('(%dLL)*(i64)((%s + %d) %s %d)' % (c, names[k[1]], k[3], '/' if k[0] == 'div' else '%', k[2]))
        return ' + '.join(parts) if parts else '0'

    def cguard(self, g):
        if not g:
            return '1'
        out = []
        for op, L, R in g:
            out.append('(%s) %s (%s)' % (self.cexpr(L), op, self.cexpr(R)))
        return ' && '.join(out)

    def c_runner(self):
        nv = self.nv
        halts = [c for c in self.cases if c['halt'] and c['tag'] == self.HALT]
        start = '%d; u64 x[NV] = {%s}' % (self.frames.index(self.start[0]), ', '.join('%dULL' % v for v in self.start[1:]))
        w = []
        w.append('// Generated by tools/segreplay/segreplay.py from the visit map "%s"%s.' % (self.name, ' of ' + self.machine if self.machine else ''))
        w.append('// usage: run N SEG [ckpt]         follow the orbit to visit N; print the state every SEG visits')
        w.append('//        run pert N G R T SP Q    perturbation probe (see pert below)')
        w.append('#include <stdio.h>\n#include <stdlib.h>\n#include <stdint.h>\n#include <string.h>\n#include <math.h>')
        w.append('typedef long long i64; typedef unsigned long long u64;')
        w.append('#define NV %d\n#define NF %d\n#define NC %d\n#define HALT %d\n#define STUCK %d\n#define BND %dULL' % (nv, self.nf, len(self.cases), self.HALT, self.STUCK, self.B))
        w.append('static int lastcase;')
        w.append('// one visit: 0 = went on, 1 = halted, 2 = no case applies')
        w.append('static inline int step(int *tp, u64 *x) {')
        w.append('  int t = *tp; u64 y[NV];')
        w.append('  switch (t) {')
        for f in range(self.nf):
            w.append('  case %d:' % f)
            closed = False
            for c in self.cases:
                if c['frame'] != f:
                    continue
                g = self.cguard(c['guard'])
                if c['halt']:
                    w.append('    if (%s) { lastcase = %d; *tp = %d; return %d; }' % (g, c['n'], c['tag'], 1 if c['tag'] == self.HALT else 2))
                else:
                    w.append('    if (%s) { %s *tp = %d; %s return 0; }' % (
                        g, ' '.join('y[%d] = (u64)(%s);' % (i, self.cexpr(o)) for i, o in enumerate(c['out'])), c['to'],
                        ' '.join('x[%d] = y[%d];' % (i, i) for i in range(nv))))
                if not c['guard']:
                    closed = True
                    break
            if not closed:
                w.append('    lastcase = NC; *tp = STUCK; return 2;')
        w.append('  }')
        w.append('  return 3;')
        w.append('}')
        w.append('static int big(const u64 *x) { for (int k = 0; k < NV; k++) if (x[k] >= BND) return 1; return 0; }')
        w.append('// Perturbation probe.  At sample visits of the orbit (SP per doubling of the visit index), R copies of the')
        w.append('// state, every count moved by Q times a random amount in [-G, G] (not below 0), are followed for T visits.')
        w.append('// Output per doubling b (visits 2^(b-1) .. 2^b): samples, trials, halted, stuck, visits to the halt summed,')
        w.append('// mean sum of the counts, then the number of halts by case.')
        w.append('static u64 rs = 88172645463325252ULL; static inline u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }')
        w.append('static int pert(u64 N, i64 G, u64 R, u64 T, double SP, i64 Q) {')
        w.append('  int t = %s; u64 i = 0; double nexts = 1, f = pow(2.0, 1.0 / SP); int bin = 0; u64 binend = 1;' % start)
        w.append('  static u64 ns[64], nt[64], nh[64], nk[64], sh[64], pc[64][NC + 1]; static double ssum[64];')
        w.append('  while (i < N && !big(x)) {')
        w.append('    if (i >= binend) { binend <<= 1; bin++; }')
        w.append('    if ((double)i >= nexts) { nexts = nexts * f > nexts + 1 ? nexts * f : nexts + 1; ns[bin]++; u64 sc = 0; for (int k = 0; k < NV; k++) sc += x[k]; ssum[bin] += (double)sc;')
        w.append('      for (u64 r = 0; r < R; r++) { int tt = t; u64 y[NV]; for (int k = 0; k < NV; k++) { i64 v = (i64)x[k] + Q * ((i64)(rnd() % (u64)(2 * G + 1)) - G); y[k] = v < 0 ? x[k] : (u64)v; }')
        w.append('        nt[bin]++; for (u64 j = 0; j < T && !big(y); j++) { int q = step(&tt, y); if (q == 1) { nh[bin]++; sh[bin] += j + 1; pc[bin][lastcase]++; break; } if (q) { nk[bin]++; break; } } } }')
        w.append('    if (step(&t, x)) break; i++;')
        w.append('  }')
        w.append('  for (int b = 0; b < 64; b++) if (ns[b]) { printf("pert %d %llu %llu %llu %llu %llu %.6g", b, ns[b], nt[b], nh[b], nk[b], sh[b], ssum[b] / ns[b]);')
        w.append('    for (int c = 0; c < NC; c++) if (pc[b][c]) printf(" c%d:%llu", c, pc[b][c]); printf("\\n"); }')
        w.append('  return 0;')
        w.append('}')
        w.append('static void show(const char *s, u64 i, int t, const u64 *x) { printf("%s %llu %d", s, i, t); for (int k = 0; k < NV; k++) printf(" %llu", x[k]); printf("\\n"); fflush(stdout); }')
        w.append('int main(int argc, char **argv) {')
        w.append('  if (argc > 7 && !strcmp(argv[1], "pert")) return pert(strtoull(argv[2], 0, 10), atoll(argv[3]), strtoull(argv[4], 0, 10), strtoull(argv[5], 0, 10), atof(argv[6]), atoll(argv[7]));')
        w.append('  u64 N = argc > 1 ? strtoull(argv[1], 0, 10) : 1000000ULL, SEG = argc > 2 ? strtoull(argv[2], 0, 10) : N;')
        w.append('  int t = %s; u64 i = 0; static u64 fc[64][NF]; static u64 vmax[64][NV];' % start)
        w.append('  if (argc > 3) { FILE *f = fopen(argv[3], "r"); if (f) { if (fscanf(f, "%llu %d", &i, &t) != 2) return 9; for (int k = 0; k < NV; k++) if (fscanf(f, "%llu", &x[k]) != 1) return 9; fclose(f); } }')
        w.append('  show("seg", i, t, x);')
        w.append('  int bin = 0; u64 binend = 1; while (binend <= i) { binend <<= 1; bin++; }')
        w.append('  int r = 0;')
        w.append('  while (i < N && !r) {')
        w.append('    u64 stop = i - i % SEG + SEG; if (stop > N) stop = N;')
        w.append('    while (i < stop) {')
        w.append('      if (i >= binend) { binend <<= 1; bin++; }')
        w.append('      fc[bin][t]++;')
        w.append('      for (int k = 0; k < NV; k++) if (x[k] > vmax[bin][k]) vmax[bin][k] = x[k];')
        w.append('      if (big(x)) { r = 4; break; }')
        w.append('      r = step(&t, x); i++;')
        w.append('      if (r) break;')
        w.append('    }')
        w.append('    if (r) break;')
        w.append('    show("seg", i, t, x);')
        w.append('    if (argc > 3) { FILE *f = fopen(argv[3], "w"); fprintf(f, "%llu %d", i, t); for (int k = 0; k < NV; k++) fprintf(f, " %llu", x[k]); fprintf(f, "\\n"); fclose(f); }')
        w.append('  }')
        w.append('  if (r == 1) show("halt", i, t, x);')
        w.append('  if (r == 2) printf("stuck %llu case %d\\n", i, lastcase);')
        w.append('  if (r == 4) printf("overflow %llu\\n", i);')
        w.append('  for (int b = 0; b < 64; b++) { u64 s = 0; for (int f = 0; f < NF; f++) s += fc[b][f]; if (!s) continue;')
        w.append('    printf("bin %d", b); for (int f = 0; f < NF; f++) printf(" %llu", fc[b][f]); printf(" max"); for (int k = 0; k < NV; k++) printf(" %llu", vmax[b][k]); printf("\\n"); }')
        w.append('  return 0;')
        w.append('}')
        return '\n'.join(w) + '\n'

    # ------------------------------------------------------------ segments
    def st(self, t, xs):
        return '(mk %d %s)' % (t, ' '.join(str(v) for v in xs))

    def coq_segs(self, lines, outdir, lib, mod, vm=False):
        """lines: the C runner's output. Writes J*.v and Final.v into outdir; returns the number of segments."""
        pts = []
        for l in lines:
            p = l.split()
            if p and p[0] in ('seg', 'halt'):
                pts.append((p[0], int(p[1]), int(p[2]), [int(v) for v in p[3:]]))
        halted = pts[-1][0] == 'halt'
        segs = []
        for (k0, i0, t0, x0), (k1, i1, t1, x1) in zip(pts, pts[1:]):
            if i1 > i0:
                segs.append((i0, t0, x0, i1, t1, x1))
        cast = 'vm_cast_no_check' if vm else 'native_cast_no_check'
        width = max(3, len(str(len(segs) - 1)))
        names = []
        for j, (i0, t0, x0, i1, t1, x1) in enumerate(segs):
            nm = 'J%0*d' % (width, j)
            names.append(nm)
            n = i1 - i0
            with open(os.path.join(outdir, nm + '.v'), 'w') as f:
                f.write('(* visits %d to %d *)\nFrom Coq Require Import Uint63 PArith.\nFrom %s Require Import Map.\n'
                        'Lemma seg : seg %d %d %s %s = true.\nProof. %s (eq_refl true). Qed.\n'
                        % (i0, i1, mod, n, n, self.st(t0, x0), self.st(t1, x1), cast))
        w = []
        w.append('(** Generated by tools/segreplay/segreplay.py: the segments of "%s" chained. *)' % self.name)
        w.append('From Coq Require Import ZArith Lia Uint63 PArith.')
        w.append('From %s Require Import Core.' % lib)
        w.append('From %s Require Import Map.' % mod)
        for k in range(0, len(names), 20):
            w.append('From %s Require %s.' % (mod, ' '.join(names[k:k + 20])))
        w.append('Local Open Scope Z_scope.')
        w.append('')
        i0, t0, x0 = segs[0][0], segs[0][1], segs[0][2]
        iN, tN, xN = segs[-1][3], segs[-1][4], segs[-1][5]
        w.append('Definition first : St := %s.' % self.st(t0, x0))
        w.append('Definition last : St := %s.' % self.st(tN, xN))
        w.append('')
        N = iN - i0
        lens = sorted(set(s[3] - s[0] for s in segs))
        w.append('(** The %d visits from visit %d to visit %d. *)' % (N, i0, iN))
        w.append('Theorem orbit : zit opz (Z.to_nat %d) (zs first) = zs last.' % N)
        w.append('Proof.')
        w.append('  assert (H := (')
        w.append('  ' + '(zit_chain opz ' * (len(names) - 1) + '(seg_ok _ _ _ _ %s.seg)' % names[0])
        for nm in names[1:]:
            w.append('  (seg_ok _ _ _ _ %s.seg))' % nm)
        w.append('  )).')
        w.append('  match type of H with zit opz ?k _ = _ => replace k with (Z.to_nat %d) in H; [exact H|] end.' % N)
        w.append('  %s lia.' % ' '.join('change (φ %d) with %d.' % (n, n) for n in lens))
        w.append('Qed.')
        w.append('')
        if halted:
            w.append('(** The orbit reaches the halted state. *)')
            w.append('Theorem orbit_halts : ztg (zit opz (Z.to_nat %d) (zs first)) = %d.' % (N, self.HALT))
            w.append('Proof. rewrite orbit. reflexivity. Qed.')
        else:
            w.append('(** No halt among these visits: the halted state stays put, and the last state is not halted. *)')
            w.append('Theorem no_halt : forall j, (j <= Z.to_nat %d)%%nat -> ztg (zit opz j (zs first)) <> %d.' % (N, self.HALT))
            w.append('Proof.')
            w.append('  intros j L E. assert (F : zit opz (Z.to_nat %d) (zs first) = zit opz j (zs first)).' % N)
            w.append('  { replace (Z.to_nat %d) with (j + (Z.to_nat %d - j))%%nat by lia. rewrite zit_add. apply zit_fix, halt_fix, E. }' % (N, N))
            w.append('  rewrite <- F, orbit in E. discriminate E.')
            w.append('Qed.')
        with open(os.path.join(outdir, 'Final.v'), 'w') as f:
            f.write('\n'.join(w) + '\n')
        return names

    # ------------------------------------------------------------ hit estimates
    def hits(self, lines, T):
        """From the probe's output: expected exact hits per doubling of the visit index, and its trend.

        In doubling b (visits 2^(b-1) .. 2^b) a fraction P of the perturbed copies halted within T visits, so a
        state "like the orbit's" halts at a rate of about -ln(1 - P) / T per visit, and the orbit itself is
        expected to meet 2^(b-1) times that many halts while it crosses the doubling."""
        rows = []
        for l in lines:
            p = l.split()
            if not p or p[0] != 'pert':
                continue
            b, ns, nt, nh, nk = (int(v) for v in p[1:6])
            P = nh / nt
            h = 2.0 ** (b - 1) * (-math.log(1 - P) if P < 1 else float('inf')) / T
            rows.append(dict(b=b, samples=ns, trials=nt, halted=nh, stuck=nk, P=P, scale=float(p[7]), h=h,
                             cases={int(c.split(':')[0][1:]): int(c.split(':')[1]) for c in p[8:]}))
        # Summary over the doublings where the probe means something: long enough that the T visits of a copy
        # fit inside the doubling (2^(b-1) >= T), and not saturated.  The two halves show the trend.
        use = [r for r in rows if 2 ** (r['b'] - 1) >= T and r['P'] < 0.2]
        while use and use[-1]['halted'] < 10:
            use.pop()
        fit = None
        if len(use) >= 4:
            pool = lambda rs: sum(r['h'] * r['trials'] for r in rs) / sum(r['trials'] for r in rs)
            k = len(use) // 2
            fit = dict(doublings=[use[0]['b'], use[-1]['b']], halted=sum(r['halted'] for r in use),
                       per_doubling=pool(use), first_half=pool(use[:k]), second_half=pool(use[k:]))
        return dict(T=T, rows=rows, fit=fit)


def main():
    a = sys.argv
    if len(a) < 3:
        print(__doc__)
        return 1
    spec = Spec(json.load(open(a[2])))
    cmd = a[1]
    if cmd == 'coq':
        out = a[3]
        os.makedirs(out, exist_ok=True)
        open(os.path.join(out, 'Map.v'), 'w').write(spec.coq_map())
    elif cmd == 'c':
        open(a[3], 'w').write(spec.c_runner())
    elif cmd == 'segs':
        lines = open(a[3]).read().splitlines()
        vm = '--vm' in a
        mod = a[5] if len(a) > 5 and not a[5].startswith('--') else 'M'
        names = spec.coq_segs(lines, a[4], 'SegReplay', mod, vm)
        print(len(names), 'segments')
    elif cmd == 'hits':
        lines = open(a[3]).read().splitlines()
        r = spec.hits(lines, int(a[4]))
        if '--json' in a:
            json.dump(r, sys.stdout, indent=1)
        else:
            print('doubling  scale      trials   halted  stuck  hits/doubling')
            for x in r['rows']:
                print('%5d  %10.4g %9d %8d %6d  %.4g' % (x['b'], x['scale'], x['trials'], x['halted'], x['stuck'], x['h']))
            f = r['fit']
            if f:
                print('doublings %d to %d (%d halts): %.3g expected hits per doubling; first half %.3g, second half %.3g'
                      % (f['doublings'][0], f['doublings'][1], f['halted'], f['per_doubling'], f['first_half'], f['second_half']))
            else:
                print('too few halts beyond doubling %d for an estimate' % (int(math.log2(r['T'])) + 1))
    else:
        print(__doc__)
        return 1
    return 0

if __name__ == '__main__':
    sys.exit(main())
