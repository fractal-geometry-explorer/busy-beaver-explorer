#!/usr/bin/env python3
"""The sweeps of 1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA--- (b1) and of its twin 1RB0LC_1LA0RD_1RA0LA_1RE1RD_1RA1RF_1LC---
(b2) as a relation on DIGIT LISTS, and no halt reduced to a statement about digit lists (28 November 2026).
Writes <folder>/lean/Dsweep.lean.

A digit is a wall and a run: `(w, r)` stands for the cells `w (0001)^r`, where the wall `blk a b` is `0^b 1^a` and
`O` is `0101`.  A sample (the head in state A at the left end) is a list of digits, the one nearest the head first;
its first digit is the end: `blk 1 2` (E: `001 (0001)^z`) or `blk 1 4` (E0: `00001 (0001)^z`).  Z = blk 1 5,
T = blk 3 3.

Every sweep theorem of lean/Stops.lean (stated on tapes) is restated here on digit lists, `d_<name>`: the input is
the theorem's tape cut into digits, and so is the output.  Cutting the output sometimes depends on a run being 0, 1
or more (a run of 0001 blocks next to a 1 or to leftover 0s), or on the first digit of the rest of the tape; then
the theorem is split into those cases (`_c0`, `_c1`, ...), each with its own input and output lists.  The cuts are
done here, and Lean checks each one: the digit lists' tapes equal the theorem's tapes.

The relation `Sw d n d'` (one constructor per case) is then sound: `steps n` takes the sample of `d` to that of
`d'`, n > 0.  `no_halt_of_closed` reduces no halt from blank tape to a statement about digit lists only: a set of
digit lists that holds a sample reached from blank, and from each of whose members some `Sw` step leads back into
it.  Finding that set is the closure step; it is not done here.

    python3 py/dsweep_lean.py b1|b2            write the Lean file
    python3 py/dsweep_lean.py b1|b2 --check    compare with the file
    python3 py/dsweep_lean.py b1 --rules       print the digit rules
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
M = {'b1': '1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---', 'b2': '1RB0LC_1LA0RD_1RA0LA_1RE1RD_1RA1RF_1LC---'}
NS = {'b1': 'H104106', 'b2': 'H44149'}
QA = {'b1': 'A', 'b2': 'C'}
NAMES = re.compile(r'(bottom|bottomT0|bottomE|sweep|borrow|sweepE|sweepE0top)_\w+$|e0toE$')
VARS = ('z', 's', 'v', 'u', 'r')

# ---------------------------------------------------------------- linear counts: {var: coeff, '': const}


def lin_parse(s):
    d = {}
    for t in s.replace(' ', '').split('+'):
        if t.isdigit():
            d[''] = d.get('', 0) + int(t)
        else:
            d[t] = d.get(t, 0) + 1
    return d


def lin_add(a, b):
    d = dict(a)
    for k, x in b.items():
        d[k] = d.get(k, 0) + x
    return {k: x for k, x in d.items() if x}


def lin_lean(d):
    parts = [k if x == 1 else '%d * %s' % (x, k) for k, x in d.items() if k]
    if d.get(''):
        parts.append(str(d['']))
    return ' + '.join(parts) if parts else '0'


def lin_const(d):
    return d.get('', 0)


def lin_vars(d):
    return [k for k in d if k]


def lin_subst(d, sub):
    out = {'': d.get('', 0)}
    for k, x in d.items():
        if k:
            for k2, y in sub.get(k, {k: 1}).items():
                out[k2] = out.get(k2, 0) + x * y
    return {k: x for k, x in out.items() if x}


# ---------------------------------------------------------------- reading the theorems of Stops.lean


def toks(s):
    return re.findall(r'\[[^\]]*\]|\(|\)|[^\s()\[\]]+', s)


def group(ts, j):
    """tokens of a parenthesised group starting after '(' at j-1: (text, index after ')')"""
    depth, e = 1, []
    while True:
        if ts[j] == '(':
            depth += 1
        if ts[j] == ')':
            depth -= 1
            if depth == 0:
                return ' '.join(e), j + 1
        e.append(ts[j])
        j += 1


def parse_term(s):
    ts = toks(s)

    def rec(i):
        res = []
        while True:
            t = ts[i]
            if t == '(':
                # a parenthesised term: everything inside, then ')'
                sub, i = rec(i + 1)
                assert ts[i] == ')', ts[i:i + 4]
                return res + sub, i + 1
            if t == 'cons':
                res.append(('b', 1 if ts[i + 1] == 'true' else 0))
                i += 2
                continue
            if t == 'app':
                res += [('b', 1 if x.strip() == 'true' else 0) for x in ts[i + 1][1:-1].split(',')]
                i += 2
                continue
            if t == 'rep':
                if ts[i + 1] == '(':
                    n, j = group(ts, i + 2)
                else:
                    n, j = ts[i + 1], i + 2
                w = ''.join('1' if x.strip() == 'true' else '0' for x in ts[j][1:-1].split(','))
                res.append(('rep', lin_parse(n), w))
                i = j + 1
                continue
            if t in ('Tc', 'Zc'):
                if ts[i + 1] == '(':
                    lst, j = group(ts, i + 2)
                else:
                    lst, j = ts[i + 1], i + 2
                res.append((t, lst))
                i = j
                continue
            if t == 'L':
                return res + [('L',)], i + 1
            raise ValueError(ts[i:i + 6])
    out, _ = rec(0)
    return out


def theorems(which):
    src = open(os.path.join(ROOT, 'holdouts', M[which], 'lean', 'Stops.lean')).read()
    pat = re.compile(r'theorem (\w+) \(([^)]*) : Nat\)( \(rs : List Nat\))? \(L : Tape\) :\n(.*?) := by', re.S)
    res = []
    for m in pat.finditer(src):
        name = m.group(1)
        if not NAMES.match(name):
            continue
        body = m.group(4)
        cnt = re.match(r'\s*steps \((.*?)\)\s*⟨', body, re.S).group(1)
        lhs, rhs = body.split('= some')
        tape = lambda s: re.search(r'⟨blank, (.*), \.\w⟩', s, re.S).group(1)
        res.append(dict(name=name, args=m.group(2).split(), rs=bool(m.group(3)), count=cnt,
                        inp=parse_term(tape(lhs)), out=parse_term(tape(rhs))))
    return res


# ---------------------------------------------------------------- cutting a tape into digits


class Split(Exception):
    """the cut needs a case split: substitute var by 0, 1, ..., k-1 and by var + k"""

    def __init__(self, var, k):
        Exception.__init__(self, var, k)
        self.var, self.k = var, k


class SplitL(Exception):
    """leftover 0s before the rest of the tape: split on its first digit"""


def normalize(items):
    """rotated runs: (0010)^n 0 0 1 = 0 0 1 (0001)^n (lemma rep_0010)"""
    out = list(items)
    i = 0
    while i < len(out):
        x = out[i]
        if x[0] == 'rep' and x[2] == '0010':
            nxt = out[i + 1:i + 4]
            assert [y[1] if y[0] == 'b' else None for y in nxt] == [0, 0, 1], out
            out[i:i + 4] = [('b', 0), ('b', 0), ('b', 1), ('rep', x[1], '0001')]
        elif x[0] == 'rep':
            assert x[2] == '0001', x
            if not lin_vars(x[1]):      # a fixed number of blocks: just cells
                out[i:i + 1] = [('b', int(c)) for c in x[2] * lin_const(x[1])]
                continue
        i += 1
    return out


def cut(items, tail):
    """items: bits, ('rep', n, '0001'), ('Tc'|'Zc', list), then ('L',).  tail: 'L' (an arbitrary digit list),
    'nil', or ('blk', 'a', 'b') / ('O',) for L = that digit :: L'.  Returns a list of digit tokens:
    ('d', wall, run) with wall ('blk', a, b) | ('O',) and run a lin, or ('Tc'|'Zc', list), then the tail token."""
    items = normalize(items)
    assert items[-1] == ('L',)
    items = items[:-1]
    blocks = []         # ('k', a, b) a block 0^b 1^a; ('R', n) n blocks 0001; ('Tc'|'Zc', lst)
    cb, ca = 0, 0       # current block
    i = 0
    while i < len(items):
        x = items[i]
        if x[0] == 'b':
            if x[1] == 0:
                if ca:
                    blocks.append(('k', ca, cb))
                    cb, ca = 0, 0
                cb += 1
            else:
                assert cb or ca, 'a block with no 0'
                ca += 1
            i += 1
            continue
        if x[0] in ('Tc', 'Zc'):
            assert ca and cb or not (ca or cb), (cb, ca)
            if ca:
                blocks.append(('k', ca, cb))
                cb, ca = 0, 0
            blocks.append(x)
            i += 1
            continue
        n = x[1]
        nxt1 = i + 1 < len(items) and items[i + 1] == ('b', 1)
        need = (1 if (cb and not ca) else 0) + (1 if nxt1 else 0)
        if lin_const(n) < need:
            vs = lin_vars(n)
            assert len(vs) == 1 and n[vs[0]] == 1, n
            raise Split(vs[0], need - lin_const(n))
        if not need and not lin_vars(n) and lin_const(n) == 0:
            i += 1
            continue
        if cb and not ca:           # leftover 0s: the first block 0001 joins them
            ca, cb = 1, cb + 3
            n = lin_add(n, {'': -1})
            blocks.append(('k', ca, cb))
            cb, ca = 0, 0
        elif ca:
            blocks.append(('k', ca, cb))
            cb, ca = 0, 0
        if nxt1:                    # the last block 0001 continues into the following 1s
            n = lin_add(n, {'': -1})
            if n:
                blocks.append(('R', n))
            cb, ca = 3, 1
        else:
            if n:
                blocks.append(('R', n))
        i += 1
    if ca:
        blocks.append(('k', ca, cb))
        cb = 0
    lead0 = cb                      # 0s left over in front of the rest of the tape
    if lead0 and tail == 'L':
        raise SplitL()
    # blocks to digits
    digs = []
    for bl in blocks:
        if bl[0] in ('Tc', 'Zc'):
            digs.append(bl)
        elif bl[0] == 'k' and (bl[1], bl[2]) != (1, 3):
            digs.append(['d', ('blk', bl[1], bl[2]), {}])
        else:
            n = bl[1] if bl[0] == 'R' else {'': 1}
            assert digs and digs[-1][0] == 'd', blocks
            digs[-1][2] = lin_add(digs[-1][2], n)
    # O: b1_1 with no run, then b1_1
    out = []
    for d in digs:
        if (d[0] == 'd' and d[1] == ('blk', 1, 1) and out and out[-1][0] == 'd' and out[-1][1] == ('blk', 1, 1)
                and not out[-1][2]):
            out[-1] = ['d', ('O',), d[2]]
        else:
            out.append(d)
    if lead0:
        if tail == 'nil':
            tl = ('nil',)
        elif tail[0] == 'blk':      # 0^k then 0^b 1^a: the wall gets k more 0s
            tl = ('cons', ('blk', tail[1], tail[2] + '+%d' % lead0), 'q')
        else:                       # 0^k then 0101: 0^(k+1) 1, then 01 with the run
            tl = ('consO', lead0)
    else:
        tl = ('tail', tail)
    return [tuple(d) for d in out], tl


# ---------------------------------------------------------------- Lean text

FF = {0: 'false', 1: 'true'}


def wall_lean(w):
    if w[0] == 'O':
        return 'Wall.O'
    return 'Wall.blk %s %s' % tuple(paren(str(x)) for x in w[1:])


def paren(s):
    return s if re.fullmatch(r'\w+', s) else '(%s)' % s


def dig_lean(d):
    if d[0] == 'Tc':
        return 'Ts (%s)' % d[1], True
    if d[0] == 'Zc':
        return 'Zs (%s)' % d[1], True
    return '(%s, %s)' % (wall_lean(d[1]), lin_lean(d[2])), False


def list_lean(digs, tl):
    """digits ++ tail as a Lean list term"""
    if tl[0] == 'nil':
        acc = '[]'
    elif tl[0] == 'tail':
        t = tl[1]
        acc = {'L': 'L', 'nil': '[]'}.get(t) if isinstance(t, str) else (
            '(Wall.blk %s %s, q) :: L' % (t[1], t[2]) if t[0] == 'blk' else '(Wall.O, q) :: L')
    elif tl[0] == 'cons':
        w = tl[1]
        acc = '(Wall.blk %s (%s), q) :: L' % (w[1], w[2].replace('+', ' + '))
    else:
        acc = '(Wall.blk 1 %d, 0) :: (Wall.blk 1 1, q) :: L' % (tl[1] + 1)
    for d in reversed(digs):
        s, islist = dig_lean(d)
        acc = '%s ++ (%s)' % (s, acc) if islist else '%s :: %s' % (s, acc)
    return acc


def items_lean(items, Lterm):
    """a tape term from items (for the instantiated theorem tape)"""
    acc = Lterm
    for x in reversed(items):
        if x == ('L',):
            continue
        if x[0] == 'b':
            acc = 'cons %s (%s)' % (FF[x[1]], acc)
        elif x[0] == 'rep':
            acc = 'rep (%s) [%s] (%s)' % (lin_lean(x[1]), ', '.join(FF[int(c)] for c in x[2]), acc)
        else:
            acc = '%s (%s) (%s)' % (x[0], x[1], acc)
    return acc


def subst_items(items, sub):
    return [('rep', lin_subst(x[1], sub), x[2]) if x[0] == 'rep' else
            (x[0], subst_text(x[1], sub)) if x[0] in ('Tc', 'Zc') else x for x in items]


def subst_text(s, sub):
    def f(m):
        v = m.group(0)
        return '(%s)' % lin_lean(sub[v]) if v in sub else v
    return re.sub(r'\b[a-z]\b', f, s)


def cases(th):
    """all cases of a theorem: list of (suffix, sub, tail, inp digits, out digits); sub maps each argument to a
    linear count in the case's variables"""
    todo = [('', {}, 'L')]
    done = []
    while todo:
        suf, sub, tail = todo.pop(0)
        try:
            ind = cut(subst_items(th['inp'], sub), tail)
            outd = cut(subst_items(th['out'], sub), tail)
        except Split as e:
            v, k = e.var, e.k
            vals = [('%s%d' % (v, c), {'': c}) for c in range(k)] + [('%s%dp' % (v, k), {v: 1, '': k})]
            for tag, val in vals:
                nsub = {a: lin_subst(sub.get(a, {a: 1}), {v: val}) for a in th['args']}
                todo.append((suf + '_' + tag, nsub, tail))
            continue
        except SplitL:
            for s2, t2 in [('_nil', 'nil'), ('_blk', ('blk', 'a', 'b')), ('_O', ('O',))]:
                todo.append((suf + s2, sub, t2))
            continue
        done.append((suf, sub, tail, ind, outd))
    return done


HAND = r'''
/-! ## Digit lists

A digit `(w, r)` is the wall `w` and then `r` blocks `0001`.  The wall `blk a b` is `0^b 1^a`, and `O` is `0101`.
A sample is the head in state A at the left end of the tape, in front of a list of digits, the nearest first; its
first digit is the end, `blk 1 2` (E) or `blk 1 4` (E0). -/

inductive Wall where
  | blk (a b : Nat)
  | O
  deriving DecidableEq, Repr

def Wall.bits : Wall → List Bool
  | .blk a b => List.replicate b false ++ List.replicate a true
  | .O => [false, true, false, true]

/-- The cells of a list of digits, the first one nearest the head, in front of `t`. -/
def tapeOf : List (Wall × Nat) → Tape → Tape
  | [], t => t
  | (w, r) :: ds, t => app w.bits (rep r [false, false, false, true] (tapeOf ds t))

/-- The sample of a digit list. -/
def cfgOf (ds : List (Wall × Nat)) : Config := ⟨blank, tapeOf ds blank, .@A⟩

/-- T digits (walls `000111`) and Z digits (`000001`) with the given runs. -/
def Ts (rs : List Nat) : List (Wall × Nat) := rs.map (fun r => (Wall.blk 3 3, r))
def Zs (rs : List Nat) : List (Wall × Nat) := rs.map (fun r => (Wall.blk 1 5, r))

theorem tapeOf_append (a b : List (Wall × Nat)) (t : Tape) : tapeOf (a ++ b) t = tapeOf a (tapeOf b t) := by
  induction a with
  | nil => rfl
  | cons d a ih => obtain ⟨w, r⟩ := d; simp [tapeOf, ih]

theorem tapeOf_Ts (rs : List Nat) (t : Tape) : tapeOf (Ts rs) t = Tc rs t := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [Ts, List.map] at ih ⊢; simp only [tapeOf, ih, Tc, Tdig, Wall.bits]; rfl

theorem tapeOf_Zs (rs : List Nat) (t : Tape) : tapeOf (Zs rs) t = Zc rs t := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [Zs, List.map] at ih ⊢; simp only [tapeOf, ih, Zc, Zdig, Wall.bits]; rfl

theorem rep_succ' (n : Nat) (w : List Bool) (s : Tape) : rep (n + 1) w s = rep n w (app w s) :=
  (rep_app_comm n w s).symm

/-- Normal form: a block `0001` in front of a run of them goes behind it. -/
theorem rep_shift (n : Nat) (s : Tape) :
    cons false (cons false (cons false (cons true (rep n [false, false, false, true] s))))
      = rep n [false, false, false, true] (cons false (cons false (cons false (cons true s)))) :=
  (rep_app_comm n [false, false, false, true] s).symm

theorem app_append' (v w : List Bool) (s : Tape) : app (v ++ w) s = app v (app w s) := (app_app v w s).symm

theorem rep_0010 (n : Nat) (s : Tape) :
    rep n [false, false, true, false] (cons false (cons false (cons true s)))
      = cons false (cons false (cons true (rep n [false, false, false, true] s))) :=
  (rep_rotate n [false, false, true] [false, false, false, true] [false, false, true, false] rfl s).symm

theorem blank_zeros (k : Nat) : app (List.replicate k false) blank = blank := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [List.replicate, app, ih]; exact cons_false_blank
'''

TAIL = r'''
/-! ## No halt, reduced to digit lists -/

/-- Every sweep of the relation takes at least one step. -/
theorem Sw.pos {d d' : List (Wall × Nat)} {n : Nat} (h : Sw d n d') : 0 < n := by
  cases h <;> omega

/-- **No halt from blank tape follows from a closed set of digit lists**: a set `I` that holds a sample reached
from blank, and from each of whose members some sweep leads back into `I`. -/
theorem no_halt_of_closed (I : List (Wall × Nat) → Prop) (n0 : Nat) (d0 : List (Wall × Nat))
    (h0 : steps n0 init = some (cfgOf d0)) (hd0 : I d0)
    (hI : ∀ d, I d → ∃ n d', Sw d n d' ∧ I d') : ¬ HaltsFromBlank := by
  have reach : ∀ k, ∃ m d, k ≤ m ∧ steps m init = some (cfgOf d) ∧ I d := by
    intro k
    induction k with
    | zero => exact ⟨n0, d0, Nat.zero_le _, h0, hd0⟩
    | succ k ih =>
      obtain ⟨m, d, hkm, hm, hd⟩ := ih
      obtain ⟨n, d', hs, hd'⟩ := hI d hd
      exact ⟨m + n, d', by have := hs.pos; omega, steps_seq trans hm hs.sound, hd'⟩
  apply not_halts_of_forall
  apply forall_of_unbounded trans (fun m => ∃ d, steps m init = some (cfgOf d))
  · intro k
    obtain ⟨m, d, hkm, hm, _⟩ := reach k
    exact ⟨m, hkm, d, hm⟩
  · rintro m ⟨d, hm⟩
    exact ⟨_, hm⟩
'''


def main():
    which = sys.argv[1]
    qa = QA[which]
    ths = theorems(which)
    NF = ('cfgOf, tapeOf, tapeOf_append, tapeOf_Ts, tapeOf_Zs, Wall.bits, List.replicate, List.cons_append, '
          'List.nil_append, app_append\', app_cons, app_nil, rep_add, rep_succ\', rep_zero, rep_0010, rep_shift, Nat.add_zero')
    dthms, ctors, rules = [], [], []
    only = os.environ.get('DSW_ONLY')
    for th in ths:
        if only and not re.match(only, th['name']):
            continue
        for suf, sub, tail, ind, outd in cases(th):
            nm = 'd_%s%s' % (th['name'], suf)
            args = [a for a in th['args']]
            binders = list(args)
            extra = []
            if tail != 'L' and tail != 'nil':
                extra = ['a', 'b'] if tail[0] == 'blk' else []
                extra += ['q']
            # variables that remain after substitution
            vs = []
            for a in args:
                if a in sub:
                    vs += [k for k in sub[a] if k and k not in vs]
                elif a not in vs:
                    vs.append(a)
            vs += [x for x in extra if x not in vs]
            # the tape that stands for the rest
            if tail == 'L':
                Lt, Ll = 'tapeOf L blank', 'L'
            elif tail == 'nil':
                Lt, Ll = 'blank', '[]'
            elif tail[0] == 'blk':
                Lt, Ll = 'tapeOf ((Wall.blk a b, q) :: L) blank', '(Wall.blk a b, q) :: L'
            else:
                Lt, Ll = 'tapeOf ((Wall.O, q) :: L) blank', '(Wall.O, q) :: L'
            inl = list_lean(ind[0], ('tail', tail))
            outl = list_lean(outd[0], outd[1])
            cnt = subst_text(th['count'], sub)
            inst = ' '.join(paren(lin_lean(sub[a])) if a in sub else a for a in args)
            hasL = tail not in ('nil',)
            bnd = '(%s : Nat)' % ' '.join(vs) if vs else ''
            bnd += ' (rs : List Nat)' if th['rs'] else ''
            bnd += ' (L : List (Wall × Nat))' if tail != 'nil' else ''
            intape = items_lean(subst_items(th['inp'], sub), '(%s)' % Lt)
            outtape = items_lean(subst_items(th['out'], sub), '(%s)' % Lt)
            dthms.append('\n'.join([
                '/-- `%s`%s on digit lists. -/' % (th['name'], (' (case `%s`)' % suf[1:]) if suf else ''),
                'theorem %s %s :' % (nm, bnd),
                '    steps (%s) (cfgOf (%s)) = some (cfgOf (%s)) := by' % (cnt, inl, outl),
                '  have h := %s %s%s (%s)' % (th['name'], inst, ' rs' if th['rs'] else '', Lt),
                '  have e1 : tapeOf (%s) blank = %s := by' % (inl, intape),
                '    simp only [%s]' % NF,
                '  have e2 : tapeOf (%s) blank = %s := by' % (outl, outtape),
                '    simp only [%s%s]' % (NF, ', blank_zeros, cons_false_blank' if tail == 'nil' else ''),
                '  simp only [cfgOf, e1, e2]',
                '  exact h', '']))
            ctors.append('  | %s %s : Sw (%s) (%s) (%s)' % (nm[2:], bnd, inl, cnt, outl))
            names = vs + (['rs'] if th['rs'] else []) + (['L'] if tail != 'nil' else [])
            rules.append((nm, inl, cnt, outl, names))
    # relation
    rel = ['/-- One sweep on digit lists: a constructor for each case of each sweep theorem. -/',
           'inductive Sw : List (Wall × Nat) → Nat → List (Wall × Nat) → Prop'] + ctors + ['']
    sound = ['/-- **The relation is sound**: each sweep is a run of the machine from sample to sample. -/',
             'theorem Sw.sound {d d\' : List (Wall × Nat)} {n : Nat} (h : Sw d n d\') : steps n (cfgOf d) = some (cfgOf d\') := by',
             '  cases h with'] + ['  | %s %s => exact %s %s' % (r[0][2:], ' '.join(r[4]), r[0], ' '.join(r[4])) for r in rules] + ['']
    if '--rules' in sys.argv:
        for r in rules:
            print('%s\n   %s\n   --%s-->  %s' % r[:4])
        return
    head = ('/-! The sweeps of %s on digit lists, and no halt reduced to a closed set of digit lists.  Generated by '
            '`py/dsweep_lean.py %s` in the folder of 1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---; do not edit by '
            'hand. -/' % (M[which], which))
    hand = HAND.replace('.@A', '.%s' % qa)
    out = '\n'.join(['import Stops', '', 'set_option linter.unusedSimpArgs false', '', head, '', 'namespace %s' % NS[which], '', 'open TM', hand] + dthms + rel
                    + sound + [TAIL, 'end %s' % NS[which], ''])
    path = os.path.join(ROOT, 'holdouts', M[which], 'lean', 'Dsweep.lean')
    if '--check' in sys.argv:
        same = os.path.exists(path) and open(path).read() == out
        print('Dsweep.lean', 'current' if same else 'DIFFERS')
        sys.exit(0 if same else 1)
    open(path, 'w').write(out)
    print('wrote', path, len(rules), 'digit rules from', len(ths), 'theorems')


if __name__ == '__main__':
    main()
