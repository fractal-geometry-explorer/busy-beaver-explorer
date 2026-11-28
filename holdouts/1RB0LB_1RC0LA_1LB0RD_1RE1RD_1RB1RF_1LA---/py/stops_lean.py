#!/usr/bin/env python3
"""Lean proofs of the special counter sweeps of 1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA--- (b1) and of its twin
1RB0LC_1LA0RD_1RA0LA_1RE1RD_1RA1RF_1LC--- (b2), for EVERY number of carry digits, written to <folder>/lean/Stops.lean.

`lean/Chain.lean` proves the sweeps whose carry stops on a Z or an O digit after a top T digit with at least one
block.  The exact rule table (data/rule_table_b1.txt) has more stop parts: the odd walls b1_1, b2_2, b1_6, b1_7,
b3_5 and the pairs of walls (b1_1 b1_2), (b1_2 b1_2), (b1_1 b3_1), (b5_3 O), and the borrows, where the top T digit
has no block left.  For each stop part W (with the runs it reads) this file proves, by `bbtools.symtm.prove` on the
machine itself and then by the chain lemmas of Chain.lean, the sweep for every list of T digits in front of it:

  bottom_W    no T digit: the carry stops on W itself                       (one symbolic run, all run lengths)
  bottomT0_W  only one T digit, with no block: a borrow at the bottom      (one symbolic run)
  sweep_W     T digits rs, then a top T digit with s + 1 blocks             (stopW_W, then `sweepGen`)
  borrow_W    T digits rs, then one with r blocks, then one with none       (borrowW_W, then `sweepGen`)

Every list of T digits is [], [0], rs ++ [s + 1] or rs ++ [r, 0], so for these stop parts every chain is covered.
The result is stated as the machine leaves it, `Zc rs (app 000001 M)`: the T digits rs become Z digits, and M is
the rest of the tape after the stop.

The far end (added 28 November 2026): after the pairs (b2_3 b1_2) and (b2_3 b1_1) the way back costs 6 steps per
block and the sweep ends at the other kind of sample, E0 (`0^inf A> 0 0 0 0 1 (0001)^z`): `bottomE_W` (no T digit),
`sweepE_W` (a top T digit of `s + 1` blocks) and `sweepE0top_W` (a top T digit with no block), through `retE`,
`endE0` and `sweepGenE0`.  From E0, `e0toE`: 8 steps to an E sample, whatever the tape, the end run becoming an O
digit.  With Chain.lean, this covers every stop part of the rule table.

    python3 py/stops_lean.py b1|b2            write the Lean file
    python3 py/stops_lean.py b1|b2 --check    compare with the file
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
sys.path.insert(0, os.path.join(ROOT, 'tools', 'py'))
from bbtools import symtm  # noqa: E402
from bbtools.symtm import Config, Ctx, Blank, Rep, lin  # noqa: E402
from bbtools.machine import Machine, STATES  # noqa: E402

M = {'b1': '1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---', 'b2': '1RB0LC_1LA0RD_1RA0LA_1RE1RD_1RA1RF_1LC---'}
NS = {'b1': 'H104106', 'b2': 'H44149'}
REL = {'b1': {}, 'b2': {'A': 'C', 'B': 'A', 'C': 'B'}}   # b2 is b1 with A -> C, B -> A, C -> B
WALL = {'Z': '000001', 'O': '0101', 'T': '000111'}

# stop parts: (Lean name, walls far-first as in the rule table, their runs)
SHAPES = [
    ('Z', ('Z',), ('v',)), ('O', ('O',), ('v',)), ('b1_1', ('b1_1',), ('v+1',)), ('b2_2', ('b2_2',), ('v',)),
    ('b1_6', ('b1_6',), ('v',)), ('b1_7', ('b1_7',), ('v',)), ('b3_5', ('b3_5',), ('v',)),
    ('b1_1_b1_2', ('b1_2', 'b1_1'), ('v', 0)), ('b1_2_b1_2', ('b1_2', 'b1_2'), ('v', 0)),
    ('b1_1_b3_1', ('b3_1', 'b1_1'), ('v', 0)), ('b5_3_O', ('O', 'b5_3'), ('u', 'v')),
]
# stop parts after which the sweep ends at E0
SHAPES_E0 = [('b2_3_b1_2', ('b1_2', 'b2_3'), ('v', 0)), ('b2_3_b1_1', ('b1_1', 'b2_3'), ('v+1', 0))]


def wall(n):
    if n in WALL:
        return WALL[n]
    a, b = n[1:].split('_')
    return '0' * int(b) + '1' * int(a)


def cells(walls, runs):
    """the stop part in the machine's own orientation, the digit nearest the head first"""
    out = []
    for w, r in reversed(list(zip(walls, runs))):
        out.append(' '.join(wall(w)))
        if r != 0:
            out.append('(0001)^%s' % r)
    return ' '.join(out)


def describe(walls, runs):
    return ', then '.join('%s (%s blocks)' % (w, r) for w, r in reversed(list(zip(walls, runs))))


def relabel(s, rel):
    return ''.join(rel.get(ch, ch) for ch in s)


def run_to(m, s, stop):
    return symtm.run(m, Config.parse(s), stop, max_moves=50000, rotate=True)


def split_m(right):
    """N = 0^6 0 0 1 M for the tokens N of a return boundary: (M tokens, Lean proof of the equation)"""
    t = list(right)
    if t[:9] == [0] * 8 + [1]:
        return t[9:], 'rfl'
    if t[:5] == [0] * 5 and isinstance(t[5], Rep) and t[5].word == (0, 0, 0, 1) and t[5].n.surely_ge(1):
        return [Rep((0, 0, 0, 1), t[5].n - lin(1))] + t[6:], 'rfl'
    if t[:6] == [0] * 6 and isinstance(t[6], Rep) and t[6].word == (0, 0, 1, 0) and t[6].n.surely_ge(1):
        n1 = (t[6].n - lin(1)).lean()
        return ([Rep((0, 0, 0, 1), t[6].n - lin(1)), 0] + t[7:],
                'by rw [rep_rotate (%s) [false, false, true] [false, false, false, true] [false, false, true, false] '
                'rfl, ← rep_app_comm]; rfl' % n1)
    raise ValueError('not a return boundary: %r' % t)


def main():
    which = sys.argv[1]
    rel = REL[which]
    m = Machine.parse(M[which])
    A = STATES.index(rel.get('A', 'A'))
    back = lambda c: c.state == A and len(c.left) == 4 and isinstance(c.left[0], Ctx) and c.left[1:] == [1, 1, 1]
    sample = lambda c: (c.state == A and len(c.left) == 1 and isinstance(c.left[0], Blank) and not c.steps.is_zero()
                        and c.right[:3] == [0, 0, 1])
    pieces, sweeps, e0pieces, e0sweeps = [], [], [], []
    qa = rel.get('A', 'A')
    for name, walls, runs in SHAPES:
        cl = cells(walls, runs)
        vs = sorted({r for r in runs if r != 0 for r in [r.split('+')[0]]})
        what = describe(walls, runs)
        for kind, start, doc in [
                ('bottom', '0^inf %s> 0 0 1 (0001)^z %s L' % (qa, cl),
                 'No T digit: the carry stops on %s at the bottom.' % what),
                ('bottomT0', '0^inf %s> 0 0 1 (0001)^z 0 0 0 1 1 1 %s L' % (qa, cl),
                 'A borrow at the bottom: one T digit with no block, then %s.' % what)]:
            fin = run_to(m, start, sample)
            text, _ = symtm.prove(m, '%s_%s' % (kind, name), Config.parse(start), fin, doc=doc, rotate=True,
                                  count_first=True, max_seg=400)
            pieces.append(text)
        for kind, top, tops, tvars, doc in [
                ('stopW', '(1110)^s+1', '[s + 1]', ['s'],
                 'The carry stops on %s after a top T digit of `s + 1` blocks.' % what),
                ('borrowW', '(1110)^r 1 1 1 0 1 1', '[r, 0]', ['r'],
                 'A borrow: the carry stops on %s after a T digit of `r` blocks and one with no block.' % what)]:
            start = 'X 1 1 1 0 1 1 %s D> %s L' % (top, cl)
            fin = run_to(m, start, back)
            text, _ = symtm.prove(m, '%s_%s' % (kind, name), Config.parse(start), fin, doc=doc, rotate=True,
                                  count_first=True, max_seg=400)
            pieces.append(text)
            K = fin.steps.lean()
            mt, hN = split_m(fin.right)
            allv = sorted(set(vs) | set(tvars))
            S = symtm.right_term(Config.parse(start).right)
            Mt = symtm.right_term(mt)
            tl = [symtm.parse_lin(x) for x in tops.strip('[]').split(', ')]
            tot = sum((lin(4) * t + lin(6) for t in tl), lin(0)) + fin.steps + lin(21)
            sname = 'sweep_%s' % name if kind == 'stopW' else 'borrow_%s' % name
            sdoc = ('**The sweep stopping on %s, for every list `rs` of T digits** in front of the top one (%s).  The '
                    'T digits of `rs` become Z digits with the same runs, the end run gains 2 blocks, and `M` is what '
                    'the stop leaves.' % (what, 'which has `s + 1` blocks' if kind == 'stopW' else
                                           'a T digit of `r` blocks, then one with no block'))
            sweeps.append('\n'.join([
                '/-- %s -/' % sdoc,
                'theorem %s (z %s : Nat) (rs : List Nat) (L : Tape) :' % (sname, ' '.join(allv)),
                '    steps (12 * z + cost rs + (%s))' % tot.lean(),
                '      ⟨blank, app [false, false, true] (rep z [false, false, false, true] (Tc (rs ++ %s) (%s))), .%s⟩' % (tops, S, qa),
                '      = some ⟨blank, app [false, false, true] (rep (z + 2) [false, false, false, true] (Zc rs (app [false, false, false, false, false, true] (%s)))), .%s⟩ := by' % (Mt, qa),
                '  have h := sweepGen z (%s) rs %s (by simp) (%s) _ (%s) (fun X => %s_%s %s X L) (%s)' % (
                    K, tops, S, Mt, kind, name, ' '.join(allv), hN),
                '  rw [show fcost %s + (%s) + 21 = %s by simp [fcost] <;> omega] at h' % (tops, K, tot.lean()),
                '  exact h', '']))

    # ---- the far end: E to E0 and back
    qb = rel.get('B', 'B')
    Bq = STATES.index(qb)
    P8 = [0] * 7 + [1]
    bndE = lambda c: (c.state == Bq and len(c.left) == 4 and isinstance(c.left[0], Ctx) and c.left[1:] == [1, 1, 1]
                      and c.right[:8] == P8 and not c.steps.is_zero())
    samp0 = lambda c: (c.state == A and len(c.left) == 1 and isinstance(c.left[0], Blank) and not c.steps.is_zero()
                       and c.right[:1] == [0])
    for nm, start, stop, doc in [
            ('retE', 'X 1 1 1 0 1 1 (1110)^r 1 1 1 %s> 0 0 0 0 0 0 0 1 M' % qb, bndE,
             'On the way back towards E0, one more T digit becomes a Z digit with the same run.'),
            ('endE0', '0^inf 1 (1011)^z 1 0 1 1 1 %s> 0 0 0 0 0 0 0 1 M' % qb, samp0,
             'Back to the sample: the end run gains a block and the end becomes E0.'),
            ('e0toE', '0^inf %s> 0 0 0 0 1 (0001)^z L' % qa, samp0,
             '**From an E0 sample, whatever the rest of the tape:** 8 steps to the next sample, an E sample, the end '
             'run having become an O digit.')]:
        fin = run_to(m, start, stop)
        text, _ = symtm.prove(m, nm, Config.parse(start), fin, doc=doc, rotate=True, count_first=True, max_seg=400)
        e0pieces.append(text)
    for name, walls, runs in SHAPES_E0:
        cl = cells(walls, runs)
        vs = sorted({r.split('+')[0] for r in runs if r != 0})
        what = describe(walls, runs)
        start = '0^inf %s> 0 0 1 (0001)^z %s L' % (qa, cl)
        fin = run_to(m, start, samp0)
        text, _ = symtm.prove(m, 'bottomE_%s' % name, Config.parse(start), fin, rotate=True, count_first=True,
                              max_seg=400, doc='No T digit: the carry stops on %s and the sweep ends at E0.' % what)
        e0pieces.append(text)
        for kind, top, tops, tvars in [('stopE', '(1110)^s+1', '[s + 1]', ['s']), ('stopE0', '', '[0]', [])]:
            start = 'X 1 1 1 0 1 1 %s D> %s L' % (top, cl)
            fin = run_to(m, start, bndE)
            assert fin.right[:8] == P8
            doc = 'The carry stops on %s after a top T digit of %s, and goes back towards E0.' % (
                what, '`s + 1` blocks' if tvars else 'no block')
            text, _ = symtm.prove(m, '%s_%s' % (kind, name), Config.parse(start), fin, doc=doc, rotate=True,
                                  count_first=True, max_seg=400)
            e0pieces.append(text)
            K = fin.steps.lean()
            allv = sorted(set(vs) | set(tvars))
            S = symtm.right_term(Config.parse(start).right)
            Mt = symtm.right_term(fin.right[8:])
            tl = [symtm.parse_lin(x) for x in tops.strip('[]').split(', ')]
            tot = sum((lin(4) * t + lin(6) for t in tl), lin(0)) + fin.steps + lin(14)
            sname = ('sweepE_%s' if tvars else 'sweepE0top_%s') % name
            sdoc = ('**The sweep from E to E0 stopping on %s, for every list `rs` of T digits** in front of a top one '
                    'with %s.  The T digits of `rs` become Z digits with the same runs, the end becomes E0 with one '
                    'more block, and `M` is what the stop leaves.' % (what, '`s + 1` blocks' if tvars else 'no block'))
            e0sweeps.append('\n'.join([
                '/-- %s -/' % sdoc,
                'theorem %s (z %s : Nat) (rs : List Nat) (L : Tape) :' % (sname, ' '.join(allv)),
                '    steps (10 * z + costE rs + (%s))' % tot.lean(),
                '      ⟨blank, app [false, false, true] (rep z [false, false, false, true] (Tc (rs ++ %s) (%s))), .%s⟩' % (tops, S, qa),
                '      = some ⟨blank, app [false, false, false, false, true] (rep (z + 1) [false, false, false, true] (Zc rs (app [false, false, false, false, false, true] (%s)))), .%s⟩ := by' % (Mt, qa),
                '  have h := sweepGenE0 z (%s) rs %s (by simp) (%s) (%s) (fun X => %s_%s %s X L)' % (
                    K, tops, S, Mt, kind, name, ' '.join(allv)),
                '  rw [show fcost %s + (%s) + 14 = %s by simp [fcost] <;> omega] at h' % (tops, K, tot.lean()),
                '  exact h', '']))
    hand = open(os.path.join(HERE, 'stops_lean.lean.in')).read()
    for q in 'AB':
        hand = hand.replace('.%s⟩' % q, '.@%s⟩' % q)
    for q in 'AB':
        hand = hand.replace('.@%s⟩' % q, '.%s⟩' % rel.get(q, q))
    head = ('The special counter sweeps of %s (py/cdigits.py): every stop part of the rule table besides the Z and O '
            'stops of Chain.lean, the borrows, and the far end (E to E0 and back), for every number of carry digits '
            'and all run lengths.  '
            'Generated by `py/stops_lean.py %s` in the folder of 1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---; do not '
            'edit by hand.' % (M[which], which))
    out = symtm.rules_file('Chain', NS[which], pieces, head)
    end = 'end %s' % NS[which]
    out = out.rstrip()[:-len(end)] + '\n'.join(e0pieces) + '\n' + hand + '\n' + '\n'.join(sweeps) + '\n'.join(e0sweeps) + end + '\n'
    path = os.path.join(ROOT, 'holdouts', M[which], 'lean', 'Stops.lean')
    if '--check' in sys.argv:
        same = os.path.exists(path) and open(path).read() == out
        print('Stops.lean', 'current' if same else 'DIFFERS')
        sys.exit(0 if same else 1)
    open(path, 'w').write(out)
    print('wrote', path, len(pieces) + len(e0pieces), 'pieces,', len(sweeps) + len(e0sweeps), 'sweeps')


if __name__ == '__main__':
    main()
