"""autoprove: run symbolically from start until pred(cfg), then prove() to that config; returns lean text"""
import sys
import os; sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '../../../tools/py'))
from bbtools.symtm import Config, Blank, Rep, canon, try_cross, try_rotate, step, prove
from bbtools.machine import Machine, STATES
def cfg_str(c):
    def tok(t):
        if isinstance(t, Rep):
            return f"({''.join(map(str,t.word))})^{t.n}".replace(' ', '')
        return str(t)
    l = canon(c.left); r = canon(c.right)
    return ' '.join(map(tok, l)) + f" {STATES[c.state]}> " + ' '.join(map(tok, r))
def find(M, start, pred, maxmoves=100000, rotate=True):
    m = Machine.parse(M); c = Config.parse(start)
    for i in range(maxmoves):
        x = try_cross(m, c)
        if x is None and rotate:
            c2 = c.copy(); rot = try_rotate(c2)
            if rot is not None:
                x = try_cross(m, c2)
                if x is not None: c = c2
        if x is None: step(m, c)
        if pred(c): return c
    raise RuntimeError('not found')
def auto(M, name, start, pred, doc=None, **kw):
    c = find(M, start, pred)
    end = cfg_str(c)
    t, f = prove(M, name, start, end, doc=doc, rotate=True, **kw)
    return t, end, f.steps
def at_right(state):
    return lambda c: c.state == STATES.index(state) and len(c.right) == 1 and isinstance(c.right[0], Blank)
def has_rep(word):
    return lambda c: any(isinstance(t, Rep) and t.word == word for t in c.left)
