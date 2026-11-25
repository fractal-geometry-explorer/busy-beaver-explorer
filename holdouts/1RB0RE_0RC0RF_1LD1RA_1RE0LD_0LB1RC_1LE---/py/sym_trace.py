"""Record the steps of py/sym_engine.py, for the Lean generator (py/gen_front.py)."""
import sym_engine as E
from sym_lin import Lin
import sym_lin

_step = E.St.step
_chunk = E.St.chunk


def snap(s):
    return dict(mode=s.mode, ph=s.ph, lb=list(s.lb) if s.lb is not None else None, k=s.k, us=list(s.us),
                F=list(s.F) if s.F is not None else None, l=s.l, nops=len(s.ops), H=s.H, cons=list(s.cons))


def step(s):
    before = snap(s); s._kind = None
    if s.mode == "ps":
        kind = "arun" if (s.ph == "A" and E.ge(s.k, 3)) else "ps"
    else:
        kind = None
    _step(s)
    if kind is None:
        kind = s._kind or ("start" if s.mode == "ps" else "arith")
    elif s.mode == "mom":
        kind = "pdone"
    s.trace = s.trace + [("step", kind, before, snap(s), s.ops[before["nops"]:], getattr(s, "_chunk", None))]
    s._chunk = None


def chunk(s, e, minus):
    s._chunk = ("chunk", e, minus)
    _chunk(s, e, minus)


E.St.step = step
E.St.chunk = chunk
E.St._kind = None
E.St._chunk = None
