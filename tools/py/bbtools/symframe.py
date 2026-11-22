"""Framed Lean proofs of the rules of `symtm.py`: the same symbolic run, but each piece of the trace is proved on the
few cells it touches, for every tape beyond them, and the pieces are chained by unification.

`symtm.prove` states every intermediate configuration in full (two per piece), so a rule whose tape carries a long
literal tail (dozens of words that the run never looks at) gives a proof of megabytes.  Here a run of single steps
becomes

    have wI : ∀ L R : Tape, steps k ⟨<cells read on the left> L, <cells read on the right> R, .Q⟩ = some ⟨..⟩ := fun _ _ => rfl

(the window is every cell the head reads or ends on, so the lemma holds for all L and R), a crossing is `TM.cross_r`
/ `TM.cross_l` with its two tapes left to unification, and a re-bracketing is `TM.rep_rotate` on the repeat next to
the head.  The proof ends with `steps_seq trans (w0 _ _) (steps_seq trans (...) ...)`: Lean fills in each L and R
from the configuration the previous piece ends in.  Only the start and the end configurations are written out.

`prove_framed(machine, name, start, end, ...)` has the arguments and result of `symtm.prove`.
"""
from .machine import Machine, STATES
from . import symtm
from .symtm import (Config, Rep, Blank, Ctx, Lin, run, left_term, right_term, cfg_term, _word, ProofError,
                    TouchContext, NeedSplit, Halted, same_config, lin)


def _sym(t):
    if isinstance(t, int):
        return t
    if isinstance(t, Rep):
        return t.word[0]
    if isinstance(t, Blank):
        return 0
    raise ProofError(f"head on {t}")


def _take(tokens, cells):
    """Tokens from the front of `tokens` covering at least `cells` cells (a repeat counts with its constant number of
    copies; a blank ends the window).  Returns (window, closed)."""
    out, got = [], 0
    for t in tokens:
        if got >= cells:
            break
        out.append(t)
        if isinstance(t, Blank):
            return out, True
        if isinstance(t, Ctx):
            raise ProofError("window reaches a context")
        got += 1 if isinstance(t, int) else len(t.word) * max(t.n.k, 0)
    return out, False


def _window(m, group):
    """The piece of single steps `group` (list of (before, after)): the window of the first configuration."""
    a, b = group[0][0], group[-1][1]
    p, touched = 0, set()
    for before, after in group:
        touched.add(p)
        sym = _sym(before.right[0])
        tr = m.table[before.state][sym]
        p += 1 if tr[1] == 1 else -1
    touched.add(p)
    need_r = max([q for q in touched if q >= 0], default=-1) + 1
    need_l = max([-q for q in touched if q < 0], default=0)
    wr, cr = _take(a.right, need_r)
    wl_rev, cl = _take(list(reversed(a.left)), need_l)
    wl = list(reversed(wl_rev))
    outer_l = a.left[:len(a.left) - len(wl)]
    outer_r = a.right[len(wr):]
    if b.left[:len(outer_l)] != outer_l or (outer_r and b.right[len(b.right) - len(outer_r):] != outer_r):
        raise ProofError("a piece changes the tape outside its window")
    bl = b.left[len(outer_l):]
    br = b.right[:len(b.right) - len(outer_r)] if outer_r else b.right
    return wl, wr, bl, br, cl, cr


def _side_terms(wl, wr, cl, cr):
    lt = left_term(([] if cl else [Ctx("L")]) + wl)
    rt = right_term(wr + ([] if cr else [Ctx("R")]))
    return lt, rt


class Library:
    """The piece lemmas of several rules, each stated once (they recur: the same few windows and crossings at every
    visit of the head).  `prefix` names them; `text()` is the Lean to put before the rules."""

    def __init__(self, prefix):
        self.prefix, self.names, self.items = prefix, {}, []

    def name(self, stmt, proof):
        if stmt not in self.names:
            self.names[stmt] = f"{self.prefix}{len(self.items)}"
            self.items.append((self.names[stmt], stmt, proof))
        return self.names[stmt]

    def text(self):
        return "".join(f"theorem {n} : {st} :={pf}\n" for n, st, pf in self.items)


def prove_framed(m, name, start, end, nsteps=None, doc=None, max_moves=100000, cross=True, rotate=False,
                 max_seg=None, count_first=True, lib=None):
    """As `symtm.prove`.  With `lib` (a Library) the piece lemmas go there and the proof refers to them."""
    own = lib is None
    if own:
        lib = Library(f"{name}_p")
    m = Machine.parse(m) if isinstance(m, str) else m
    start = Config.parse(start) if isinstance(start, str) else start
    end = Config.parse(end) if isinstance(end, str) else end
    trace = []
    try:
        fin = run(m, start.copy(), lambda c: c.state == end.state and not c.steps.is_zero() and same_config(c, end),
                  max_moves=max_moves, cross=cross, trace=trace, rotate=rotate)
    except (TouchContext, NeedSplit, Halted, RuntimeError) as e:
        raise ProofError(f"{name}: {type(e).__name__}: {e}")
    if nsteps is not None and lin(nsteps) != fin.steps:
        raise ProofError(f"{name}: the run takes {fin.steps} steps, not {nsteps}")
    # pieces: ('steps', [(before, after)...]) | ('cross', before, after, Cross) | ('rot', before, after, Rotate)
    pieces = []
    for ev in trace:
        if ev[0] == "step":
            if pieces and pieces[-1][0] == "steps" and (max_seg is None or len(pieces[-1][1]) < max_seg):
                pieces[-1][1].append((ev[1], ev[2]))
            else:
                pieces.append(("steps", [(ev[1], ev[2])]))
        else:
            pieces.append(ev)
    vs = sorted(start.vars() | end.vars())
    ctxs = []
    for x in start.contexts() + end.contexts():
        if x not in ctxs:
            ctxs.append(x)
    binders = (f" ({' '.join(vs)} : Nat)" if vs else "") + (f" ({' '.join(ctxs)} : Tape)" if ctxs else "")
    lines = []
    if doc:
        lines.append(f"/-- {doc} -/")
    lines.append(f"theorem {name}{binders} :")
    lines.append(f"    steps ({fin.steps.lean()}) {cfg_term(start)} = some {cfg_term(fin)} := by")
    terms, counts = [], []
    for i, pc in enumerate(pieces):
        if pc[0] == "steps":
            grp = pc[1]
            a, b = grp[0][0], grp[-1][1]
            wl, wr, bl, br, cl, cr = _window(m, grp)
            la, ra = _side_terms(wl, wr, cl, cr)
            lb, rb = _side_terms(bl, br, cl, cr)
            bs = [x for x, c in (("L", cl), ("R", cr)) if not c]
            wv = sorted(set().union(*[t.n.vars() for t in wl + wr + bl + br if isinstance(t, Rep)]))
            bind = (f"∀ {' '.join(wv)} : Nat, " if wv else "") + (f"∀ {' '.join(bs)} : Tape, " if bs else "")
            lam = f"fun {' '.join('_' for _ in wv + bs)} => rfl" if wv + bs else "rfl"
            nm = lib.name(f"{bind}steps {len(grp)} ⟨{la}, {ra}, .{STATES[a.state]}⟩ = some ⟨{lb}, {rb}, "
                          f".{STATES[b.state]}⟩", f" {lam}")
            terms.append(nm + "".join(" _" for _ in wv + bs))
            counts.append(str(len(grp)))
        elif pc[0] == "rot":
            _, a, b, x = pc
            if x.rev:
                raise ProofError("reverse rotation not supported")
            j = len(x.x)
            q = f".{STATES[a.state]}"
            if x.side == "l":
                wl = a.left[len(a.left) - 1 - j:]
                lhs = left_term([Ctx("L")] + wl)
                rhs = left_term([Ctx("L")] + b.left[len(b.left) - 1 - j:])
                xs, ys, y2s = tuple(reversed(x.x)), tuple(reversed(x.w)), tuple(reversed(x.w2))
                stmt = f"∀ L R : Tape, steps 0 ⟨{lhs}, R, {q}⟩ = some ⟨{rhs}, R, {q}⟩"
            else:
                lhs = right_term(a.right[:j + 1] + [Ctx("R")])
                rhs = right_term(b.right[:j + 1] + [Ctx("R")])
                xs, ys, y2s = x.x, x.w, x.w2
                stmt = f"∀ L R : Tape, steps 0 ⟨L, {lhs}, {q}⟩ = some ⟨L, {rhs}, {q}⟩"
            ctx = "L" if x.side == "l" else "R"
            pf = (f" fun L R => by\n  simp only [steps_zero, show {lhs} = {rhs} from\n"
                  f"    rep_rotate ({x.n.lean()}) {_word(xs)} {_word(ys)} {_word(y2s)} rfl ({ctx})]")
            if x.n.vars():
                vs_ = " ".join(sorted(x.n.vars()))
                stmt = f"∀ {vs_} : Nat, {stmt}"
                pf = pf.replace(" fun L R =>", f" fun {vs_} L R =>", 1)
                nm = lib.name(stmt, pf)
                terms.append(f"{nm} {' '.join('_' for _ in x.n.vars())} _ _")
            else:
                terms.append(f"{lib.name(stmt, pf)} _ _")
            counts.append("0")
        else:
            _, a, b, x = pc
            q = f".{STATES[a.state]}"
            if x.d == "r":
                u_, w_, v_ = tuple(reversed(x.u)), x.w, tuple(reversed(x.v))
                nm = lib.name(f"∀ L R : Tape, steps {x.s} ⟨app {_word(u_)} L, app {_word(w_)} R, {q}⟩ = "
                              f"some ⟨app {_word(u_)} (app {_word(v_)} L), R, {q}⟩", " fun _ _ => rfl")
                terms.append(f"cross_r trans {nm} ({x.k.lean()}) _ _")
            else:
                w_ = tuple(reversed(x.w))
                nm = lib.name(f"∀ L R : Tape, steps {x.s} ⟨app {_word(w_)} L, app {_word(x.u)} R, {q}⟩ = "
                              f"some ⟨L, app {_word(x.u)} (app {_word(x.v)} R), {q}⟩", " fun _ _ => rfl")
                terms.append(f"cross_l trans {nm} ({x.k.lean()}) _ _")
            counts.append(f"({x.k.lean()}) * {x.s}")
    if not terms:
        raise ProofError(f"{name}: the run is empty")
    total = counts[-1]
    for c in reversed(counts[:-1]):
        total = f"{c} + ({total})"
    chain = f"({terms[-1]})"
    for t in reversed(terms[:-1]):
        chain = f"(steps_seq trans ({t}) {chain})"
    lines.insert(3 if doc else 2, f"  have hn : {total} = {fin.steps.lean()} := by omega")
    lines.append(f"  exact steps_congr trans hn ({chain})")
    txt = "\n".join(lines) + "\n"
    if own:
        txt = lib.text() + "\n" + txt
    return txt, fin
