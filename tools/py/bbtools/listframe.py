"""Run-length frame maps: frames whose parameters are lists, fitted from the machine, checked against it, and written
as Lean case tables for `tools/lean/TM/ListFrame.lean`.

A *frame* is the configuration at a head turn (just before a step whose direction differs from the step before),
written run-length: `(q, L, R)` with `L` the runs left of the head, nearest first, and `R` the runs from the head
cell rightwards, each run a pair `(bit, length)`, both sides ending in blank tape.  Frames are kept in normal form
(`normB`: no empty runs, neighbours of different symbols, no last run of 0s), exactly as `TM.normB` in Lean.

A *case* is a pattern on the first runs of both sides (each run's length an exact number, or `v + k` for a fresh
variable `v`, meaning "at least k"; the rest of each side a context list, or nothing when the pattern reaches blank
tape) and the frame the machine reaches at its next head turn, computed by a symbolic run of `bbtools.symtm` from
the pattern, so it holds for all values of the variables and all contexts.  The frame map applies the first case
in the table that matches.  Machines whose head, between two turns, crosses only a few run boundaries (a counter
whose digits are runs, a word of blocks the head works on locally) have a finite table of such cases even though
the number of runs on the tape grows without bound.

API
  Fitter(M, T=4)                       the case table of machine M, built on demand
    .fit(steps)                        run M from blank tape for `steps` steps; every frame at a head turn that no
                                       case matches gets a new case (window: the runs the head visits until the
                                       next turn; run lengths >= T become variables).  Returns statistics.
    .check(steps)                      run M again and compare, at every head turn, the frame the table predicts
                                       with the machine's; returns (frames, mismatches, unmatched)
    .predict(frame)                    the table's next frame (normal form) or None
    .cases                             the list of Case objects, in table order
    .lean(ns, machine_module)          (pieces_text, cases_text): Lean files with one `symtm` theorem per case and
                                       the table `cases : List (RLCase trans)`, each case's `sound` proved
  frames(M, steps)                     iterate (step, frame) at head turns of the run from blank tape
  first_frame(M), lean_start(M, ns, K)  the first frame, and a Lean file reaching it from blank tape
                                       (`blank_frame`) and checking K frames of the map (`checkF`, native_decide)
  NGramClosure(fitter, n).run()        experimental: search for an n-gram invariant of the abstract run lists
                                       (lengths cut at T) closed under the table; 'closed' would mean the table is
                                       total on all reachable frames, hence no halt; adds cases on demand
  normR(rs), normB(rs)                 the normal forms of `TM.normR` / `TM.normB`

Lean side: `frame.cfg` is `⟨runs L blank, runs R blank, q⟩`; the frame map is `rlNext cases`, sound by
`rlNext_sound`; `checkF` + `rl_reach` give bounded runs, `frames_halts_iff` the halting equivalence once an
invariant `Good` is proved closed (not generated here).
"""
import os
import sys

from . import symtm
from .machine import Machine
from .symtm import Blank, Config, Ctx, Rep, lin

STATES = "ABCDEF"
LB = {0: "false", 1: "true"}


def normR(rs):
    out = []
    for b, k in rs:
        if k == 0:
            continue
        if out and out[-1][0] == b:
            out[-1] = (b, out[-1][1] + k)
        else:
            out.append((b, k))
    return out


def normB(rs):
    rs = normR(rs)
    if rs and rs[-1][0] == 0:
        rs = rs[:-1]
    return rs


def _runs_of(cells):
    out = []
    for c in cells:
        if out and out[-1][0] == c:
            out[-1] = (c, out[-1][1] + 1)
        else:
            out.append((c, 1))
    return out


class _Sim:
    """The machine on a bytearray tape, with frames at head turns."""

    def __init__(self, M, width=1 << 22):
        self.m = Machine.parse(M)
        self.tape = bytearray(width)
        self.h = width // 2
        self.lo = self.hi = self.h
        self.st = 0
        self.n = 0
        self.prevd = 0

    def frame(self):
        t, h = self.tape, self.h
        L = normB(_runs_of(t[i] for i in range(h - 1, self.lo - 1, -1)))
        R = normB(_runs_of(t[i] for i in range(h, self.hi + 1)))
        return (self.st, tuple(L), tuple(R))

    def next_dir(self):
        tr = self.m.table[self.st][self.tape[self.h]]
        return None if tr is None else tr[1]

    def step(self):
        tr = self.m.table[self.st][self.tape[self.h]]
        if tr is None:
            return False
        w, d, s = tr
        self.tape[self.h] = w
        self.h += d
        self.st = s
        self.n += 1
        self.prevd = d
        self.lo = min(self.lo, self.h)
        self.hi = max(self.hi, self.h)
        return True


def frames(M, steps):
    """(step, frame) at every head turn of the run from blank tape, in the first `steps` steps."""
    s = _Sim(M)
    while s.n < steps:
        d = s.next_dir()
        if d is None:
            return
        if s.prevd and d != s.prevd:
            yield s.n, s.frame()
        s.step()


class Case:
    def __init__(self, q, lpat, rpat, lend, rend, q2, newl, newr, nsteps, start, end):
        self.q, self.lpat, self.rpat, self.lend, self.rend = q, lpat, rpat, lend, rend
        self.q2, self.newl, self.newr, self.nsteps = q2, newl, newr, nsteps
        self.start, self.end = start, end

    def bind(self, f):
        """The variables' values if the normal-form frame f matches, else None."""
        q, L, R = f
        if q != self.q:
            return None
        env = {}
        for pat, side, end in ((self.lpat, L, self.lend), (self.rpat, R, self.rend)):
            if len(side) < len(pat) or (end and len(side) != len(pat)):
                return None
            for (b, kind, k, v), (b2, k2) in zip(pat, side):
                if b != b2:
                    return None
                if kind == "eq" and k2 != k:
                    return None
                if kind == "ge":
                    if k2 < k:
                        return None
                    env[v] = k2 - k
        return env

    def apply(self, f):
        env = self.bind(f)
        if env is None:
            return None
        q, L, R = f
        nl = [(b, n.subs(env)) for b, n in self.newl] + list(L[len(self.lpat):])
        nr = [(b, n.subs(env)) for b, n in self.newr] + list(R[len(self.rpat):])
        return (self.q2, nl, nr)


def _pat_tok(b, kind, k, v):
    return f"{b}^{k}" if kind == "eq" else (f"{b}^{v}+{k}" if k else f"{b}^{v}")


def _side_runs(toks, left):
    """Run list (nearest the head first) of symtm tokens of one side; None if not expressible."""
    seq = list(reversed(toks)) if left else list(toks)
    out, tail = [], None
    for t in seq:
        if isinstance(t, int):
            out.append((t, lin(1)))
        elif isinstance(t, Rep):
            if len(set(t.word)) == 1:
                out.append((t.word[0], t.n * len(t.word)))
            elif t.n.is_const():
                for _ in range(t.n.k):
                    for c in (reversed(t.word) if left else t.word):
                        out.append((c, lin(1)))
            else:
                return None
        elif isinstance(t, (Ctx, Blank)):
            tail = t
        else:
            return None
    return out, tail


class Fitter:
    def __init__(self, M, T=4, max_moves=4000):
        self.M = M
        self.m = Machine.parse(M)
        self.T = T
        self.max_moves = max_moves
        self.cases = []
        self.failed = []

    def predict(self, f):
        for c in self.cases:
            g = c.apply(f)
            if g is not None:
                return (g[0], tuple(normB(g[1])), tuple(normB(g[2])))
        return None

    def _window(self, f):
        """Concrete run from frame f to its next turn: how many runs of each side the head visits."""
        q, L, R = f
        s = _Sim(self.M, width=1 << 16)
        c = s.h
        for i, (b, k) in enumerate(R):
            for _ in range(k):
                s.tape[c] = b
                c += 1
        c2 = s.h - 1
        for b, k in L:
            for _ in range(k):
                s.tape[c2] = b
                c2 -= 1
        s.lo, s.hi, s.st = c2 + 1, max(c - 1, s.h), q
        h0 = s.h
        vmin = vmax = 0
        first = True
        while True:
            d = s.next_dir()
            if d is None:
                return None
            if not first and d != s.prevd:
                break
            first = False
            s.step()
            vmin, vmax = min(vmin, s.h - h0), max(vmax, s.h - h0)
            if s.n > 100000:
                return None

        def need(side, cells):
            k, tot = 0, 0
            while tot < cells and k < len(side):
                tot += side[k][1]
                k += 1
            return k
        return need(L, -vmin), need(R, vmax + 1)

    def _make_case(self, f, exact=False):
        q, L, R = f
        w = self._window(f)
        if w is None:
            return None
        wl, wr = w
        names = iter(f"v{i}" for i in range(1000))
        for _ in range(6):
            lpat = [(b, "eq", k, None) if (exact or k < self.T) else (b, "ge", self.T, next(names)) for b, k in L[:wl]]
            rpat = [(b, "eq", k, None) if (exact or k < self.T) else (b, "ge", self.T, next(names)) for b, k in R[:wr]]
            lend, rend = wl == len(L), wr == len(R)
            left = ("0^inf" if lend else "L") + "".join(" " + _pat_tok(*p) for p in reversed(lpat))
            right = "".join(_pat_tok(*p) + " " for p in rpat) + ("0^inf" if rend else "R")
            start = f"{left} {STATES[q]}> {right}"
            trace = []
            last = {"d": None}

            def stop(c, trace=trace):
                if not trace:
                    return False
                kind = trace[-1][0]
                if kind == "cross":
                    x = trace[-1][3]
                    if x.s != len(x.w):
                        raise ValueError("crossing with turns inside")
                    d = 1 if x.d == "r" else -1
                else:
                    b = trace[-1][1].copy()
                    sym = symtm._unroll_front(b.right)
                    d = self.m.table[b.state][sym][1]
                c2 = c.copy()
                try:
                    sym = symtm._unroll_front(c2.right)
                except symtm.TouchContext:
                    raise
                tr = self.m.table[c.state][sym]
                if tr is None:
                    raise symtm.Halted("halt")
                return tr[1] != d
            try:
                fin = symtm.run(self.m, Config.parse(start), stop, max_moves=self.max_moves, trace=trace)
            except symtm.TouchContext as e:
                side = str(e)
                if side == "L" and not lend:
                    wl += 1
                    continue
                if side == "R" and not rend:
                    wr += 1
                    continue
                return None
            except symtm.NeedSplit:
                if exact:
                    return None
                return self._make_case(f, exact=True)
            except (symtm.Halted, ValueError, RuntimeError):
                return None
            sl = _side_runs(fin.left, True)
            sr = _side_runs(fin.right, False)
            if sl is None or sr is None:
                return None if exact else self._make_case(f, exact=True)
            (newl, tl), (newr, tr_) = sl, sr
            if (isinstance(tl, Ctx)) != (not lend) or (isinstance(tr_, Ctx)) != (not rend):
                return None
            return Case(q, lpat, rpat, lend, rend, fin.state, newl, newr, fin.steps, start, repr(fin))
        return None

    def fit(self, steps, log=None):
        n_frames = n_new = n_fail = 0
        prev = None
        for n, f in frames(self.M, steps):
            n_frames += 1
            if self.predict(f) is None:
                c = self._make_case(f)
                if c is None or c.apply(f) is None:
                    n_fail += 1
                    if len(self.failed) < 20:
                        self.failed.append((n, f))
                    continue
                self.cases.append(c)
                n_new += 1
                if log:
                    log(f"step {n}: case {len(self.cases) - 1} {c.start}  ->  {c.end}")
        return dict(frames=n_frames, cases=len(self.cases), new=n_new, failed=n_fail)

    def check(self, steps):
        bad = unmatched = total = 0
        pred = None
        for n, f in frames(self.M, steps):
            total += 1
            if pred is not None and pred != f:
                bad += 1
                if bad < 5:
                    print("MISMATCH at step", n, "predicted", pred, "got", f, file=sys.stderr)
            pred = self.predict(f)
            if pred is None:
                unmatched += 1
        return total, bad, unmatched

    # ------------------------------------------------------------------ Lean
    def lean(self, ns, machine_module="Machine", pieces_module="Pieces", prefix="pc"):
        ths = []
        for i, c in enumerate(self.cases):
            text, _ = symtm.prove(self.M, f"{prefix}{i}", c.start, c.end, max_seg=60)
            ths.append(text)
        pieces = symtm.rules_file(machine_module, ns, ths, f"One symbolic run per case of the frame map, generated by "
                                  f"`bbtools.listframe`; do not edit.")
        # exact cases with long literal runs unfold deep `rep` terms in `rfl`
        pieces = pieces.replace(f"namespace {ns}\n", f"set_option maxRecDepth 20000\n\nnamespace {ns}\n", 1)
        out = [f"import {pieces_module}", "import TM.ListFrame", "",
               "/-! The case table of the run-length frame map, generated by `bbtools.listframe`; do not edit. -/", "",
               f"namespace {ns}", "", "open TM", ""]
        names = []
        for i, c in enumerate(self.cases):
            def pat(p, side_end, rest):
                items = []
                for b, kind, k, v in p:
                    items.append(f"({LB[b]}, {k})" if kind == "eq" else (f"({LB[b]}, {v} + {k})" if k else f"({LB[b]}, {v})"))
                return " :: ".join(items + ["[]" if side_end else rest])
            def res(rs, side_end, rest):
                items = [f"({LB[b]}, {n.lean()})" for b, n in rs]
                return " :: ".join(items + ["[]" if side_end else rest])
            lp, rp = pat(c.lpat, c.lend, "l"), pat(c.rpat, c.rend, "r")
            lr, rr = res(c.newl, c.lend, "l"), res(c.newr, c.rend, "r")
            lvs = [p[3] for p in c.lpat if p[1] == "ge"]
            rvs = [p[3] for p in c.rpat if p[1] == "ge"]
            vs = lvs + rvs
            binders = lvs + ([] if c.lend else ["l"]) + rvs + ([] if c.rend else ["r"])
            th = symtm.Config.parse(c.start)
            pvars = sorted(set(vs))
            ctx_args = []
            for x in th.contexts():
                ctx_args.append("(runs l blank)" if x == "L" else "(runs r blank)")
            name = f"ca{i}"
            names.append(name)
            out.append(f"def {name} : RLCase trans where")
            out.append("  apply f := match f with")
            out.append(f"    | ⟨.{STATES[c.q]}, {lp}, {rp}⟩ => some ⟨.{STATES[c.q2]}, {lr}, {rr}⟩")
            out.append("    | _ => none")
            out.append("  sound f f' h := by")
            out.append("    split at h")
            out.append(f"    · rename_i {' '.join(binders)}" if binders else "    · skip")
            out.append("      simp only [Option.some.injEq] at h; subst h")
            out.append("      simp only [RLFrame.cfg]")
            out.append(f"      exact ⟨_, by omega, steps_eq_of' ({prefix}{i} {' '.join(pvars + ctx_args)}) "
                       "(cfg_congr' (by rl_eq) (by rl_eq)) (cfg_congr' (by rl_eq) (by rl_eq))⟩")
            out.append("    · simp at h")
            out.append("")
        out.append("/-- The case table, in the order `bbtools.listframe` matches it. -/")
        out.append("def cases : List (RLCase trans) := [" + ", ".join(names) + "]")
        out.append("")
        out.append("/-- The run-length frame map. -/")
        out.append("abbrev next (f : RLFrame St) : Option (RLFrame St) := rlNext cases f")
        out.append("")
        out.append(f"end {ns}")
        return pieces, "\n".join(out) + "\n"


def first_frame(M):
    """(step, frame) of the first head turn of the run from blank tape."""
    for n, f in frames(M, 10 ** 6):
        return n, f


def lean_start(M, ns, K, cases_module="Cases"):
    """Lean file: the first frame of the run from blank tape, reached by `blank_frame` (kernel `decide`), and the
    first K frames of the frame map by `native_decide` (`checkF`)."""
    n0, f0 = first_frame(M)
    return f"""import {cases_module}

/-! The run-length frame map from blank tape, generated by `bbtools.listframe`; do not edit.

`init_f0`: the run from blank tape reaches the frame `f0` (its first head turn) after {n0} steps.  `frames_{K}`:
the frame map is defined for the first {K} frames (`native_decide`), so by `rl_reach` the machine runs on through
them.  `no_halt_of_total`: if the frame map is defined forever along this orbit, the machine never halts; that is
the open part. -/

namespace {ns}

open TM

def f0 : RLFrame St := {lean_frame(f0)}

theorem init_f0 : steps {n0} init = some f0.cfg := blank_frame trans (by decide)

theorem frames_{K} : ∀ j, j ≤ {K} → ∃ f, iterF next j f0 = some f :=
  checkF_sound next {K} f0 (by native_decide)

theorem no_halt_of_total (h : ∀ k, ∃ f, iterF next k f0 = some f) : ¬ HaltsFromBlank :=
  rl_no_halt trans cases init_f0 h

end {ns}
"""


def lean_frame(f):
    """A frame as a Lean term `⟨.q, l, r⟩`."""
    q, L, R = f
    side = lambda rs: "[" + ", ".join(f"({LB[b]}, {k})" for b, k in rs) + "]"
    return f"(⟨.{STATES[q]}, {side(L)}, {side(R)}⟩ : RLFrame St)"


# ---------------------------------------------------------------------- closure (experimental)
class NGramClosure:
    """Search for a run-length n-gram invariant: an over-approximation of the reachable frames by their abstract
    form (each run length cut to a class 1, ..., T-1 or >= T; each side a word of such runs, `E` for the blank end)
    in which each side is described by its set of n-grams.  `run()` returns ('closed', stats) when the set of
    abstract frames and n-grams is closed under the case table and every abstract frame is covered by a case
    whose pattern matches all its concrete frames (so the case table is defined on every frame the machine reaches,
    and it never halts), or ('open', reason) when an abstract frame is not covered."""

    def __init__(self, fitter, n=3, steps=200000, max_iter=10000):
        self.F, self.n, self.T = fitter, n, fitter.T
        self.steps, self.max_iter = steps, max_iter
        self.added = 0

    def cls(self, k):
        return min(k, self.T)

    def abs_side(self, rs):
        return tuple((b, self.cls(k)) for b, k in rs) + ("E",)

    def grams(self, side):
        n, out = self.n, set()
        for i in range(len(side)):
            g = side[i:i + n]
            out.add(g)
        return out

    def values(self, c):
        """Concrete lengths of class c, enough to cover every class of affine images."""
        return [c] if c < self.T else list(range(self.T, 3 * self.T + 2))

    def run(self):
        GL, GR, configs = set(), set(), set()
        for _, f in frames(self.F.M, self.steps):
            q, L, R = f
            aL, aR = self.abs_side(L), self.abs_side(R)
            GL |= self.grams(aL)
            GR |= self.grams(aR)
            configs.add((q, aL[:self.n - 1], aR[:self.n - 1]))
        todo = list(configs)
        seen = set(configs)
        it = 0
        while todo:
            it += 1
            if it > self.max_iter * 100:
                return ("open", "too many abstract frames")
            q, tl, tr = todo.pop()
            res = self._step(q, tl, tr, GL, GR)
            if isinstance(res, str):
                return ("open", f"{res} at {(q, tl, tr)}; cases added {self.added}; abstract frames {len(seen)}")
            newg_l, newg_r, succ = res
            grew = (newg_l - GL) or (newg_r - GR)
            GL |= newg_l
            GR |= newg_r
            if grew:
                todo = list(seen)       # the languages grew: everything again
            for c in succ:
                if c not in seen:
                    seen.add(c)
                    todo.append(c)
        return ("closed", dict(frames=len(seen), grams_left=len(GL), grams_right=len(GR), cases_added=self.added))

    def _extend(self, top, G, k):
        """All continuations of the side `top` to at least k tokens (or to E), using the n-grams G."""
        out = []
        stack = [top]
        n = self.n
        while stack:
            t = stack.pop()
            if len(t) >= k or t[-1] == "E":
                out.append(t)
                continue
            ctx = t[-(n - 1):]
            for g in G:
                if len(g) == n and g[:n - 1] == ctx:
                    stack.append(t + (g[-1],))
                elif len(g) < n and g[:-1] == ctx and g[-1] == "E":
                    stack.append(t + ("E",))
        return out

    def _concretes(self, side, k):
        """Concrete run lists for the first k abstract tokens of side (values per class)."""
        import itertools
        toks = [t for t in side[:k] if t != "E"]
        for vals in itertools.product(*[self.values(c) for _, c in toks]):
            yield [(b, v) for (b, _), v in zip(toks, vals)]

    def _step(self, q, tl, tr, GL, GR):
        maxw = 6
        newgl, newgr, succ = set(), set(), set()
        for L in self._extend(tl, GL, maxw):
            for R in self._extend(tr, GR, maxw):
                # every concrete frame of this abstract window must be matched by some case
                lt = [t for t in L if t != "E"]
                rt = [t for t in R if t != "E"]
                lclosed, rclosed = L[-1] == "E", R[-1] == "E"
                for cl in self._concretes(L, len(L)):
                    for cr in self._concretes(R, len(R)):
                        f = (q, tuple(cl), tuple(cr))
                        hit = None
                        for c in self.F.cases:
                            env = c.bind(f)
                            if env is None:
                                continue
                            if (not c.lend and len(c.lpat) >= len(lt) and not lclosed) or \
                               (not c.rend and len(c.rpat) >= len(rt) and not rclosed):
                                continue
                            if (c.lend and not lclosed) or (c.rend and not rclosed):
                                continue
                            hit = c
                            break
                        if hit is None:
                            if (not lclosed and len(lt) < maxw) or (not rclosed and len(rt) < maxw):
                                continue
                            c = self.F._make_case(f)
                            if c is None or c.apply(f) is None:
                                return f"no case for {f}"
                            self.F.cases.append(c)
                            self.added += 1
                            hit = c
                        q2, nl, nr = hit.apply(f)
                        # the abstract tails beyond the window: from the abstract side
                        kl, kr = len(hit.lpat), len(hit.rpat)
                        tailL = L[kl:]
                        tailR = R[kr:]
                        # concrete new window + abstract tail, normalized at the seam
                        winL = nl[:len(nl) - (len(cl) - kl)]
                        winR = nr[:len(nr) - (len(cr) - kr)]
                        aL = self._seam(winL, tailL)
                        aR = self._seam(winR, tailR)
                        for a in aL:
                            newgl |= self.grams(a)
                            for b in aR:
                                succ.add((q2, a[:self.n - 1], b[:self.n - 1]))
                        for b in aR:
                            newgr |= self.grams(b)
        return newgl, newgr, succ

    def _seam(self, win, tail):
        """Abstract sides from a concrete window `win` followed by the abstract tail (normal form at the seam)."""
        rs = normR(win)
        outs = []
        if tail and tail[0] != "E" and rs and rs[-1][0] == tail[0][0]:
            b, k = rs[-1]
            c = tail[0][1]
            for v in self.values(c):
                outs.append(tuple((bb, self.cls(kk)) for bb, kk in rs[:-1]) + ((b, self.cls(k + v)),) + tuple(tail[1:]))
        else:
            if tail == ("E",) and rs and rs[-1][0] == 0:
                rs = rs[:-1]
            if not rs and tail and tail[0] != "E":
                outs.append(tuple(tail))
            else:
                outs.append(tuple((bb, self.cls(kk)) for bb, kk in rs) + tuple(tail))
        return list(set(outs))
