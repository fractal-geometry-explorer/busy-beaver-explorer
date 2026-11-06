"""Symbolic runs over lists of blocks of any length, and their Lean proofs: `symtm.py` with one more kind of token.

A *sequence* `[w]^ts` is a list of blocks side by side, each the token word `w` with its own values of the
parameters of `w` (variables that appear only in `w`), the list `ts` itself a variable: any length, any values.  A
symbolic run treats it as a context it may not look into, except for one move, the *sequence rule*: when the head is
about to step onto it, one block is run on its own between two contexts (with up to three literal cells `u` next to
the head carried along); if the head comes out on the far side of the block in the state it went in with, the block
changed to `w'`, then every block of the list is crossed the same way, and the sequence is on the other side of the
head as `[w']^ts` (in reverse order).  This is `symtm`'s shift rule for a word with parameters, and it is proved in
Lean the same way: the one-block run by `symtm.prove`, the list by induction (`seqL`, `seqR` and their reversed
forms in the machine's `Seq.lean`, with `sq`/`sqr` writing the list on the tape).

`run(m, cfg, stop)` runs with sequence rules and returns the end configuration and the parts: plain symbolic
stretches between sequence rules (proved by `symtm.prove`, each sequence written as a context there) and the rules
(`Cross`).  `prove(m, name, start, end_stop)` writes the Lean theorem `∃ n, steps n start = some end`.

Syntax: in a configuration string, `[ tokens ]^ts` is a sequence; the variables of its tokens are its parameters.
"""
from dataclasses import dataclass

from . import symtm
from .symtm import Blank, Config, Ctx, Lin, Rep, TouchContext, lin

STATES = "ABCDEF"
B = {0: "false", 1: "true"}
MAX_CARRY = 3


@dataclass(frozen=True)
class Seq:
    """A list `name` of blocks (tokens left to right on the tape), parameters `params`; `rev`: the list is written
    last element first, reading from the head outwards (`sqr`), else first element first (`sq`).  `alts`: the
    kinds of block, each a token tuple; with one kind an element of the list is its parameters, with several it is
    a pair (kind, parameter) and every kind has the one parameter `params[0]`."""
    alts: tuple
    params: tuple
    name: str
    rev: bool = False

    @property
    def elem(self):
        return self.alts[0]

    @property
    def typed(self):
        return len(self.alts) > 1

    def __repr__(self):
        return "[" + " | ".join(" ".join(map(str, a)) for a in self.alts) + f"]^{self.name}{'~' if self.rev else ''}"


def parse(s):
    """A configuration string with sequences `[ ... ]^name`."""
    parts = s.split()
    out, i = [], 0
    seqs = {}
    while i < len(parts):
        p = parts[i]
        if p == "[":
            j = i + 1
            while not parts[j].startswith("]^"):
                j += 1
            name = parts[j][2:]
            alts, cur = [], []
            for p in parts[i + 1:j] + ["|"]:
                if p == "|":
                    alts.append(tuple(symtm.tokens(" ".join(cur))))
                    cur = []
                else:
                    cur.append(p)
            params = []
            for elem in alts:
                for t in elem:
                    if isinstance(t, Rep):
                        for v in sorted(t.n.vars()):
                            if v not in params:
                                params.append(v)
            if len(alts) > 1 and len(params) != 1:
                raise ValueError("a sequence of several kinds of block has one parameter")
            key = f"__seq{len(seqs)}"
            seqs[key] = Seq(tuple(alts), tuple(params), name)
            out.append(key)
            i = j + 1
        else:
            out.append(p)
            i += 1
    k = next(n for n, p in enumerate(out) if p.endswith(">") and len(p) == 2)

    def toks(ps):
        res, buf = [], []
        for p in ps:
            if p in seqs:
                if buf:
                    res += symtm.tokens(" ".join(buf))
                    buf = []
                res.append(seqs[p])
            else:
                buf.append(p)
        if buf:
            res += symtm.tokens(" ".join(buf))
        return res

    return Config(toks(out[:k]), STATES.index(out[k][0]), toks(out[k + 1:]))


def seq_vars(cfg):
    """The list variables and the plain variables (outside sequences) of a configuration."""
    lists, vs = [], set()
    for t in cfg.left + cfg.right:
        if isinstance(t, Seq):
            lists.append(t.name)
        elif isinstance(t, Rep):
            vs |= t.n.vars()
    return lists, vs


# ---------------------------------------------------------------- the sequence rule
@dataclass
class Cross:
    """A sequence crossed: direction 'l' or 'r', the carried cells u (left to right), the sequence before and after,
    the state, and the one-block run (start and end configurations between contexts L and R)."""
    d: str
    u: tuple
    seq: Seq
    seq2: Seq
    state: int
    one: tuple
    before: Config = None
    after: Config = None


def _fresh(seq):
    return list(seq.elem)


def _one_block(m, q, seq, d, u, max_moves):
    """Each kind of block of `seq` run on its own, head in state q, carrying u: [(start, end)] or None."""
    out = []
    for elem in seq.alts:
        r = _one_kind(m, q, elem, seq.params, d, u, max_moves)
        if r is None:
            return None
        out.append(r)
    return out


def _one_kind(m, q, elem, params, d, u, max_moves):
    if d == "l":
        start = Config([Ctx("L")] + list(elem), q, list(u) + [Ctx("R")])

        def stop(c):
            return (c.state == q and c.left == [Ctx("L")] and not c.steps.is_zero()
                    and len(c.right) > len(u) and tuple(c.right[:len(u)]) == tuple(u) and c.right[-1] == Ctx("R"))
    else:
        start = Config([Ctx("L")] + list(u), q, list(elem) + [Ctx("R")])

        def stop(c):
            return (c.state == q and c.right == [Ctx("R")] and not c.steps.is_zero()
                    and len(c.left) > len(u) and tuple(c.left[len(c.left) - len(u):]) == tuple(u)
                    and c.left[0] == Ctx("L"))
    try:
        fin = symtm.run(m, start.copy(), stop, max_moves=max_moves)
    except (TouchContext, symtm.NeedSplit, symtm.Halted, RuntimeError):
        return None
    if fin.vars() - set(params):
        return None
    if any(isinstance(t, (Ctx, Blank)) for t in (fin.right[len(u):-1] if d == "l" else fin.left[1:len(fin.left) - len(u)])):
        return None
    return start, fin


def _next_touches_seq(m, cfg):
    """'l' or 'r' if the next single step of `cfg` would read into a sequence (to the left or under the head)."""
    if not cfg.right:
        return None
    h = cfg.right[0]
    if isinstance(h, Seq):
        return "r"
    if isinstance(h, Rep):
        if h.n.is_zero() or not h.n.surely_ge(1):
            return None
        h = h.word[0]
    if not isinstance(h, int):
        return None
    tr = m.table[cfg.state][h]
    if tr is None or tr[1] == 1:
        return None
    if cfg.left and isinstance(cfg.left[-1], Seq):
        return "l"
    return None


def try_seq(m, cfg, max_moves=2000):
    """Apply the sequence rule if the next step would read into a sequence; returns the Cross (cfg updated) or
    None.  Raises TouchContext if the head would read into a sequence it cannot cross."""
    probe = cfg.copy()
    if symtm.try_cross(m, probe) is not None:
        return None
    d = _next_touches_seq(m, cfg)
    if d is None:
        return None
    if d == "l":
        seq = cfg.left[-1]
        for lu in range(1, MAX_CARRY + 1):
            u = cfg.right[:lu]
            if len(cfg.right) <= lu or not all(isinstance(x, int) for x in u):
                break
            r = _one_block(m, cfg.state, seq, "l", tuple(u), max_moves)
            if r:
                seq2 = Seq(tuple(tuple(fin.right[lu:-1]) for _, fin in r), seq.params, seq.name, not seq.rev)
                x = Cross("l", tuple(u), seq, seq2, cfg.state, r, before=cfg.copy())
                cfg.left = cfg.left[:-1]
                cfg.right = list(u) + [seq2] + cfg.right[lu:]
                x.after = cfg.copy()
                return x
    else:
        seq = cfg.right[0]
        for lu in range(0, MAX_CARRY + 1):
            u = cfg.left[len(cfg.left) - lu:] if lu else []
            if len(cfg.left) <= lu or not all(isinstance(x, int) for x in u):
                break
            r = _one_block(m, cfg.state, seq, "r", tuple(u), max_moves)
            if r:
                seq2 = Seq(tuple(tuple(fin.left[1:len(fin.left) - lu]) for _, fin in r), seq.params, seq.name,
                           not seq.rev)
                x = Cross("r", tuple(u), seq, seq2, cfg.state, r, before=cfg.copy())
                cfg.left = cfg.left[:len(cfg.left) - lu] + [seq2] + list(u)
                cfg.right = cfg.right[1:]
                x.after = cfg.copy()
                return x
    raise TouchContext(f"cannot cross {cfg.left[-1] if d == 'l' else cfg.right[0]}")


def run(m, cfg, stop, max_moves=2000, parts=None):
    """Run with shift rules and sequence rules until stop(cfg).  `parts`: a list to which the plain stretches
    (start, end) and the Cross moves are appended in order."""
    cur = cfg.copy()
    moves = 0
    while True:
        start = cur.copy()
        hit = []

        def st(c):
            if stop(c):
                return True
            if _next_touches_seq(m, c) is not None:
                probe = c.copy()
                if symtm.try_cross(m, probe) is None:
                    hit.append(True)
                    return True
            return False

        fin = symtm.run(m, cur, st, max_moves=max_moves - moves)
        if parts is not None and (fin.steps - start.steps) != lin(0):
            parts.append((start, fin.copy()))
        if not hit:
            return fin
        fin.steps = fin.steps
        x = try_seq(m, fin, max_moves)
        if parts is not None:
            parts.append(x)
        cur = fin
        moves += 1
        if moves >= max_moves:
            raise RuntimeError("too many sequence moves")


# ---------------------------------------------------------------- Lean terms
def _word(w):
    return "[" + ", ".join(B[x] for x in w) + "]"


def ptype(params, typed=False):
    if typed:
        return "Nat × Nat"
    return " × ".join(["Nat"] * len(params)) if params else "Unit"


def pbind(params):
    """The binder of a block's parameters: `t` or `(a, b)`."""
    if len(params) == 1:
        return params[0]
    return "(" + ", ".join(params) + ")" if params else "()"


def _kinds(n, last):
    """The match patterns of the kinds 0..n-1 of a typed sequence: `0`, `1`, ..., `_` (in a definition) or
    `_ + (n-1)` (in a proof by cases)."""
    return [str(k) for k in range(n - 1)] + ["_" if not last else f"_ + {n - 1}" if n > 1 else "_"]


def _fun(seq, side):
    def body(elem):
        return left_term([Ctx("X")] + list(elem)) if side == "l" else right_term(list(elem) + [Ctx("X")])
    if seq.typed:
        a = seq.params[0]
        cases = " ".join(f"| ({k}, {a}) => {body(e)}" for k, e in zip(_kinds(len(seq.alts), False), seq.alts))
        return f"(fun (p : Nat × Nat) (X : Tape) => match p with {cases})"
    body = body(seq.elem)
    if len(seq.params) == 1:
        return f"(fun ({seq.params[0]} : Nat) (X : Tape) => {body})"
    return f"(fun (p : {ptype(seq.params)}) (X : Tape) => match p with | {pbind(seq.params)} => {body})"


def _seq_term(seq, side, acc):
    return f"{'sqr' if seq.rev else 'sq'} {_fun(seq, side)} {seq.name} ({acc})"


def right_term(tks):
    acc = None
    for t in reversed(tks):
        if isinstance(t, Ctx):
            assert acc is None
            acc = t.name
        elif isinstance(t, Blank):
            assert acc is None
            acc = "blank"
        elif isinstance(t, int):
            acc = f"cons {B[t]} ({acc})"
        elif isinstance(t, Rep):
            if t.n.is_zero():
                continue
            acc = f"rep ({t.n.lean()}) {_word(t.word)} ({acc})"
        elif isinstance(t, Seq):
            acc = _seq_term(t, "r", acc)
    return acc


def left_term(tks):
    acc = None
    for t in tks:
        if isinstance(t, Ctx):
            assert acc is None
            acc = t.name
        elif isinstance(t, Blank):
            assert acc is None
            acc = "blank"
        elif isinstance(t, int):
            acc = f"cons {B[t]} ({acc})"
        elif isinstance(t, Rep):
            if t.n.is_zero():
                continue
            acc = f"rep ({t.n.lean()}) {_word(tuple(reversed(t.word)))} ({acc})"
        elif isinstance(t, Seq):
            acc = _seq_term(t, "l", acc)
    return acc


def cfg_term(c):
    return f"⟨{left_term(c.left)}, {right_term(c.right)}, .{STATES[c.state]}⟩"


def _collapse(c):
    """The configuration with everything from the nearest sequence outwards, on each side, a context K0/K1; and
    {context: tokens it stands for}."""
    left, right, sub = list(c.left), list(c.right), {}
    i = max((k for k, t in enumerate(left) if isinstance(t, Seq)), default=None)
    if i is not None:
        sub["K0"] = ("l", left[:i + 1])
        left = [Ctx("K0")] + left[i + 1:]
    j = min((k for k, t in enumerate(right) if isinstance(t, Seq)), default=None)
    if j is not None:
        sub["K1"] = ("r", right[j:])
        right = right[:j] + [Ctx("K1")]
    return Config(left, c.state, right, c.steps), sub


def prove(m, name, start, stop, doc=None, max_moves=2000):
    """Lean text of `name`: `∃ n, steps n start = some end`, end the configuration where `stop` holds; the
    statement is for every value of the variables, every list and every tape in the contexts.  Returns
    (text, end configuration, parts)."""
    parts = []
    fin = run(m, start.copy(), stop, max_moves=max_moves, parts=parts)
    out, lines, hs = [], [], []
    for k, p in enumerate(parts):
        if isinstance(p, Cross):
            one = f"{name}_b{k}"
            ones = []
            for kk, (a, b) in enumerate(p.one):
                nm = one if not p.seq.typed else f"{one}_{kk}"
                raw, _ = symtm.prove(m, nm, a, b, doc=f"One block of {name}, move {k}" +
                                     (f", kind {kk}." if p.seq.typed else "."))
                out.append(raw)
                ones.append(nm)
            q = STATES[p.state]
            U = f"(fun Y => {right_term(list(p.u) + [Ctx('Y')])})" if p.d == "l" else \
                f"(fun Y => {left_term([Ctx('Y')] + list(p.u))})"
            f = _fun(p.seq, p.d)
            g = _fun(p.seq2, "r" if p.d == "l" else "l")
            args = " ".join(p.seq.params)
            if p.seq.typed:
                a_ = p.seq.params[0]
                cases = " ".join(f"| ({kd}, {a_}) => ⟨_, {nm} {a_} L R⟩"
                                 for kd, nm in zip(_kinds(len(ones), True), ones))
                hyp = f"(fun p L R => match p with {cases})"
            elif len(p.seq.params) == 1:
                hyp = f"(fun {p.seq.params[0]} L R => ⟨_, {one} {args} L R⟩)"
            else:
                hyp = f"(fun p L R => match p with | {pbind(p.seq.params)} => ⟨_, {one} {args} L R⟩)"
            lemma = {("l", False): "seqL", ("l", True): "seqL'", ("r", False): "seqR", ("r", True): "seqR'"}[
                (p.d, p.seq.rev)]
            bf = p.before
            if p.d == "l":
                Lt, Rt = left_term(bf.left[:-1]), right_term(bf.right[len(p.u):])
            else:
                Lt, Rt = left_term(bf.left[:len(bf.left) - len(p.u)]), right_term(bf.right[1:])
            lines.append(f"  have h{k} : ∃ n, steps n {cfg_term(p.before)} = some {cfg_term(p.after)} :=")
            lines.append(f"    {lemma} {f} {g} {U} .{q} {hyp} {p.seq.name} ({Lt}) ({Rt})")
        else:
            a, b = p
            a0 = Config(a.left, a.state, a.right, 0)
            b0 = Config(b.left, b.state, b.right, b.steps - a.steps)
            ca, sub = _collapse(a0)
            cb, sub2 = _collapse(b0)
            assert {k_: v for k_, v in sub.items()} == sub2, (sub, sub2)
            sname = f"{name}_s{k}"
            raw, _ = symtm.prove(m, sname, ca, cb, doc=f"{name}, stretch {k}.")
            out.append(raw)
            vs = sorted(ca.vars() | cb.vars())
            ctxs = []
            for x in ca.contexts() + cb.contexts():
                if x not in ctxs:
                    ctxs.append(x)
            cargs = []
            for x in ctxs:
                if x in sub:
                    side, toks = sub[x]
                    cargs.append(f"({left_term(toks) if side == 'l' else right_term(toks)})")
                else:
                    cargs.append(x)
            lines.append(f"  have h{k} : ∃ n, steps n {cfg_term(a)} = some {cfg_term(b)} :=")
            lines.append(f"    ⟨_, {sname} {' '.join(vs + cargs)}⟩")
        hs.append(k)
    lists, vs = seq_vars(start)
    _, vs2 = seq_vars(fin)
    vs = sorted(vs | vs2)
    ctxs = []
    for x in start.contexts() + fin.contexts():
        if x not in ctxs:
            ctxs.append(x)
    binders = (f" ({' '.join(vs)} : Nat)" if vs else "")
    seqs = {}
    for t in start.left + start.right:
        if isinstance(t, Seq):
            seqs[t.name] = t
    for n_, s_ in seqs.items():
        binders += f" ({n_} : List ({ptype(s_.params, s_.typed)}))"
    binders += f" ({' '.join(ctxs)} : Tape)" if ctxs else ""
    head = [f"/-- {doc} -/" if doc else None, f"theorem {name}{binders} :",
            f"    ∃ n, steps n {cfg_term(start)} = some {cfg_term(fin)} := by"]
    body = [x for x in head if x] + lines
    if not hs:
        body.append("  exact ⟨0, rfl⟩")
    else:
        body.append("  " + " ".join(f"obtain ⟨n{k}, h{k}⟩ := h{k};" for k in hs)[:-1])
        chain = f"h{hs[-1]}"
        for k in reversed(hs[:-1]):
            chain = f"steps_seq trans h{k} ({chain})"
        body.append(f"  exact ⟨_, {chain}⟩")
    out.append("\n".join(body) + "\n")
    return "\n".join(out), fin, parts
