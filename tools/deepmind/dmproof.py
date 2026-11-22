"""Prove a DeepMind halts-iff map in this repository's Lean: write lean/DMRules.lean and lean/DMMap.lean for a machine
whose cryptids file describes each state of its map `next` as a tape template (`def cfg_X ... := Cfg.headRight ...`).

The templates are read from DeepMind's file (google-deepmind/cryptids, commit 3647718; fetched, or given as a path),
`State` and `next` from holdouts/<M>/lean/DeepMindMap.lean (their verbatim copy).  For every clause of `next` the
symbolic simulator (tools/py/bbtools/symtm.py) runs from the template of the left side to the template of the right
side (or to the halting configuration) and writes the Lean rule; DMMap.lean then proves `deepmind_halts_iff` with the
statement of the cited axiom, from `TM.halts_iff_orbit` (tools/lean/TM/MapOrbit.lean).  Lean, not this script, is
the judge: a wrong run fails to check.

usage: python3 tools/deepmind/dmproof.py MACHINE [DM_FILE] [--install]
   writes holdouts/MACHINE/lean/{DMRules,DMMap}.lean and holdouts/MACHINE/py/dmspec.json (the templates read);
   --install also puts them in lean/check.sh in place of lean/DeepMindMap.lean, which it removes
"""
import json
import os
import re
import sys
import urllib.request

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, "..", ".."))
sys.path.insert(0, os.path.join(ROOT, "tools", "py"))
from bbtools.machine import Machine  # noqa: E402
from bbtools import symtm  # noqa: E402
from bbtools.symtm import Blank, Config, Halted, Lin, Rep, ProofError, prove, run, cfg_term  # noqa: E402

symtm_run, symtm_same = symtm.run, symtm.same_config
symtm.MAX_CARRY = 6       # DeepMind's sweeps carry words of up to four cells (`sweep_B_R_01_w1000`)
BASE = "https://raw.githubusercontent.com/google-deepmind/cryptids/3647718/BusyBeaver/BB6/"
STATES = "ABCDEF"


# ---------------------------------------------------------------- a small reader of Lean terms
def lex(s):
    return re.findall(r"[A-Za-z_][A-Za-z_0-9.']*|\d+|[()\[\],:^+*]|ℕ", s)


class P:
    def __init__(self, toks):
        self.t, self.i = toks, 0

    def peek(self):
        return self.t[self.i] if self.i < len(self.t) else None

    def eat(self, x=None):
        tok = self.t[self.i]
        if x is not None and tok != x:
            raise ValueError(f"expected {x}, got {tok} at {self.t[self.i:self.i + 8]}")
        self.i += 1
        return tok

    def app(self):
        """An application f a b ... (stops at ) ] , : ^ + * or the end)."""
        items = [self.atom()]
        while self.peek() not in (None, ")", "]", ",", ":", "^", "+", "*"):
            items.append(self.atom())
        return items[0] if len(items) == 1 else ("app", items)

    def expr(self):
        """Arithmetic over applications: a + b * c, w ^ n."""
        terms = [self.prod()]
        while self.peek() == "+":
            self.eat()
            terms.append(self.prod())
        return terms[0] if len(terms) == 1 else ("+", terms)

    def prod(self):
        fs = [self.powr()]
        while self.peek() == "*":
            self.eat()
            fs.append(self.powr())
        return fs[0] if len(fs) == 1 else ("*", fs)

    def powr(self):
        b = self.app()
        if self.peek() == "^":
            self.eat()
            return ("^", b, self.app())
        return b

    def atom(self):
        tok = self.peek()
        if tok == "(":
            self.eat()
            e = self.expr()
            if self.peek() == ":":          # type ascription (w : List (Fin 2))
                self.eat()
                depth = 0
                while not (depth == 0 and self.peek() == ")"):
                    t = self.eat()
                    depth += (t == "(") - (t == ")")
            self.eat(")")
            return e
        if tok == "[":
            self.eat()
            xs = []
            while self.peek() != "]":
                xs.append(int(self.eat()))
                if self.peek() == ",":
                    self.eat()
            self.eat("]")
            return ("list", xs)
        self.eat()
        return int(tok) if tok.isdigit() else tok


def lin_of(e, env):
    """A count (number, variable, sums and products by constants) as a Lin, variables replaced by `env`."""
    if isinstance(e, int):
        return Lin(e)
    if isinstance(e, str):
        return env[e] if e in env else Lin(e)
    if e[0] == "+":
        out = Lin(0)
        for x in e[1]:
            out = out + lin_of(x, env)
        return out
    if e[0] == "*":
        out = Lin(1)
        for x in e[1]:
            out = out * lin_of(x, env)
        return out
    raise ValueError(f"not a count: {e}")


def tape_of(e, env, defs):
    """A ListBlank term as a token list, nearest cell first; ends with Blank()."""
    if e == "default":
        return [Blank()]
    if isinstance(e, str) and e in env:
        return env[e]
    if e[0] == "app":
        f, args = e[1][0], e[1][1:]
        if f == "ListBlank.append":
            w, rest = args
            if w[0] == "list":
                return list(w[1]) + tape_of(rest, env, defs)
            if w[0] == "^":
                return [Rep(tuple(w[1][1]), lin_of(w[2], env))] + tape_of(rest, env, defs)
        raise ValueError(f"tape term {e}")
    raise ValueError(f"tape term {e}")


def cfg_of(e, env, defs):
    """(state index, left tokens nearest first, right tokens) of a Cfg term."""
    f, args = e[1][0], e[1][1:]
    if f == "Cfg.headRight":
        q, l, r = args
        return STATES.index(q), tape_of(l, env, defs), tape_of(r, env, defs)
    if f in defs:
        ps, body = defs[f]
        sub = {}
        for p, a in zip(ps, args):
            if p[1] == "tape":
                sub[p[0]] = tape_of(a, env, defs)
            else:
                sub[p[0]] = lin_of(a, env)
        return cfg_of(body, sub, defs)
    raise ValueError(f"cfg term {f}")


def read_defs(src):
    """`def cfg_X (a b : ℕ) (r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) := term` blocks."""
    defs = {}
    for m in re.finditer(r"^(?:private )?def (cfg_\w+)((?:\s*\([^()]*(?:\([^()]*\)[^()]*)*\))*)\s*:\s*Cfg \(Fin 2\) \(Fin 6\) :=\n(.*?)(?=\n\n|\n/-|\n@|\nprivate|\ntheorem|\ndef)",
                         src, re.M | re.S):
        name, binders, body = m.group(1), m.group(2), m.group(3)
        ps = []
        for b in re.findall(r"\(([^():]*):\s*([^()]*(?:\([^()]*\))*[^()]*)\)", binders):
            kind = "tape" if "ListBlank" in b[1] else "nat"
            ps += [(v, kind) for v in b[0].split()]
        defs[name] = (ps, P(lex(body)).expr())
    return defs


def read_encode(src, defs):
    """Each clause of `encode` as (its variables, a template name, the template's arguments).  A clause written
    `| .X a b => cfg_X a b` names a template; a clause whose configuration is written out in place becomes the
    template `enc_X` (added to `defs`)."""
    m = re.search(r"^def encode : State → Cfg \(Fin 2\) \(Fin 6\)\n((?:  \|.*\n|    .*\n)+)", src, re.M)
    out = {}
    for cl in re.split(r"\n(?=  \|)", m.group(1).rstrip("\n")):
        mm = re.match(r"\s*\| \.(\w+)((?: \w+)*) =>\s*(.*)$", cl, re.S)
        name, ps, body = mm.group(1), mm.group(2).split(), mm.group(3).strip()
        mc = re.fullmatch(r"(cfg_\w+)((?: \w+)*)", body)
        if mc:
            out[name] = (ps, mc.group(1), mc.group(2).split())
        else:
            body = re.sub(r"\bSixState\.", "", body)
            defs[f"enc_{name}"] = ([(v, "nat") for v in ps], P(lex(body)).expr())
            out[name] = (ps, f"enc_{name}", ps)
    return out


# ---------------------------------------------------------------- the map, from the repository's copy
def split_args(s):
    out, depth, cur = [], 0, ""
    for ch in s.strip() + " ":
        if ch == " " and depth == 0:
            if cur:
                out.append(cur)
            cur = ""
            continue
        depth += (ch == "(") - (ch == ")")
        cur += ch
    return out


def read_map(path):
    if not os.path.exists(path):          # after `--install`: the copy lives in DMMap.lean
        path = os.path.join(os.path.dirname(path), "DMMap.lean")
    src = open(path).read()
    cons = {}
    for m in re.finditer(r"^  \| (\w+) \(([^:]*) : Nat\)", src, re.M):
        cons[m.group(1)] = m.group(2).split()
    for m in re.finditer(r"^  \| (\w+)\s*$", src, re.M):
        cons.setdefault(m.group(1), [])
    start = re.search(r"^def start : State := \.(.*)$", src, re.M).group(1)
    body = re.search(r"^def next : State → Option State\n((?:  \|.*\n|      .*\n)+)", src, re.M).group(1)
    clauses = []
    for line in body.splitlines():
        m = re.match(r"\s*\| \.(\w+)(.*?) => (.*)$", line)
        if not m:
            raise ValueError(f"clause not understood: {line}")
        # an anonymous pattern variable `_` gets a name, so that the clause's rule can bind it
        lhs_args = [re.sub(r"(?<![\w'])_(?![\w'])", f"u{k}", a) for k, a in enumerate(split_args(m.group(2)))]
        lhs, rhs = (m.group(1), lhs_args), m.group(3).strip()
        if rhs == "none":
            clauses.append((lhs, None))
        else:
            mm = re.match(r"some \(\.(\w+)(.*)\)$", rhs)
            if not mm:
                raise ValueError(f"right side not understood: {rhs}")
            clauses.append((lhs, (mm.group(1), split_args(mm.group(2)))))
    return cons, start, clauses


def count(e, env=None):
    """'(b + 2)', '0', '_', '(2 * a + 3)' as a Lin; '_' stays a variable."""
    e = e.strip()
    if e.startswith("(") and e.endswith(")"):
        e = e[1:-1]
    return lin_of(P(lex(e)).expr(), env or {})


# ---------------------------------------------------------------- generation
def template(enc, defs, st, args):
    ps, cfgname, cargs = enc[st]
    env = {p: a for p, a in zip(ps, args)}
    e = ("app", [cfgname] + [P(lex(a)).app() for a in cargs])
    return cfg_of(e, env, defs)


def config(t):
    """A symtm Config (left tokens in reading order, so reversed, words too)."""
    q, left, right = t
    rl = [Rep(tuple(reversed(x.word)), x.n) if isinstance(x, Rep) else x for x in reversed(left)]
    return Config(rl, q, right)


def lean_cfg(t):
    return cfg_term(config(t))


def pull_near(cfg):
    """If the head is next to a repeat that may be empty, bring literal cells from its far side next to the head
    (`x (w)^n = (w2)^n x` on the left, `(w)^n x = x (w2)^n` on the right).  Returns the Rotate or None."""
    if cfg.left and isinstance(cfg.left[-1], Rep) and not cfg.left[-1].n.surely_ge(1):
        r = cfg.left[-1]
        for j in range(len(r.word), 0, -1):
            x = cfg.left[-1 - j:-1]
            if len(cfg.left) > j + 1 and all(isinstance(t, int) for t in x):
                xw = tuple(x) + r.word
                if xw[len(r.word):] == tuple(x):
                    w2 = xw[:len(r.word)]
                    cfg.left[-1 - j:] = [Rep(w2, r.n)] + list(x)
                    return symtm.Rotate("l", tuple(x), r.word, w2, r.n, rev=True)
    if cfg.right and isinstance(cfg.right[0], Rep) and not cfg.right[0].n.surely_ge(1):
        r = cfg.right[0]
        for j in range(len(r.word), 0, -1):
            x = cfg.right[1:1 + j]
            if len(cfg.right) > j + 1 and all(isinstance(t, int) for t in x):
                wx = r.word + tuple(x)
                if wx[:j] == tuple(x):
                    w2 = wx[j:]
                    cfg.right[:1 + j] = list(x) + [Rep(w2, r.n)]
                    return symtm.Rotate("r", tuple(x), r.word, w2, r.n, rev=True)
    return None


def flat(seq):
    """Repeats of a one-symbol word as repeats of that symbol, for comparing configurations."""
    return [Rep((t.word[0],), len(t.word) * t.n) if isinstance(t, Rep) and len(set(t.word)) == 1 else t for t in seq]


def no_blank_zeros(seq):
    """Blank tape absorbs the zeros next to it, repeated or not."""
    seq = list(seq)
    while len(seq) >= 2 and isinstance(seq[-1], Blank) and (seq[-2] == 0 or (isinstance(seq[-2], Rep) and seq[-2].word == (0,))):
        seq.pop(-2)
    while len(seq) >= 2 and isinstance(seq[0], Blank) and (seq[1] == 0 or (isinstance(seq[1], Rep) and seq[1].word == (0,))):
        seq.pop(1)
    return seq


def concrete(seq, env):
    out = []
    for t in seq:
        if isinstance(t, Rep):
            out += list(t.word) * t.n.subs(env)
        elif isinstance(t, int):
            out.append(t)
        elif not isinstance(t, Blank):
            out.append(t.name)
    return out


ENVS = [3, 4, 7, 10]


def same_flat(c1, c2):
    """Equal as tapes for several values of the variables (the stop test only; Lean checks the equation)."""
    if c1.state != c2.state:
        return False
    vs = sorted(c1.vars() | c2.vars())
    for k in ENVS:
        env = {v: k + 3 * i for i, v in enumerate(vs)}
        for a, b, rev in ((c1.left, c2.left, True), (c1.right, c2.right, False)):
            x, y = concrete(a, env), concrete(b, env)
            if rev:
                x, y = x[::-1], y[::-1]
            while x and x[-1] == 0:
                x.pop()
            while y and y[-1] == 0:
                y.pop()
            if x != y:
                return False
    return True


def run_near(m, cfg, stop, max_moves=100000, cross=True, trace=None, rotate=False, near=16):
    """`symtm.run`, except that before each move it looks whether up to `near` single steps reach the stop (a shift
    rule can jump past a target that lies inside the crossing, the first copy of a sweep), and that a repeat next to
    the head which may be empty gets literal cells from its far side first (`pull_near`)."""
    for _ in range(max_moves):
        if stop(cfg):
            return cfg
        before = cfg.copy()
        rot = pull_near(cfg)
        if rot is not None:
            if trace is not None:
                trace.append(("rot", before, cfg.copy(), rot))
            continue
        probe, sub = cfg.copy(), []
        try:
            for _k in range(near):
                before = probe.copy()
                symtm.step(m, probe)
                sub.append(("step", before, probe.copy()))
                if stop(probe):
                    cfg.left, cfg.right, cfg.state, cfg.steps = probe.left, probe.right, probe.state, probe.steps
                    if trace is not None:
                        trace.extend(sub)
                    return cfg
        except (symtm.NeedSplit, symtm.TouchContext, symtm.Halted):
            pass
        _one_move(m, cfg, cross, trace, rotate)
    raise RuntimeError(f"no stop after {max_moves} moves: {cfg}")


def _one_move(m, cfg, cross, trace, rotate):
    try:
        symtm_run(m, cfg, lambda _: False, max_moves=1, cross=cross, trace=trace, rotate=rotate)
    except RuntimeError:
        pass


def prove_any(m, name, a, b, doc):
    """A rule along the symbolic run, stopping at the first configuration equal to `b` (see `run_near`)."""
    symtm.run, symtm.same_config = run_near, same_flat
    try:
        return prove(m, name, a, b, rotate=True, max_seg=40, doc=doc, max_moves=3000, count_first=True)
    finally:
        symtm.run, symtm.same_config = symtm_run, symtm_same


def before_halt(m, c):
    while True:
        prev = c.copy()
        try:
            run(m, c, lambda _: False, max_moves=1, rotate=True)
        except Halted:
            return prev
        except RuntimeError:
            pass


def subst(x, env):
    """A Lin with variables replaced by Lins."""
    out = Lin(x.k)
    for v, c in x.c.items():
        out = out + c * env.get(v, Lin(v))
    return out


def prove_tree(m, enc, defs, rname, st, args, rhs, env, what, rules, depth=0):
    """The rule of one clause, split on a count the run needs to know is not 0 (`NeedSplit`): a tree of
    ('leaf', theorem name, its variables, halts?) and ('split', variable, tree for 0, tree for v + 1)."""
    a = config(template(enc, defs, st, [subst(x, env) for x in args]))
    print(f"{rname}: {a}", file=sys.stderr)
    try:
        if rhs is None:
            b = before_halt(m, a.copy())
        else:
            b = config(template(enc, defs, rhs[0], [subst(count(x), env) for x in rhs[1]]))
        txt, fin = prove_any(m, rname, a, b, what)
    except (ProofError, symtm.NeedSplit) as e:
        mm = re.search(r"NeedSplit: \(([01]+)\)\^([a-z]\w*)$", str(e))
        var = mm.group(mm.lastindex) if mm else None
        if var is None or depth >= 4:
            raise
        t0 = prove_tree(m, enc, defs, rname + "_0", st, args, rhs, {**{k: subst(x, {var: Lin(0)}) for k, x in env.items()}, var: Lin(0)} if var not in env else env, what, rules, depth + 1)
        e1 = {k: subst(x, {var: Lin(var) + 1}) for k, x in env.items()}
        e1[var] = Lin(var) + 1
        t1 = prove_tree(m, enc, defs, rname + "_1", st, args, rhs, e1, what, rules, depth + 1)
        return ("split", var, t0, t1)
    rules.append(txt)
    return ("leaf", rname, sorted(a.vars() | fin.vars()), rhs is None)


def lean_tree(t, ind):
    if t[0] == "leaf":
        call = t[1] + "".join(f" {v}" for v in t[2])
        return f"halt ({call})" if t[3] else f"land ({call})"
    _, v, t0, t1 = t
    return (f"match {v} with\n{ind}| 0 => {lean_tree(t0, ind + '  ')}\n{ind}| {v} + 1 => "
            f"{lean_tree(t1, ind + '  ')}")


def generate(M, dmfile=None):
    folder = os.path.join(ROOT, "holdouts", M)
    if dmfile is None:
        url = BASE + "M_" + M.replace("---", "HHH") + ".lean"
        dsrc = urllib.request.urlopen(url, timeout=60).read().decode()
    else:
        dsrc = open(dmfile).read()
    defs = read_defs(dsrc)
    enc = read_encode(dsrc, defs)
    cons, start, clauses = read_map(os.path.join(folder, "lean", "DeepMindMap.lean"))
    ns = re.search(r"^namespace (\S+)", open(os.path.join(folder, "lean", "Machine.lean")).read(), re.M).group(1)
    m = Machine.parse(M)
    rules, cases, spec, lemmas = [], [], {}, []
    # enc in Lean
    enc_lines = []
    for st, ps in cons.items():
        t = template(enc, defs, st, [Lin(p) for p in ps])
        spec[st] = repr(config(t))
        enc_lines.append(f"  | .{st}{''.join(' ' + p for p in ps)} => {lean_cfg(t)}")
    # the run from blank tape to start
    sst, sargs = start.split()[0], split_args(" ".join(start.split()[1:]))
    st0 = template(enc, defs, sst, [count(a) for a in sargs])
    txt, fin = prove(m, "blank_start", Config.parse("0^inf A> 0^inf"), config(st0), rotate=True, max_seg=40,
                     doc="From blank tape to the first state of the map.")
    rules.append(txt)
    for i, ((st, pats), rhs) in enumerate(clauses):
        args = [Lin(f"u{k}") if p == "_" else count(p) for k, p in enumerate(pats)]
        lhs = f".{st}" + "".join(" " + (f"u{k}" if p == "_" else p) for k, p in enumerate(pats))
        what = f"`{st} {' '.join(pats)}`" + (": halts." if rhs is None else f" to `{rhs[0]} {' '.join(rhs[1])}`.")
        tree = prove_tree(m, enc, defs, f"r{i}_{st}", st, args, rhs, {}, what, rules)
        vs = []
        for v in re.findall(r"\b[a-z]\w*\b", lhs):
            if v not in vs:
                vs.append(v)
        bind = f" ({' '.join(vs)} : Nat)" if vs else ""
        # `next` on the left side need not reduce by `rfl` (its match may split a count that the pattern leaves
        # open, as `b + 1` against `1` and `b + 2` elsewhere), so the clause's value is rewritten in first
        val = "none" if rhs is None else f"some (.{rhs[0]}{''.join(' ' + a for a in rhs[1])})"
        lemmas.append(f"theorem c{i}_{st}{bind} : TM.Lands trans Rel (enc ({lhs})) (next ({lhs})) := by\n"
                      f"  have e : next ({lhs}) = {val} := by first | rfl | simp only [next]\n"
                      f"  rw [e]\n  exact " + lean_tree(tree, "    ") + "\n")
        cases.append(f"  | {lhs} => c{i}_{st}" + "".join(" " + v for v in vs))
    return ns, rules, enc_lines, (lemmas, cases), spec, sst, sargs, fin


def write(M, ns, rules, enc_lines, cases, spec, sst, sargs):
    folder = os.path.join(ROOT, "holdouts", M)
    head = (f"import Machine\n\n/-! Rules of the halts-iff map of {M}: one per clause of DeepMind's `next`, generated by "
            f"`tools/deepmind/dmproof.py`; do not edit by hand. -/\n\nnamespace {ns}\n\nopen TM\n\n")
    with open(os.path.join(folder, "lean", "DMRules.lean"), "w") as f:
        f.write(head + "\n".join(rules) + f"\nend {ns}\n")
    p = os.path.join(folder, "lean", "DeepMindMap.lean")
    src = open(p if os.path.exists(p) else os.path.join(folder, "lean", "DMMap.lean")).read()
    dm = src[src.index("namespace DM"):src.index("end DM") + len("end DM")]
    stmt = re.search(r"(?:axiom|theorem) deepmind_halts_iff : (.*?)(?: := by)?$", src, re.M).group(1)
    module = re.search(r"`(BusyBeaver/BB6/[^`]*\.lean)`", src)
    where = f" (`{module.group(1)}`)" if module else ""
    out = f"""import Blank
import DMRules
import TM.MapOrbit

/-!
# DeepMind's halts-iff map, proved here

`DM.State`, `DM.start`, `DM.next` are DeepMind's (google-deepmind/cryptids{where}, commit 3647718), copied unchanged
but for `ℕ` written `Nat`.  Their file proves with Mathlib that the machine halts iff the orbit of `next` from `start`
stops.  Here the same statement is proved on this repository's machine semantics with core Lean (`deepmind_halts_iff`),
so it no longer needs to be cited.

`enc` gives the configuration of each state, transcribed from DeepMind's `cfg_*` templates.  Each clause of `next` is
a rule of `DMRules.lean`, found by the symbolic simulator and written by `tools/deepmind/dmproof.py`: the template of
the left side runs, in at least one step, to the template of the right side, or to a halting configuration.
`TM.halts_iff_orbit` turns that into the halts-iff statement.
-/

set_option autoImplicit false

namespace {ns}

{dm}

open TM DM

/-- The configuration of a state (DeepMind's `encode`). -/
def enc : State → Config
{chr(10).join(enc_lines)}

def Rel (s : State) (c : Config) : Prop := c = enc s

/-- `cfg_rfl` after unfolding `enc`. -/
macro "enc_rfl" : tactic => `(tactic| first | (simp only [enc]; done) | (simp only [enc]; cfg_rfl) | cfg_rfl | (simp only [enc, Nat.mul_succ]; cfg_rfl))

theorem land {{c c' d : Config}} {{n : Nat}} {{s : State}} (h : steps n c = some c') (e₁ : d = c := by enc_rfl)
    (e₂ : c' = enc s := by enc_rfl) (hn : 0 < n := by omega) : TM.Lands trans Rel d (some s) :=
  ⟨_, plus_of h e₁ e₂ hn, rfl⟩

theorem halt {{c c' d : Config}} {{n : Nat}} (h : steps n c = some c') (e₁ : d = c := by enc_rfl)
    (hd : step c' = none := by rfl) : TM.Lands trans Rel d none :=
  halts_at h e₁ hd

set_option maxHeartbeats 2000000 in
{(chr(10) + "set_option maxHeartbeats 2000000 in" + chr(10)).join(cases[0])}
/-- Every state lands where `next` says. -/
theorem step_enc : ∀ s, TM.Lands trans Rel (enc s) (next s)
{chr(10).join(cases[1])}

/-- **DeepMind's halts-iff map, proved here.**  The machine halts from blank tape if and only if the orbit of
DeepMind's `next` from `start` stops. -/
theorem deepmind_halts_iff : {stmt} := by
  have h : HaltsFromBlank ↔ ∃ n, TM.orbit next start n = none :=
    halts_iff_orbit (Rel := Rel) ⟨_, _, blank_start, by simp only [Rel]; enc_rfl⟩ (fun s c h => by subst h; exact step_enc s)
  have e : ∀ n, DM.orbit n = TM.orbit next start n := by
    intro n; induction n with
    | zero => rfl
    | succ n ih => simp only [DM.orbit, TM.orbit, ih]
  rw [h]
  constructor
  · rintro ⟨n, hn⟩; exact ⟨n, by rw [e, hn]; rfl⟩
  · rintro ⟨n, hn⟩; refine ⟨n, ?_⟩; rw [← e]; cases h' : DM.orbit n <;> simp_all

end {ns}
"""
    with open(os.path.join(folder, "lean", "DMMap.lean"), "w") as f:
        f.write(out)
    os.makedirs(os.path.join(folder, "py"), exist_ok=True)
    with open(os.path.join(folder, "py", "dmspec.json"), "w") as f:
        json.dump({"machine": M, "source": "google-deepmind/cryptids commit 3647718", "templates": spec}, f, indent=1)
        f.write("\n")


def install(M):
    """Replace the cited axiom by the proof: check.sh compiles DMRules.lean and DMMap.lean instead of
    DeepMindMap.lean, which is removed (DMMap.lean holds the same copy of DeepMind's map)."""
    lean = os.path.join(ROOT, "holdouts", M, "lean")
    p = os.path.join(lean, "check.sh")
    s = open(p).read()
    if "DMMap.lean" not in s:
        s = s.replace(" DeepMindMap.lean", " DMRules.lean DMMap.lean")
        open(p, "w").write(s)
    if os.path.exists(os.path.join(lean, "DeepMindMap.lean")):
        os.remove(os.path.join(lean, "DeepMindMap.lean"))


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    M = args[0]
    ns, rules, enc_lines, cases, spec, sst, sargs, _ = generate(M, args[1] if len(args) > 1 else None)
    write(M, ns, rules, enc_lines, cases, spec, sst, sargs)
    if "--install" in sys.argv:
        install(M)


if __name__ == "__main__":
    main()
