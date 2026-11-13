"""Symbolic closure check of the level system of 1RB0RE_0LC0RF_1LD1LC_1RA0LD_0RD1RE_---0LB.

A *sample* is a configuration  0^inf D> 0 ...  (state D on a 0 with blank tape to its left).  A *level start* is a
sample of the form  0^inf D> 0 0 1^5 100 (10111)^b T 0^inf .  Its *type* is the sequence of words and cells of the
tape with the block counts left out; its parameters are the block counts.

`explore` runs the machine symbolically (tools/py/bbtools/symtm.py: single steps and shift rules on a tape whose block
counts are linear forms in variables k0, k1, ... >= 0) from a level start of a type, every parameter p_i = LB_i + k_i,
to the next level start.  Three devices keep the run finite:

 * cycle jumps.  When a sample has the same words as two earlier ones, equally spaced, and every count moves by the
   same constant d_i each time, the stretch is re-run with every changing or symbolic count replaced by v_i + T_i,
   v_i >= 0 free (`verify_cycle`).  If that run ends in the same words with counts v_i + T_i + d_i, the cycle is a
   theorem for all v >= 0; it is stored (with all its rotations: the samples it passes through) and applied n times
   at once wherever a sample matches, n = min over the shrinking counts of floor(v_i / |d_i|), so that every
   intermediate v stays >= 0.
 * case splits on residues.  If n is not a linear form because a variable's coefficient is not a multiple of |d_i|,
   the variable is replaced by q*k + r for each residue r and the run continues in each case from where it stands.
 * case splits on zero.  If the run needs to know whether a count is zero, the block is first made longer (the same
   level is run with the variable raised by BIG, only to find the cycles of that phase); if no cycle then
   applies, the variable is split into 0 and k + 1.

The result for each case is the next level's type and parameters as linear forms in the final variables.  `closure`
repeats this for every type that turns up, keeping for each type a lower bound LB for its parameters, until every
level start of a listed type with parameters >= LB is shown to lead to a level start of a listed type with parameters
>= that type's LB (CLOSED), or a case fails.  A halt would stop a symbolic run (`Halted`), so in a closed system no
level start halts and each is followed by another: the machine runs for ever once it reaches one.

Result (13 November 2026, about 60 s): 14 types; 91 cases pass, 2 fail; NOT CLOSED.  Twelve types pass for every
block count: the four short tails P, Q, R, S (types 0, 3, 2, 1) and types 5 to 9 and 11 to 13.  The two failing
cases belong to the two types whose tail holds a long block of six-cell words, (100111)^m (type 4) or (110011)^m
(type 10), with m above the first two values tried: there the machine counts to m - 1 in binary between the blocks
(py/counter.py), a phase in which no sample shape repeats with constant count steps.  The run gives up on such a
case after ZSPLITS zero splits.  The run from blank tape enters type 4 (level 7, m = 2,702) and type 10.

Trust: this file and symtm's symbolic steps (the same engine whose traces Lean checks for the rules in lean/).
Nothing here is checked by Lean.

usage (from the repo root):
  python3 holdouts/1RB0RE_0LC0RF_1LD1LC_1RA0LD_0RD1RE_---0LB/py/closure.py [SECONDS [STATEFILE]]
"""
import itertools
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "py"))
import bbtools.symtm as symtm  # noqa: E402
from bbtools.symtm import Blank, Config, Lin, Rep, canon, run, NeedSplit, Halted, TouchContext, parse_lin  # noqa: E402
from bbtools.macro import Machine  # noqa: E402

M = "1RB0RE_0LC0RF_1LD1LC_1RA0LD_0RD1RE_---0LB"
MACH = Machine.parse(M)
D = 3
symtm.MAX_CARRY = 10      # a zigzag that eats a block word by word carries up to ten cells along



def fold(out):
    """Literal copies after a repeat join it; adjacent repeats of one word merge."""
    i = 0
    while i < len(out):
        t = out[i]
        if isinstance(t, Rep):
            L, n, j = len(t.word), t.n, i + 1
            while True:
                nxt = out[j:j + L]
                if len(nxt) == L and all(isinstance(x, int) for x in nxt) and tuple(nxt) == t.word:
                    n, j = n + 1, j + L
                elif j < len(out) and isinstance(out[j], Rep) and out[j].word == t.word:
                    n, j = n + out[j].n, j + 1
                else:
                    break
            out[i:j] = [Rep(t.word, n)]
        i += 1
    return out


def norm(right):
    """Canonical token list of a right tape: symtm.canon (with each symbolic count hidden behind a fresh name, so
    that canon does not write its constant part out as cells), then `fold`."""
    env, toks = {}, []
    for t in right:
        if isinstance(t, Rep) and not t.n.is_const():
            name = f"u{len(env)}"
            env[name] = t.n
            toks.append(Rep(t.word, Lin(name)))
        else:
            toks.append(t)
    out = []
    for t in canon(toks):
        if isinstance(t, Rep):
            n = Lin(t.n.k)
            for v, a in t.n.c.items():
                n = n + a * env[v]
            out.append(Rep(t.word, n))
        else:
            out.append(t)
    return fold(out)


def compress(toks):
    """Fold literal stretches: at least three copies of a word of 2 to 6 cells become a repeat with a constant count
    (so that a block that grows from nothing has the same shape at successive samples)."""
    out, i = [], 0
    while i < len(toks):
        best = None
        if isinstance(toks[i], int):
            for w in range(2, 7):
                word = toks[i:i + w]
                if len(word) < w or not all(isinstance(x, int) for x in word):
                    break
                if any(w % q == 0 and word == word[:q] * (w // q) for q in range(1, w)):
                    continue
                k = 1
                while toks[i + k * w:i + (k + 1) * w] == word:
                    k += 1
                if k >= 3 and (best is None or k * w > best[0] * best[1]):
                    best = (k, w)
        if best:
            k, w = best
            out.append(Rep(tuple(toks[i:i + w]), Lin(k)))
            i += k * w
        else:
            out.append(toks[i])
            i += 1
    return fold(out)


def key_counts(toks):
    key = tuple(t.word if isinstance(t, Rep) else ("B" if isinstance(t, Blank) else t) for t in toks)
    return key, [t.n for t in toks if isinstance(t, Rep)]


def build(key, counts):
    it = iter(counts)
    return [Rep(t, next(it)) if isinstance(t, tuple) else (Blank() if t == "B" else t) for t in key]


def is_sample(c):
    return (c.state == D and not c.steps.is_zero() and all(isinstance(t, Blank) or t == 0 for t in c.left)
            and c.right and c.right[0] == 0)


class Fail(Exception):
    pass


class Need(Exception):
    """The run needs to know whether a count is zero."""
    def __init__(self, count):
        super().__init__(str(count))
        self.count = count


class Modulus(Exception):
    """A jump needs variable `var` modulo `q`."""
    def __init__(self, var, q):
        super().__init__(f"{var} mod {q}")
        self.var, self.q = var, q


NVISIT = 0


def visit(right):
    """One visit: from the sample with right tape `right` to the next sample, in compressed normal form."""
    global NVISIT
    NVISIT += 1
    c = Config([Blank()], D, list(right))
    try:
        c = run(MACH, c, is_sample, rotate=True, max_moves=20000)
    except NeedSplit as e:
        raise Need(e.args[0].n if e.args and isinstance(e.args[0], Rep) else None)
    except Halted as e:
        raise Fail(f"HALT {e}")
    except (TouchContext, RuntimeError) as e:
        raise Fail(f"{type(e).__name__} {e}")
    out = norm(c.right)
    for t in out:
        if isinstance(t, Rep) and not t.n.surely_ge(0):
            raise Fail(f"negative count {t}")
    return compress(out)


LEVEL_HEAD = [0, 0, 1, 1, 1, 1, 1, 1, 0, 0]


def is_level_start(toks):
    return toks[:10] == LEVEL_HEAD and isinstance(toks[10], Rep) and toks[10].word == (1, 0, 1, 1, 1)


def subst(l, var, repl):
    a = l.c.get(var, 0)
    return l if not a else l - a * Lin(var) + a * repl


# ---------------------------------------------------------------- cycles
LIB = {}          # key -> list of (pattern, deltas, visits);  pattern[i] = ("c", const) or ("v", index, offset)
TRIED = set()


def verify_cycle(key, deltas, counts, nvis):
    """Is the stretch of nvis visits from the sample (key, counts) a cycle for every size of its blocks?  Every count
    that changes or is symbolic becomes v_i + T_i with a free v_i >= 0 (constant counts that do not change stay).
    First with independent variables, then with one variable for the changing counts that differ by a constant and
    move by the same amount.  On success the cycle and its rotations are added to LIB."""
    n = len(deltas)
    free = [bool(deltas[i]) or not counts[i].is_const() for i in range(n)]
    for tie in (False, True):
        var, reps = [None] * n, []
        for i in range(n):
            if not free[i]:
                continue
            if tie and deltas[i]:
                for j in reps:
                    if deltas[j] == deltas[i] and (counts[i] - counts[j]).is_const():
                        var[i] = j
                        break
            if var[i] is None:
                var[i] = i
                reps.append(i)
        off = [0 if var[i] is None else (counts[i] - counts[var[i]]).k for i in range(n)]
        sig = (key, tuple(deltas), tuple(None if free[i] else counts[i].k for i in range(n)), tuple(var), tuple(off), nvis)
        if sig in TRIED:
            continue
        TRIED.add(sig)
        for t in range(0, 9):
            base = {j: t + max(0, -deltas[j]) + max(0, -min(off[i] for i in range(n) if var[i] == j)) for j in reps}
            cs = [counts[i] if var[i] is None else Lin(f"v{var[i]}") + base[var[i]] + off[i] for i in range(n)]
            toks = build(key, cs)
            trail = []
            try:
                for _ in range(nvis):
                    trail.append(key_counts(toks))
                    toks = visit(toks)
            except (Fail, Need):
                continue
            k2, c2 = key_counts(toks)
            if k2 == key and all(c2[i] == cs[i] + deltas[i] for i in range(n)):
                dv = {f"v{j}": deltas[j] for j in reps}
                for kj, cj in trail:              # the cycle from each sample it passes through
                    pat = []
                    for x in cj:
                        if x.is_const():
                            pat.append(("c", x.k))
                        elif len(x.c) == 1 and list(x.c.values()) == [1]:
                            pat.append(("v", list(x.c)[0], x.k))
                        else:
                            pat = None
                            break
                    if pat is not None:
                        LIB.setdefault(kj, []).append((tuple(pat), dv, nvis))
                return True
    return False


def floordiv(l, d):
    """l // d for a linear form whose variable coefficients are multiples of d; else Modulus."""
    for v, a in l.c.items():
        if a % d:
            from math import gcd
            raise Modulus(v, d // gcd(a, d))
    return Lin(l.k // d, {v: a // d for v, a in l.c.items()})


def lib_jump(key, counts):
    """Apply a stored cycle at this sample as often as possible.  Returns (new counts, n) or None."""
    for pat, dv, nvis in LIB.get(key, ()):
        env, ok = {}, True
        for p, x in zip(pat, counts):
            if p[0] == "c":
                ok = ok and x.is_const() and x.k == p[1]
            else:
                val = x - p[2]
                if p[1] in env and env[p[1]] != val:
                    ok = False
                env[p[1]] = val
            if not ok:
                break
        if not ok or not all(v.surely_ge(0) for v in env.values()):
            continue
        ns = [floordiv(env[v], -d) for v, d in dv.items() if d < 0 and v in env]
        if not ns:
            continue
        n = next((c for c in ns if all((o - c).surely_ge(0) for o in ns)), None)
        if n is None:
            raise Fail(f"case split: cycle counts {ns} not comparable")
        if not n.surely_ge(1):
            continue
        new = [x if p[0] == "c" else x + dv.get(p[1], 0) * n for p, x in zip(pat, counts)]
        if not all(x.surely_ge(0) for x in new):
            raise Fail(f"negative count after a jump: {new}")
        return new, n
    return None


def detect(hist, key, counts):
    """Find and verify a new cycle ending at this sample (seen twice in a row).  True if LIB grew.  hist is a list
    of (key, counts) with hist.pos: key -> indices."""
    n = len(hist)
    for i0 in reversed(hist.pos.get(key, ())):
        back = n - i0
        i1 = i0 - back
        if i1 < 0:
            break
        k1, c1 = hist[i1]
        if k1 != key:
            continue
        c0 = hist[i0][1]
        diffs = [counts[i] - c0[i] for i in range(len(counts))]
        if not all(d.is_const() for d in diffs) or [c0[i] - c1[i] for i in range(len(counts))] != diffs:
            continue
        deltas = [d.k for d in diffs]
        if not any(d < 0 for d in deltas):
            continue
        if verify_cycle(key, deltas, c0, back):
            return True
    return False


class Hist(list):
    def __init__(self):
        super().__init__()
        self.pos = {}

    def add(self, key, counts):
        self.pos.setdefault(key, []).append(len(self))
        self.append((key, counts))

    def clear(self):
        super().clear()
        self.pos = {}


VERBOSE = bool(os.environ.get('VERBOSE'))
ZSPLITS = 2       # splits of one case into count = 0 / count >= 1 before giving up
HIST = 3000        # samples kept for cycle detection in a normal run
BIG = 6720        # raise of a variable in a discovery run (a multiple of every cycle step seen)


def run_level(toks, params, hist, discover=False, maxvis=40000):
    """Run from the sample `toks` to the next level start.  Returns (key', counts', params).  Raises Modulus, Need
    (with .state = (toks, params) to resume from) or Fail."""
    nvis = 0
    cap = 8000 if discover else HIST
    hist = Hist()
    while True:
        k, c = key_counts(toks)
        j = lib_jump(k, c)
        if j is None and detect(hist, k, c):
            if discover:
                return None
            j = lib_jump(k, c)
        if j is not None:
            toks = build(k, j[0])
            hist.clear()
            continue
        hist.add(k, c)
        if len(hist) > cap:
            raise Fail('no cycle found in a long phase')
        try:
            toks = visit(toks)
        except Need as e:
            e.state = (build(k, c), params)
            raise
        nvis += 1
        if nvis > maxvis:
            raise Fail("too many visits")
        if is_level_start(toks):
            k, c = key_counts(norm(toks))          # the type: constant repeats written out as cells
            return k, c, params


def sub_all(toks, params, var, repl):
    toks = [Rep(t.word, subst(t.n, var, repl)) if isinstance(t, Rep) else t for t in toks]
    return compress(norm(toks)), [subst(p, var, repl) for p in params]


def explore(key, params, out, fails, budget):
    """All cases of the level from the level start (key, params).  Appends (params, key', counts') to out and
    (params, reason) to fails."""
    stack = [(build(key, params), list(params), 0, False, 0)]
    while stack:
        toks, ps, depth, discovered, zsplits = stack.pop()
        if VERBOSE:
            print(f"      case {[str(p) for p in ps]} depth {depth} stack {len(stack)} visits {NVISIT} lib {sum(len(v) for v in LIB.values())}", flush=True)
        if depth > 40:
            fails.append((ps, "too many case splits"))
            continue
        try:
            k2, c2, ps = run_level(compress(norm(toks)), ps, [])
            out.append((ps, k2, c2))
        except Modulus as e:
            for r in range(e.q):
                t2, p2 = sub_all(toks, ps, e.var, e.q * Lin(e.var) + r)
                stack.append((t2, p2, depth + 1, False, zsplits))
        except Need as e:
            cnt = e.count
            vs = [v for v in (cnt.c if cnt is not None else {})]
            if not vs:
                fails.append((ps, f"NeedSplit {cnt}"))
                continue
            var = vs[0]
            if not discovered:
                # find the cycles of this phase on a longer block, then try again from the same sample
                before = sum(len(v) for v in LIB.values())
                t2, p2 = sub_all(toks, ps, var, Lin(var) + BIG)
                try:
                    run_level(t2, p2, [], discover=True, maxvis=5000)
                except (Modulus, Need, Fail):
                    pass
                stack.append((toks, ps, depth, True, zsplits))
                continue
            # no cycle helps: split the variable into 0 and k + 1, from the sample where the question came up
            if zsplits >= ZSPLITS:
                fails.append((ps, f"a phase with no linear cycle (count {cnt} runs out)"))
                continue
            st_toks, st_ps = e.state
            for repl in (Lin(0), Lin(var) + 1):
                t2, p2 = sub_all(st_toks, st_ps, var, repl)
                stack.append((t2, p2, depth + 1, False, zsplits + 1))
        except Fail as e:
            fails.append((ps, str(e)))
        if budget():
            raise TimeoutError


def show(key):
    out = []
    for t in key:
        if isinstance(t, tuple):
            out.append("(" + "".join(map(str, t)) + ")^*")
        elif t != "B":
            out.append(str(t))
    return " ".join(out)


def start_key(tail):
    toks = norm(Config.parse(f"0^inf D> 0 0 (1)^5 1 0 0 (10111)^b {' '.join(tail)} 0^inf").right)
    return key_counts(toks)[0]


def closure(BASE, seconds=1e9, state=None, verbose=False):
    """Explore from the type of tail P with parameter >= BASE.  LB[type] is a lower bound for each parameter; a type
    is run again when an image with a smaller parameter turns up.  Returns (types, LB, results, fails, finished)."""
    import pickle
    import time
    t0 = time.time()
    if state and os.path.exists(state):
        types, LB, results, fails, todo, lib = pickle.load(open(state, "rb"))
        LIB.update(lib)
    else:
        types, LB, results, fails, todo = [start_key("10011110111100111")], {0: [BASE]}, {}, {}, [0]
    finished = True
    while todo:
        i = todo[0]
        key = types[i]
        params = [Lin(f"k{j}") + LB[i][j] for j in range(len(LB[i]))]
        out, fl = [], []
        try:
            explore(key, params, out, fl, lambda: time.time() - t0 > seconds)
        except TimeoutError:
            finished = False
            break
        todo.pop(0)
        results[i], fails[i] = [], fl
        for ps, k2, c2 in out:
            if any(not all(a >= 0 for a in x.c.values()) for x in c2):
                fails[i].append((ps, f"parameter not monotone {c2}"))
                continue
            if k2 not in types:
                types.append(k2)
            j = types.index(k2)
            low = [x.k for x in c2]
            if j not in LB:
                LB[j] = low
                todo.append(j)
            elif any(a < b for a, b in zip(low, LB[j])):
                LB[j] = [min(a, b) for a, b in zip(low, LB[j])]
                if j not in todo:
                    todo.append(j)
            results[i].append(([str(p) for p in ps], j, [str(x) for x in c2]))
        if verbose:
            print(f"type {i}: {show(key)}\n   parameters >= {LB[i]}: {len(results[i])} cases, {len(fl)} failed; "
                  f"{len(types)} types, {NVISIT} visits, {time.time() - t0:.0f} s", flush=True)
            for ps, why in fl[:5]:
                print(f"     FAIL {[str(p) for p in ps]}: {why[:160]}", flush=True)
        if state:
            pickle.dump((types, LB, results, fails, todo, LIB), open(state, "wb"))
    return types, LB, results, fails, finished and not todo


def main():
    seconds = float(sys.argv[1]) if len(sys.argv) > 1 else 1e9
    state = sys.argv[2] if len(sys.argv) > 2 else None
    types, LB, results, fails, finished = closure(24, seconds, state, verbose=True)
    print()
    for i, key in enumerate(types):
        if i not in results:
            print(f"type {i}: {show(key)}   not done")
            continue
        print(f"type {i}: {show(key)}   parameters >= {LB[i]}")
        by = {}
        for ps, j, c2 in results[i]:
            by.setdefault(j, []).append((ps, c2))
        for j, lst in sorted(by.items()):
            print(f"    -> type {j} in {len(lst)} cases, e.g. parameters {lst[0][0]} -> {lst[0][1]}")
    nf = sum(len(v) for v in fails.values())
    nc = sum(len(v) for v in results.values())
    print(f"{len(types)} types, {nc} cases, {nf} failed")
    print("CLOSED" if finished and not nf else ("NOT FINISHED" if not finished else "NOT CLOSED"))
    sys.exit(0 if finished and not nf else 1)


if __name__ == "__main__":
    main()
