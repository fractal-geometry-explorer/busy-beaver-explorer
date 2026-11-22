"""Generate lean/StackRules.lean: the cell-level rules of the counter stack of
1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC, proved along the symbolic run (tools/py/bbtools/symtm.py).

usage:
  python3 stack.py > ../lean/StackRules.lean     generate the Lean rules
  python3 stack.py orbit STEPS                   along the orbit from step 10,206 of the run (zonemap.py, the step
                                                 map proved in Lean): how often `stepRes` of lean/Stack.lean answers,
                                                 and that it gives the same (W', N') as the step map
  python3 stack.py random CASES [SEED]           the same on random walls, against stackmodel.py
  python3 stack.py graph WALLS                   free parities: breadth-first search of the walls reached from `1`
                                                 by `stepRes` with N = 10^12 + parity; counts the steps where it
                                                 does not answer, and where stackmodel.py does not either

Each rule is a list of phases; each phase is a run of the symbolic simulator from one tape pattern to another
(`L`, `W`, `R` contexts: tape the run never reads), proved in Lean by `symtm.prove` (`rfl` pieces and the shift
rules `cross_r`/`cross_l`).  The end the run reaches is re-bracketed to the stated end by `tape_eq` (the normaliser
of `StackDefs.lean`).  Then the rule is stated with the interfaces of `StackDefs.lean` (`CALL`, `QQ`, `START`, the
contexts `Cx.top` = `1 0^inf` and `Cx.deep m c` = `1 0 1 0 b^m rhs(c)`).

The rules (W the wall below, any tape; b = 110):

* `sweepT`, `sweepD`  one sweep of the transfer loop (`W b^(x+2) 111 F> b^(y+1)` to `W b^x 111 F> b^(y+4)`), at the
                      top / under an item (one copy of the item's block is used up);
* `q1T`, `q1D`        `CALL W 1 (y+1)` reaches `QQ` (the head on the last cell of the wall: the signal even);
* `close`, `close0`   the signal even on an open counter (or the bottom `1`): `0 1` becomes `1`, the counter is closed;
* `b0`                the signal odd on the bottom `1`: a new open counter `K(0)`;
* `o0`, `k0`          the signal odd on an open counter `K(k+1)`, `K(0)`: its block becomes the left block of a new
                      junction one level down (the rest of the transfer loop moves 2 copies to 3), with a new context;
* `reb`               the answer from below under an open counter: the new block of the level below becomes the
                      counter `K(n)` and the step goes on in the context above;
* `cq`                the signal even on a closed counter `K'(j+1)`: its block becomes the left block of a junction;
* `c1T`, `c1D`        the signal odd on a closed counter `K'(j+2)` (two passes over the block, then as `cq`);
* `q0c`                the signal even on `K'(0)`: passes down, two more copies in the block;
* `k1T`, `k1D`        the signal odd on `K'(1)`: two passes over the block, the signal even goes down;
* `p0`                the signal odd on `1 K'(0)^(a+1)`: a new open counter `K(0)` on top;
* `part1`             the start of a step: `W A> 0 b^(n+5) 1` reaches the junction `CALL W n 12 .top`.
"""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "..", "tools", "py"))
from bbtools.symtm import prove, Config, Rep, Ctx, Blank, cfg_term  # noqa: E402

M = "1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC"
B = {0: "false", 1: "true"}

TOPR = "1 0^inf"
DEEPR = "1 0 1 0 (110)^m+1 R"
DEEPR0 = "1 0 1 0 (110)^m R"

# name, doc, interface binders, interface start, interface end, phases [(start, end, rotate)], args {name: term}
RULES = [
    ("sweepT", "One sweep at the top of the stack.", "(W : Tape) (x y : Nat)",
     "CALL W (x + 2) y .top", "CALL W x (y + 3) .top",
     [(f"W (110)^x+2 111 F> (110)^y+1 {TOPR}", f"W (110)^x 111 F> (110)^y+4 {TOPR}", True)], {}),
    ("sweepD", "One sweep under an item: one copy of the block above is used up.", "(W : Tape) (x y m : Nat) (c : Cx)",
     "CALL W (x + 2) y (.deep (m + 1) c)", "CALL W x (y + 3) (.deep m c)",
     [(f"W (110)^x+2 111 F> (110)^y+1 {DEEPR}", f"W (110)^x 111 F> (110)^y+4 {DEEPR0}", True)], {"R": "(rhs c)"}),
    ("q1T", "The junction with one copy left, at the top: the signal even reaches the wall `L 1`.", "(L : Tape) (y : Nat)",
     "CALL (cons true L) 1 (y + 1) .top", "QQ L (y + 5) .top",
     [(f"L 1 110 111 F> (110)^y+2 {TOPR}", f"L F> 1 (110)^y+5 {TOPR}", True)], {}),
    ("q1D", "The junction with one copy left, under an item.", "(L : Tape) (y m : Nat) (c : Cx)",
     "CALL (cons true L) 1 (y + 1) (.deep (m + 1) c)", "QQ L (y + 5) (.deep m c)",
     [(f"L 1 110 111 F> (110)^y+2 {DEEPR}", f"L F> 1 (110)^y+5 {DEEPR0}", True)], {"R": "(rhs c)"}),
    ("close", "The signal even on an open counter: `0 1` becomes `1` (the counter is closed).", "(L : Tape) (n : Nat) (c : Cx)",
     "QQ (cons false L) n c", "START (cons true L) n c",
     [("L 0 F> 1 R", "L 1 A> 0 R", True)], {"R": "(rep n [true, true, false] (rhs c))"}),
    ("close0", "The signal even on the bottom `1`: nothing changes.", "(n : Nat) (c : Cx)",
     "QQ blank n c", "START (cons true blank) n c",
     [("0^inf F> 1 R", "0^inf 1 A> 0 R", True)], {"R": "(rep n [true, true, false] (rhs c))"}),
    ("b0", "The signal odd on the bottom `1`: a new open counter `K(0)`.", "(y : Nat) (c : Cx)",
     "CALL (cons true blank) 0 (y + 1) c", "START (wt [.o 0]) (y + 1) c",
     [("0^inf 1 111 F> (110)^y+2 R", "0^inf 1 1111101 A> 0 (110)^y+1 R", True)], {"R": "(rhs c)"}),
    ("o0", "The signal odd on an open counter `K(k+1)`: its block becomes the left block of a junction one level down.",
     "(W : Tape) (k y : Nat) (c : Cx)",
     "CALL (itT (.o (k + 1)) W) 0 y c", "CALL W k 2 (.deep y c)",
     [("W (110)^k+1 1111101 111 F> (110)^y+1 R", "W (110)^k 111 F> (110)^3 1 0 1 0 (110)^y R", True)], {"R": "(rhs c)"}),
    ("k0", "The signal odd on an open counter `K(0)`: the signal even goes down.", "(L : Tape) (y : Nat) (c : Cx)",
     "CALL (itT (.o 0) (cons true L)) 0 y c", "QQ L 3 (.deep y c)",
     [("L 1 1111101 111 F> (110)^y+1 R", "L F> 1 (110)^3 1 0 1 0 (110)^y R", True)], {"R": "(rhs c)"}),
    ("reb", "The answer from below under an open counter: the new block becomes the counter.",
     "(W : Tape) (n m : Nat) (c : Cx)",
     "START W (n + 1) (.deep (m + 1) c)", "START (itT (.o n) W) (m + 1) c",
     [(f"W A> 0 (110)^n+1 {DEEPR}", "W (110)^n 1111101 A> 0 (110)^m+1 R", True)], {"R": "(rhs c)"}),
    ("cq", "The signal even on a closed counter `K'(j+1)`: its block becomes the left block of a junction.",
     "(W : Tape) (j n : Nat) (c : Cx)",
     "QQ (app [true, true, true, true, true] (rep (j + 1) [false, true, true] W)) n c", "CALL W j (n + 1) c",
     [("W (110)^j+1 11111 F> 1 (110)^n R", "W (110)^j 111 F> (110)^n+2 R", True)], {"R": "(rhs c)"}),
    ("c1T", "The signal odd on a closed counter `K'(j+2)`, at the top.", "(W : Tape) (j n : Nat)",
     "CALL (itT (.c (j + 2)) W) 0 n .top", "CALL W j (n + 6) .top",
     [(f"W (110)^j+2 111111 111 F> (110)^n+1 {TOPR}", f"W (110)^j 11 F> 0 (110)^n+7 {TOPR}", True),
      (f"W (110)^j 11 F> 0 (110)^n+7 {TOPR}", f"W (110)^j 111 F> (110)^n+7 {TOPR}", False)], {}),
    ("c1D", "The signal odd on a closed counter `K'(j+2)`, under an item: two copies of the block above are used up.",
     "(W : Tape) (j n m : Nat) (c : Cx)",
     "CALL (itT (.c (j + 2)) W) 0 n (.deep (m + 2) c)", "CALL W j (n + 6) (.deep m c)",
     [(f"W (110)^j+2 111111 111 F> (110)^n+1 1 0 1 0 (110)^m+2 R", f"W (110)^j 11 F> 0 (110)^n+7 {DEEPR0}", True),
      (f"W (110)^j 11 F> 0 (110)^n+7 {DEEPR0}", f"W (110)^j 111 F> (110)^n+7 {DEEPR0}", False)], {"R": "(rhs c)"}),
    ("q0c", "The signal even on a closed counter `K'(0)`: its six 1s become two copies of b and the signal goes on down.",
     "(L : Tape) (n : Nat) (c : Cx)",
     "QQ (app [true, true, true, true, true] (cons true L)) n c", "QQ L (n + 2) c",
     [("L 1 11111 F> 1 R", "L F> 1 110 110 R", True)], {"R": "(rep n [true, true, false] (rhs c))"}),
    ("k1T", "The signal odd on a closed counter `K'(1)`, at the top: the signal even goes down.", "(L : Tape) (y : Nat)",
     "CALL (itT (.c 1) (cons true L)) 0 y .top", "QQ L (y + 7) .top",
     [(f"L 1 110 111111 111 F> (110)^y+1 {TOPR}", f"L F> 1 (110)^y+7 {TOPR}", True)], {}),
    ("k1D", "The signal odd on a closed counter `K'(1)`, under an item.", "(L : Tape) (y m : Nat) (c : Cx)",
     "CALL (itT (.c 1) (cons true L)) 0 y (.deep (m + 2) c)", "QQ L (y + 7) (.deep m c)",
     [(f"L 1 110 111111 111 F> (110)^y+1 1 0 1 0 (110)^m+2 R", f"L F> 1 (110)^y+7 {DEEPR0}", True)], {"R": "(rhs c)"}),
    ("p0", "The signal odd on `1 K'(0)^(a+1)` (closed empty counters on the bottom): a new open counter `K(0)`.",
     "(a y : Nat) (c : Cx)",
     "CALL (rep (a + 1) [true, true, true, true, true, true] (cons true blank)) 0 (y + 1) c",
     "START (itT (.o 0) (rep (a + 1) [true, true, true, true, true, true] (cons true blank))) (y + 1) c",
     [("0^inf 1 (111111)^a+1 111 F> (110)^y+2 R", "0^inf 1 (111111)^a+1 1111101 A> 0 (110)^y+1 R", True)], {"R": "(rhs c)"}),
    ("part1", "The start of a step, for every wall `L 1`: the head crosses the block and builds the junction.",
     "(L : Tape) (n : Nat)",
     "START (cons true L) (n + 5) .top", "CALL (cons true L) n 12 .top",
     [(f"L 1 A> 0 (110)^n+5 {TOPR}", f"L 1 (110)^n 111 F> (110)^13 {TOPR}", True)], {}),
]


def word(w):
    return "[" + ", ".join(B[x] for x in w) + "]"


def segs(tokens, side):
    """Seg list (Lean) and base for a token list (left: far to near; right: near to far)."""
    if side == "l":
        base, body = tokens[0], list(reversed(tokens[1:]))
    else:
        base, body = tokens[-1], tokens[:-1]
    out, lit = [], []
    for t in body:
        if isinstance(t, int):
            lit.append(t)
        else:
            w = tuple(reversed(t.word)) if side == "l" else t.word
            var = t.n - t.n.k
            lit.extend(list(w) * t.n.k)
            if not var.is_zero():
                if lit:
                    out.append(f".l {word(lit)}")
                    lit = []
                out.append(f".r ({var.lean()}) {word(w)}")
    if lit:
        out.append(f".l {word(lit)}")
    return "[" + ", ".join(out) + "]", base


def side_eq(fin, end, side, args):
    from bbtools.symtm import left_term, right_term
    ft = left_term(fin.left) if side == "l" else right_term(fin.right)
    et = left_term(end.left) if side == "l" else right_term(end.right)
    if ft == et:
        return "rfl"
    s1, b1 = segs(fin.left if side == "l" else fin.right, side)
    s2, b2 = segs(end.left if side == "l" else end.right, side)
    assert repr(b1) == repr(b2), (b1, b2)
    if isinstance(b1, Blank):
        return f"(tape_eqB {s1} {s2} rfl)"
    return f"(tape_eq {s1} {s2} {b1.name} rfl)"


def binders(start, end):
    vs = sorted(start.vars() | end.vars())
    ctxs = []
    for x in start.contexts() + end.contexts():
        if x not in ctxs:
            ctxs.append(x)
    return vs, ctxs


def rule(name, doc, ibind, istart, iend, phases, args):
    out, calls, counts = [], [], []
    for i, (a, b, rot) in enumerate(phases):
        pn = f"{name}_{i}"
        raw, fin = prove(M, pn + "_raw", a, b, rotate=rot, count_first=True, max_moves=20000, max_seg=40)
        out.append(raw)
        start, end = Config.parse(a), Config.parse(b)
        vs, ctxs = binders(start, end)
        bnd = (f" ({' '.join(vs)} : Nat)" if vs else "") + (f" ({' '.join(ctxs)} : Tape)" if ctxs else "")
        names = vs + ctxs
        out.append(f"theorem {pn}{bnd} :\n    steps ({fin.steps.lean()}) {cfg_term(start)} = some {cfg_term(end)} :=\n"
                   f"  ({pn}_raw {' '.join(names)}).trans (congrArg some (cfg_eq {side_eq(fin, end, 'l', args)} "
                   f"{side_eq(fin, end, 'r', args)}))\n")
        calls.append(f"({pn} {' '.join(args.get(n, n) for n in names)})")
        counts.append(fin.steps.lean())
    chain = calls[-1]
    for c in reversed(calls[:-1]):
        chain = f"steps_seq trans {c} ({chain})"
    out.append(f"/-- {doc} -/\ntheorem {name} {ibind} :\n    steps ({' + '.join(counts) if len(counts) == 1 else ' + '.join(f'({c})' for c in counts)}) ({istart}) = some ({iend}) :=\n"
               f"  {chain}\n")
    return "\n".join(out)


# ---------------------------------------------------------------- res / stepRes of lean/Stack.lean, in Python
# walls: lists of items, TOP FIRST: ('o', k) open counter K(k), ('c', k) closed counter K'(k)

def go_x(ws, x, y):
    t = x // 2
    if x % 2 == 0:
        r = res(ws, True, y + 3 * t)
        return None if r is None else (r[0], r[1], t + r[2])
    if y + 3 * t >= 1:
        r = res(ws, False, y + 3 * t + 4)
        return None if r is None else (r[0], r[1], t + 1 + r[2])
    return None


def reb_r(y, r):
    if r is None:
        return None
    ws2, m, u = r
    return ([("o", m - 1)] + ws2, y - u, 0) if m >= 1 and u + 1 <= y else None


def res(ws, s, n):
    """(new wall, new count, copies used up from the block above), or None; s True = odd."""
    if not ws:
        return ([], n, 0) if not s else ([("o", 0)], n, 0) if n >= 1 else None
    (t, k), rest = ws[0], ws[1:]
    if t == "o":
        if not s:
            return [("c", k)] + rest, n, 0
        return reb_r(n, res(rest, False, 3) if k == 0 else go_x(rest, k - 1, 2))
    if k == 0:
        if not s:
            return res(rest, False, n + 2)
        return ([("o", 0)] + ws, n, 0) if all(x == ("c", 0) for x in rest) and n >= 1 else None
    if not s:
        return go_x(rest, k - 1, n + 1)
    r = res(rest, False, n + 7) if k == 1 else go_x(rest, k - 2, n + 6)
    return None if r is None else (r[0], r[1], 2 + r[2])


def step_res(ws, n):
    if n < 5:
        return None
    r = go_x(ws, n - 5, 12)
    return None if r is None else (r[0], r[1])


def to_lv(ws):
    return [(k, t == "c") for t, k in reversed(ws)]


def to_ws(lv):
    return [("c" if closed else "o", k) for k, closed in reversed(lv)]


def orbit(steps):
    import zonemap as Z
    import stackmodel as SM
    W, N = Z.START
    answered = differ = 0
    for i in range(steps):
        r = Z.step_map(W, N)
        lv = SM.unword(Z.show(W))
        m = None if lv is None else step_res(to_ws(lv), N)
        if m is not None:
            answered += 1
            if len(r) != 2 or SM.word(to_lv(m[0])) != Z.show(r[0]) or m[1] != r[1]:
                differ += 1
        if len(r) != 2:
            print("the step map stops at orbit step", i)
            break
        W, N = r
    print(f"{steps} orbit steps: stepRes answers in {answered}, differs from the step map in {differ}; "
          f"N has {N.bit_length()} bits")


def rand(cases, seed=1):
    import random
    import stackmodel as SM
    random.seed(seed)
    answered = differ = 0
    for _ in range(cases):
        lv = [(random.choice([0, 0, 1, 2, 3]) if random.random() < 0.3 else random.randint(0, 40), random.random() < 0.35)
              for _ in range(random.randint(0, 5))]
        for p in (0, 1):
            n = 10 ** 9 + p
            m = step_res(to_ws(lv), n)
            if m is None:
                continue
            answered += 1
            mm = SM.stepN(lv, n)
            differ += mm is None or to_lv(m[0]) != mm[0] or m[1] != mm[1]
    print(f"{2 * cases} (wall, parity) cases: stepRes answers in {answered}, differs from stackmodel.py in {differ}")


def graph(limit):
    from collections import deque
    sys.setrecursionlimit(1000000)
    seen, queue, steps, none = {(): 0}, deque([()]), 0, []
    while queue and len(seen) < limit:
        ws = list(queue.popleft())
        for p in (0, 1):
            steps += 1
            m = step_res(ws, 10 ** 12 + p)
            if m is None:
                none.append((ws, p))
                continue
            t = tuple(m[0])
            if t not in seen:
                seen[t] = seen[tuple(ws)] + 1
                queue.append(t)
    import stackmodel as SM
    model_none = sum(SM.stepN(to_lv(ws), 10 ** 12 + p) is None for ws, p in none)
    print(f"{len(seen)} walls, {steps} steps; stepRes does not answer in {len(none)}, and in {model_none} of these "
          f"stackmodel.py does not either (a count below zero)")


def main():
    head = ("import StackDefs\n\n/-! Rules of the counter stack of " + M + ", generated by `py/stack.py`; do not edit by hand.\n\n"
            "Each `*_raw` theorem is the symbolic run; `*_i` re-brackets its end; the last theorem of each group states the rule\n"
            "with the interfaces of `StackDefs.lean`. -/\n\nnamespace H3292\n\nopen TM\n\n")
    body = "\n".join(rule(*r) for r in RULES)
    sys.stdout.write(head + body + "\nend H3292\n")


if __name__ == "__main__":
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    if len(sys.argv) > 1 and sys.argv[1] == "orbit":
        orbit(int(sys.argv[2]))
    elif len(sys.argv) > 1 and sys.argv[1] == "graph":
        graph(int(sys.argv[2]))
    elif len(sys.argv) > 1 and sys.argv[1] == "random":
        rand(int(sys.argv[2]), int(sys.argv[3]) if len(sys.argv) > 3 else 1)
    else:
        main()
