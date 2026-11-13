"""Replay the run of 1RB0LE_1RC---_1RD1RE_1LA0RF_0RC0LA_0LC0RB with the proved rules only, as a map on phase forms.

usage: python3 holdouts/1RB0LE_1RC---_1RD1RE_1LA0RF_0RC0LA_0LC0RB/py/macro.py [MAXSTEPS]
           prints every change of form, from O 14 37 11 at step 29,301, until MAXSTEPS (default 1e300) or until
           no rule of the table applies (the escaping branch)
       python3 .../py/macro.py --checkpoints FILE [MAXSTEPS]
           writes every macro state before MAXSTEPS (default 3e10) as a concrete tape, for c/checkpoints.c

Each move is one rule of `lean/Cycle.lean`, `lean/Phase.lean`, `lean/Branch.lean` or `lean/Ends.lean` (`RULES`: start form and
arguments, target form and arguments, step count, exactly as the Lean theorems state them), or k turns of a cycle
rule at once (its `*_iter`).  A rule applies when the parameters meet its offsets (`b+6` needs b >= 6) and its
constants; when none does, the replay stops and names the branch.  The step counts make the replay checkable
against the plain simulation: the forms it predicts must be on the tape at exactly the predicted steps.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "py"))
from bbtools.symtm import parse_lin  # noqa: E402

RULES = {
    'oentry': ('O', ['a', 'b+6', 'c+2'], 'S1', ['a+1', 'b+6', 'c'], '20*a+62*b+454'),
    'cycle': ('S1', ['a', 'b+2', 'c+2'], 'S1', ['a+3', 'b+14', 'c'], '80*a+72*b+1356'),
    'oexit': ('S1', ['a', 'b+6', '1'], 'RF', ['a+3', '5', 'b+12'], '70*a+142*b+2683'),
    'rcyc': ('RF', ['a', 'k', 'm+2'], 'RF', ['a', 'k+1', 'm+1'], '26*m+111'),
    'rend': ('RF2', ['a', 'q', '1'], 'EF', ['a', 'q'], '26*a+42*q+225'),
    'cycle2': ('T2', ['a', 'x+6', 'y+6', 'c+2'], 'T2', ['a+3', 'x+13', 'y+11', 'c'], '80*a+72*x+72*y+1962'),
    'cycle3': ('T3', ['a', 'x+6', 'd+5', 'y+6', 'z+6', 'c+2'], 'T3', ['a+4', 'x+14', 'd', 'y+13', 'z+11', 'c'],
               '80*a+80*d+40*x+72*y+72*z+2466'),
    'eentry': ('EF', ['a+7', 'q+5'], 'T3', ['5', '14', 'a', '8', '7', 'q+2'], '120*a+2501'),
    'texit0': ('T3', ['a', 'x+5', '0', 'y+2', 'z+2', 'c+1'], 'T2', ['a+1', 'x+y+6', 'z+6', 'c+1'],
               '20*a+62*x+62*y+10*z+586'),
    'texit1': ('T3', ['a', 'x+6', '1', 'y+5', 'z+6', 'c+2'], 'U3', ['a+2', 'x+6', 'y+6', 'z+11', 'c'],
               '40*a+72*x+72*y+72*z+1950'),
    'texit2': ('T3', ['a', 'x+6', '2', 'y+5', 'z+6', 'c+2'], 'U3', ['a+2', 'x+8', 'y+6', 'z+11', 'c'],
               '40*a+72*x+72*y+72*z+2060'),
    'texit3': ('T3', ['a', 'x+6', '3', 'y+5', 'z+6', 'c+3'], 'T2', ['a+5', 'x+y+21', 'z+15', 'c+1'],
               '100*a+102*x+134*y+82*z+3880'),
    'texit4': ('T3', ['a', 'x+6', '4', 'y+5', 'z+6', 'c+3'], 'T2', ['a+5', 'x+y+23', 'z+15', 'c+1'],
               '100*a+102*x+134*y+82*z+4104'),
    'ucyc': ('U3', ['a', 'x+2', 'y+6', 'z+6', 'c+2'], 'U3', ['a+3', 'x+9', 'y+6', 'z+11', 'c'],
             '80*a+72*x+72*y+72*z+2396'),
    't2exit0': ('T2', ['a', 'x+2', 'y+10', '0'], 'RG', ['a+3', 'x+1', '4', 'y+6'], '50*a+2*x+106*y+1454'),
    't2exit1': ('T2', ['a', 'x+2', 'y+12', '1'], 'RG', ['a+3', 'x+1', '5', 'y+7'], '50*a+2*x+132*y+1771'),
    'gcyc': ('RG', ['a', 'x', 'n', 'm+2'], 'RG', ['a', 'x', 'n+1', 'm+1'], '26*m+111'),
    'gend': ('RG2', ['a+2', 'x', 'q', '1'], 'O', ['a+1', 'x+9', 'q+1'], '10*a+42*q+8*x+326'),
    'uexit0': ('U3', ['a', 'x+2', 'y+6', 'z+10', '0'], 'RG3', ['a+3', 'x+7', 'y+4', '4', 'z+10'],
               '70*a+64*x+64*y+116*z+3160'),
    'uexit1': ('U3', ['a', 'x+2', 'y+6', 'z+12', '1'], 'RG3', ['a+3', 'x+7', 'y+4', '5', 'z+11'],
               '70*a+64*x+64*y+142*z+3601'),
    'g3cyc': ('RG3', ['a', 'x', 'y', 'n', 'm+2'], 'RG3', ['a', 'x', 'y', 'n+1', 'm+1'], '26*m+111'),
    'g3end': ('RG3p', ['a', 'x', 'y+4', 'q+2', '1'], 'T2', ['a+3', 'x+9', 'y+10', 'q+1'], '90*a+42*q+80*x+80*y+2072'),
    'sexit0': ('S1', ['a', 'b+3', '0'], 'RF', ['a+3', '4', 'b+10'], '70*a+116*b+2100'),
    'gendo': ('RG2o', ['a+3', 'x+6', 'q+3', '1'], 'T3', ['1', '6', 'a', '11', 'x+14', 'q+1'],
              '66*a+42*q+106*x+2410'),
    'g3endo': ('RG3o', ['a+7', 'x+10', 'y+2', 'q+3', '1'], 'T3', ['5', '14', 'a', '15', 'x+y+17', 'q+1'],
               '146*a+42*q+148*x+106*y+4952'),
    'rende': ('RF2e', ['a', 'q', '1'], 'O', ['a', '0', 'q+1'], '10*a+42*q+212'),
    'ozero': ('O', ['a', '0', 'c+3'], 'T3', ['a+2', '0', '0', '0', '7', 'c'], '60*a+672'),
}


class Escape(Exception):
    pass


def _ev(lin, env):
    return lin.k + sum(c * env[v] for v, c in lin.c.items())


def _bind(rule, P):
    env = {}
    for a, p in zip(RULES[rule][1], P):
        L = parse_lin(a)
        if not L.c:
            if L.k != p:
                return None
            continue
        (v, _), = L.c.items()
        if p < L.k:
            return None
        env[v] = p - L.k
    return env


def apply(rule, P):
    env = _bind(rule, P)
    if env is None:
        raise Escape(f"{rule} does not apply to {P}")
    _, _, tf, targs, st = RULES[rule]
    return tf, [_ev(parse_lin(s), env) for s in targs], _ev(parse_lin(st), env)


def iterate(rule, P, k):
    """k turns of a cycle rule: parameters and the total step count (the per-turn count is linear in them)."""
    if k == 0:
        return P, 0
    _, P1, s0 = apply(rule, P)
    delta = [b - a for a, b in zip(P, P1)]
    idx = {next(iter(parse_lin(a).c)): i for i, a in enumerate(RULES[rule][1]) if parse_lin(a).c}
    slope = sum(c * delta[idx[v]] for v, c in parse_lin(RULES[rule][4]).c.items())
    return [p + k * d for p, d in zip(P, delta)], k * s0 + slope * k * (k - 1) // 2


def move(form, P):
    """One move of the table: (form, parameters, steps), or Escape naming the missing branch."""
    if form == "O":
        return apply("ozero" if P[1] == 0 else "oentry", P)
    if form == "S1":
        if P[2] >= 2:
            return ("S1",) + tuple(iterate("cycle", P, P[2] // 2))
        return apply("oexit" if P[2] == 1 else "sexit0", P)
    if form == "RF":
        a, k, m = P
        if m >= 2:
            return ("RF",) + tuple(iterate("rcyc", P, m - 1))
        if k % 2:
            return apply("rend", [a, (k - 1) // 2, 1])             # rend' : RF a (2q+1) 1 = RF2 a q 1
        return apply("rende", [a, k // 2, 1])                      # rende' : RF a (2q) 1 = RF2e a q 1
    if form == "EF":
        return apply("eentry", P)
    if form == "T3":
        d, c = P[2], P[5]
        if P[1] == P[2] == P[3] == 0:
            return "S1", [P[0], P[4], P[5]], 0                     # T3 a 0 0 0 z c is S1 a z c (t3_s1)
        if d >= 5:
            k = min(d // 5, c // 2)
            if k == 0:
                raise Escape(f"T3 {P}: the 14-cell words run out before the 0010s")
            return ("T3",) + tuple(iterate("cycle3", P, k))
        return apply(f"texit{d}", P)
    if form == "T2":
        if P[3] >= 2:
            return ("T2",) + tuple(iterate("cycle2", P, P[3] // 2))
        return apply(f"t2exit{P[3]}", P)
    if form == "U3":
        if P[4] >= 2:
            return ("U3",) + tuple(iterate("ucyc", P, P[4] // 2))
        return apply(f"uexit{P[4]}", P)
    if form == "RG":
        a, x, n, m = P
        if m >= 2:
            return ("RG",) + tuple(iterate("gcyc", P, m - 1))
        if n % 2 == 0:
            return apply("gend", [a, x, n // 2, 1])                # gend' : RG a x (2q) 1 = RG2 a x q 1
        return apply("gendo", [a, x, n // 2, 1])                   # gendo' : RG a x (2q+1) 1 = RG2o a x q 1
    if form == "RG3":
        a, x, y, n, m = P
        if m >= 2:
            return ("RG3",) + tuple(iterate("g3cyc", P, m - 1))
        if n % 2 == 0:
            return apply("g3end", [a, x, y, n // 2, 1])
        return apply("g3endo", [a, x, y, n // 2, 1])
    raise Escape(f"no rule for form {form}")


START = ("O", [14, 37, 11], 29301)


def replay(maxt):
    """[(step, form, params)] of the macro states before maxt, and the escape message or None."""
    form, P, t = START
    out = []
    while t < maxt:
        out.append((t, form, list(P)))
        try:
            form, P, s = move(form, P)
        except Escape as e:
            return out, str(e)
        t += s
    return out, None


def main():
    args = sys.argv[1:]
    if args and args[0] == "--checkpoints":
        from bbtools.symtm import Config, Rep, Blank
        from branch import FORMS
        rows, _ = replay(float(args[2]) if len(args) > 2 else 3e10)

        def bits(toks):
            out = []
            for t in toks:
                if isinstance(t, Rep):
                    out.extend(list(t.word) * t.n.k)
                elif not isinstance(t, Blank):
                    out.append(t)
            return out
        with open(args[1], "w") as fh:
            for t, f, P in rows:
                c = Config.parse(FORMS[f](*map(str, P)))
                L, R = bits(c.left), bits(c.right)
                fh.write(f"{t} {c.state} {len(L)} {''.join(map(str, L + R))}\n")
        print(len(rows), "checkpoints written")
        return
    rows, esc = replay(float(args[0]) if args else 1e300)
    last = None
    for t, f, P in rows:
        if f != last or f in ("O", "EF"):
            print(f"{t:>26,}  {f} {' '.join(map(str, P))}")
        last = f
    print("escape:" if esc else "reached the step bound", esc or "")


if __name__ == "__main__":
    main()
