"""Generate M2 (1RB0LE_1RC---_1RD1RE_1LA0RF_0RC0LA_0LC0RB) busycoq files: forms and rules."""
import os, re, sys
REPO = os.environ.get("BBX", "/home/user/busy-beaver-explorer")   # the busy-beaver-explorer checkout
M = REPO + "/holdouts/1RB0LE_1RC---_1RD1RE_1LA0RF_0RC0LA_0LC0RB"
sys.path.insert(0, M + "/py")
sys.path.insert(0, REPO + "/tools/py")
import ends, macro  # noqa
from bbtools.symtm import parse_lin  # noqa

FORMS = ends.FORMS
SYM = {"0": "S0", "1": "S1"}


def fvars(f):
    fn = FORMS[f]
    return list(fn.__code__.co_varnames[:fn.__code__.co_argcount])


def lin(const, coeffs):
    while coeffs and coeffs[-1] == 0:
        coeffs = coeffs[:-1]
    return "mkLin %d [%s]" % (const, ";".join(map(str, coeffs)))


def word(w):
    return "[" + ";".join(SYM[c] for c in w) + "]"


def form_mc(f):
    vs = fvars(f)
    s = FORMS[f](*["{%s}" % v for v in vs]).split()
    assert s[0] == "0^inf" and s[-1] == "0^inf"
    s = s[1:-1]
    h = [i for i, t in enumerate(s) if t.endswith(">")][0]
    st = s[h][0]
    toks = []
    body = s[1:] if h == 0 else s[:-1]
    for t in body:
        m = re.fullmatch(r"\(([01]+)\)\^\{(\w+)\}", t)
        if m:
            co = [0] * len(vs)
            co[vs.index(m.group(2))] = 1
            toks.append((m.group(1), lin(0, co)))
        else:
            toks.append(t)
    if h == 0:
        r = ["TR %s (%s)" % (word(w), n) if isinstance(w, str) and n else "" for w, n in []]
        mr = ["TB %s" % SYM[t] if isinstance(t, str) else "TR %s (%s)" % (word(t[0]), t[1]) for t in toks]
        return "mkMC [] [%s] %s" % ("; ".join(mr), st)
    ml = ["TB %s" % SYM[t] if isinstance(t, str) else "TR %s (%s)" % (word(t[0][::-1]), t[1]) for t in toks[::-1]]
    return "mkMC [%s] [] %s" % ("; ".join(ml), st)


def args_lin(args, rv):
    out = []
    for a in args:
        L = parse_lin(a)
        co = [L.c.get(v, 0) for v in rv]
        out.append(lin(L.k, co))
    return "[" + "; ".join("(%s)" % x for x in out) + "]"


def term(a):
    L = parse_lin(a)
    parts = []
    for v, c in L.c.items():
        parts.append(v if c == 1 else "%d * %s" % (c, v))
    if L.k or not parts:
        parts.append(str(L.k))
    s = " + ".join(parts)
    return s if re.fullmatch(r"\w+", s) else "(%s)" % s


def rule_vars(args):
    return sorted({v for a in args for v in parse_lin(a).c})


if __name__ == "__main__":
    for f in FORMS:
        print(f, form_mc(f))
    for k, (f, a, tf, ta, st) in macro.RULES.items():
        rv = rule_vars(a)
        print(k, rv, args_lin(a, rv), args_lin(ta, rv), " ".join(term(x) for x in a))
