"""Exact batching of translation cycles for piecewise-affine phase maps given as data (used by `accel`).

RULES: tag -> list of (conds, rhs), in Lean's top-to-bottom match order.  conds has one entry per component of the
state (after the tag): ('=', c) or ('>=', c).  rhs is None (next is none) or (tag2, forms), each form
(const, ((i, coef), ...)) an affine function of the input components.

cycle_accel(RULES, s): try cycle lengths L = 1..LMAX.  Follow L rules from s symbolically; if the composite is a pure
translation s -> s + d on the same tag, then at the i-th repetition the j-th intermediate state is x_j + i * e_j, and
every match condition is an interval in i.  k = the number of repetitions for which, at every j, the rule taken at
i = 0 still matches and no earlier rule of that tag matches.  If k >= 2 the k repetitions are returned as one jump of
k * L phases (exact: each repetition is the same sequence of first-matching rules).  Otherwise None.
"""

LMAX = 8
INF = float("inf")


def _match(conds, x):
    for (op, c), v in zip(conds, x):
        if op == "=":
            if v != c:
                return False
        elif v < c:
            return False
    return True


def _first(rules, tag, x):
    for idx, (conds, rhs) in enumerate(rules[tag]):
        if len(conds) == len(x) and _match(conds, x):
            return idx
    return None


def _interval(conds, a, e):
    """The set of i >= 0 with conds true at a + i*e, as (lo, hi) (hi may be INF), or None if empty."""
    lo, hi = 0, INF
    for (op, c), ai, ei in zip(conds, a, e):
        if op == "=":
            if ei == 0:
                if ai != c:
                    return None
            else:
                q, r = divmod(c - ai, ei)
                if r or q < 0:
                    return None
                lo, hi = max(lo, q), min(hi, q)
        else:
            if ei == 0:
                if ai < c:
                    return None
            elif ei > 0:
                lo = max(lo, max(0, -((ai - c) // ei)))  # ceil((c - ai) / ei)
            else:
                hi = min(hi, (ai - c) // (-ei))
        if lo > hi:
            return None
    return lo, hi


def _apply(forms, x):
    return tuple(c + sum(k * x[i] for i, k in co) for c, co in forms)


def _compose(forms, M):
    """forms applied to the affine state M (list of (const, coef-vector)) -> new list."""
    out = []
    for c, co in forms:
        cc = c
        vec = [0] * len(M[0][1])
        for i, k in co:
            cc += k * M[i][0]
            for t in range(len(vec)):
                vec[t] += k * M[i][1][t]
        out.append((cc, vec))
    return out


def cycle_accel(rules, s):
    tag0, x0 = s[0], tuple(s[1:])
    n = len(x0)
    M = [(0, [1 if t == i else 0 for t in range(n)]) for i in range(n)]  # identity: state as affine in x0
    tag, x = tag0, x0
    path = []  # (tag, rule index, affine state M_j before the rule)
    for L in range(1, LMAX + 1):
        idx = _first(rules, tag, x)
        if idx is None:
            return None
        rhs = rules[tag][idx][1]
        if rhs is None:
            return None
        path.append((tag, idx, M))
        tag2, forms = rhs
        M = _compose(forms, M)
        x = _apply(forms, x)
        tag = tag2
        if tag != tag0 or len(x) != n:
            continue
        if any(M[i][1] != [1 if t == i else 0 for t in range(n)] for i in range(n)):
            continue
        d = tuple(M[i][0] for i in range(n))
        if not any(d):
            continue
        k = INF
        for (tj, ij, Mj) in path:
            a = tuple(Mj[r][0] + sum(Mj[r][1][t] * x0[t] for t in range(n)) for r in range(len(Mj)))
            e = tuple(sum(Mj[r][1][t] * d[t] for t in range(n)) for r in range(len(Mj)))
            for i2, (conds, _) in enumerate(rules[tj][:ij + 1]):
                if len(conds) != len(a):
                    continue
                iv = _interval(conds, a, e)
                if i2 == ij:
                    k = min(k, iv[1] + 1)  # iv[0] == 0 here
                elif iv is not None:
                    k = min(k, iv[0])
        if k == INF:
            raise RuntimeError("cycle %r repeats forever from %r (the orbit never halts)" % (path, s))
        if k < 2:
            return None
        k = int(k)
        y = tuple(xi + k * di for xi, di in zip(x0, d))
        lab = "cyc:" + "/".join("%s%d" % (t, i) for t, i, _ in path)
        return (tag0,) + y, k * L, lab
    return None
