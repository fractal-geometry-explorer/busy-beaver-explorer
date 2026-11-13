"""The round rules of the block-list family, written as symbolic configurations and proved with bbtools.symtm.

Frame A (1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_?): at an *event of depth j* the head is in state A on a 0 that it is
about to turn on (A0 -> 1RB), with
    L (1000)^q T_p  A>  0 (10)^(y_j) 1 (10)^(y_{j+1}) 1 ... (10)^(y_k) 1 0^inf
where the blocks right of the head are in the plain form (10)^y, the block left of the boundary is in the
"spread" form (1000)^q with one of five tails T_1 = 10, T_2 = 1, T_3 = 1001, T_4 = 101, T_5 = 11 (its phase), and
L is an unknown context.  A *round* at depth j takes phase p to phase p+1 (p = 1..4) and changes the suffix by
    eff(m) = (-4, -18, -90, ..., -18*5^(m-3), +12*5^(m-2))   (m = k-j+1 >= 2),   eff(1) = (+2),
plus 2 on the first block when p = 1.  `prove_round(m, p)` proves it for all values (above small offsets) and all
contexts and returns the Lean theorem and its step count.
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "..", "tools", "py"))
from bbtools.symtm import prove, Config, ProofError  # noqa: E402

CORE_A = "1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---"
TAILS = {1: "1 0", 2: "1", 3: "1 0 0 1", 4: "1 0 1", 5: "1 1"}
QOFF = {1: 0, 2: -1, 3: -2, 4: -2, 5: -2}     # (1000)^(q+K+QOFF[p]) T_p: the c-units consumed


def eff(m):
    if m == 1:
        return [2]
    return [-4] + [-18 * 5 ** i for i in range(m - 2)] + [12 * 5 ** (m - 2)]


def suffix(us, deltas=None):
    """right part: 0 (10)^(2u0+1) 1 (10)^(2u1) 1 ... 0^inf ; us are Lin strings like 'u0+12'"""
    parts = ["0", "1 0"]
    for i, u in enumerate(us):
        parts.append(f"(1010)^{u}")
        parts.append("1")
    parts.append("0^inf")
    return " ".join(parts)


def lin_add(name, c):
    return f"{name}+{c}" if c > 0 else (f"{name}-{-c}" if c < 0 else name)


def configs(m, p, K=24):
    e = eff(m)
    if p == 1:
        e = [e[0] + 2] + e[1:]
    offs = [max(0, -x // 2) + (3 if m <= 2 else 12) for x in e]
    names = [f"u{i}" for i in range(m)]
    us0 = [lin_add(n, c) for n, c in zip(names, offs)]
    us1 = [lin_add(n, c + x // 2) for n, c, x in zip(names, offs, e)]
    start = f"L (1000)^{lin_add('q', K + QOFF[p])} {TAILS[p]} A> " + suffix(us0)
    end = f"L (1000)^{lin_add('q', K + QOFF[p + 1])} {TAILS[p + 1]} A> " + suffix(us1)
    return start, end, offs


def prove_round(m, p, machine=CORE_A, name=None, **kw):
    start, end, offs = configs(m, p)
    name = name or f"round_m{m}_p{p}"
    txt, fin = prove(machine, name, start, end, rotate=True, count_first=True, max_moves=10 ** 7, **kw)
    return txt, fin, start, end


if __name__ == "__main__":
    m, p = int(sys.argv[1]), int(sys.argv[2])
    txt, fin, s, e = prove_round(m, p)
    print("--", s)
    print("->", e)
    print("steps", fin.steps)
    if len(sys.argv) > 3:
        print(txt)
