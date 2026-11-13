"""The list configuration `fsteps n (FCfg.blank A)` of tools/lean/TM/Fin.lean, computed in Python, and a Lean
theorem `steps n init = some (FCfg.toCfg ⟨l, r, .S⟩)` for it, to be closed by `native_decide` or the kernel.
Shared by the G12 machines of this worker (the other folders refer to this file).

usage: python3 fcfg.py MACHINE STEPS NAME [kernel]
"""
import sys


def table(text):
    t = {}
    for i, g in enumerate(text.split("_")):
        for r in (0, 1):
            s = g[3 * r:3 * r + 3]
            t[(i, r)] = None if s[2] == "-" else (int(s[0]), s[1], ord(s[2]) - 65)
    return t


def fsteps(text, n):
    """Mirror of `fsteps`: l and r are lists of 0/1, nearest cell first; None if it halts within n steps."""
    t = table(text)
    l, r, s = [], [], 0
    for _ in range(n):
        x = r[0] if r else 0
        tr = t[(s, x)]
        if tr is None:
            return None
        w, d, s = tr
        if d == "R":
            l = [w] + l
            r = r[1:]
        else:
            r = [l[0] if l else 0, w] + r[1:]
            l = l[1:]
    return l, r, s


def lean_list(xs):
    return "[" + ", ".join("true" if x else "false" for x in xs) + "]"


def theorem(text, n, name, how="native_decide", doc=None):
    l, r, s = fsteps(text, n)
    proof = "by native_decide" if how == "native_decide" else "by decide +kernel"
    d = doc or f"The configuration after {n:,} steps from blank tape."
    return (f"/-- {d} -/\ntheorem {name} :\n    steps {n} init = some (FCfg.toCfg ⟨{lean_list(l)},\n      "
            f"{lean_list(r)}, .{'ABCDEF'[s]}⟩) :=\n  blank_reaches trans ({proof})\n")


if __name__ == "__main__":
    print(theorem(sys.argv[1], int(sys.argv[2]), sys.argv[3], "kernel" if len(sys.argv) > 4 else "native_decide"))
