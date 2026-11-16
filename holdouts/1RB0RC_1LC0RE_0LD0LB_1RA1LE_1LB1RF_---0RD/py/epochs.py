"""Epoch-to-epoch extrapolation for 1RB0RC_1LC0RE_0LD0LB_1RA1LE_1LB1RF_---0RD (and its twin), on the token model.

An epoch starts with the frame right after a reset (`c/toksim.c`: the machine run cell by cell where no token rule
applies).  Its right word has one long run of 0s, `0^Z`, the track of the marker: the marker walks 3 tokens per 2
overflows along it, and when it reaches the end of the track the epoch ends with the next reset.  Shortening the
track by 3 removes 2 overflows from the epoch and changes the frame after the next reset in a regular way: in the run
-length code of that frame every run length is an affine function of the number of 3s taken away, and so are the
number of overflows and the length of the reset, while the number of steps is A*4^i + B*i + C.  (The frame before the
reset has the same regularity in its powers of short words, e.g. `(1 0)^i` and `(1 X)^i`; it is printed with a
power code but not used.)

So for an epoch whose track is too long to simulate, this script simulates the same epoch with tracks Z0, Z0+3, ...,
Z0+3(K-1) (Z0 = Z mod 3 plus a few 3s, short enough to run in seconds with toksim), fits these laws on the
first three points, checks them on the others, and evaluates them at the real track length.  This is an
extrapolation, not a proof (its level is "heuristic"); `check` compares it with the plain token simulation where that
is feasible.

usage (from the repository root):
  python3 holdouts/1RB0RC_1LC0RE_0LD0LB_1RA1LE_1LB1RF_---0RD/py/epochs.py run EPOCHS [twin]
      start from the frame after the reset at step 22,706,655 (twin: 22,706,588) and extrapolate EPOCHS epochs
  python3 .../epochs.py check [twin]
      extrapolate the epochs whose ends the plain simulation reaches and compare
"""
import functools
import os
import subprocess
import sys
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.join(HERE, "..", "c", "toksim.c")
EXE = "/tmp/toksim_145349"


def exe():
    if not os.path.exists(EXE) or os.path.getmtime(EXE) < os.path.getmtime(SRC):
        subprocess.check_call(["gcc", "-O2", "-o", EXE, SRC])
    return EXE


@functools.lru_cache(maxsize=None)
def epoch(L, R, twin):
    """Run toksim from L | R to the end of the next reset."""
    args = [exe()] + (["twin"] if twin else []) + ["epoch", L or "e", R or "e"]
    out = subprocess.run(args, capture_output=True, text=True, check=True).stdout.split()
    assert out[0] == "epoch", out
    w = lambda s: "" if s == "e" else s
    return dict(steps=int(out[1]), ovs=int(out[2]), Lb=w(out[3]), Rb=w(out[4]), La=w(out[5]), Ra=w(out[6]),
                rsteps=int(out[7]))


def rle(s):
    out = []
    for c in s:
        if out and out[-1][0] == c:
            out[-1][1] += 1
        else:
            out.append([c, 1])
    return out


def unrle(r):
    return "".join(c * n for c, n in r)


def track(R):
    """(start, length) of the longest run of 0s in R."""
    best, i = (0, 0), 0
    while i < len(R):
        if R[i] == "0":
            j = i
            while j < len(R) and R[j] == "0":
                j += 1
            if j - i > best[1]:
                best = (i, j - i)
            i = j
        else:
            i += 1
    return best


def fit_affine(xs, ys):
    a = Fraction(ys[1] - ys[0], xs[1] - xs[0])
    b = ys[0] - a * xs[0]
    return lambda x: a * x + b


def fit_exp(xs, ys, base):
    """y = A base^x + B x + C through three points."""
    m = [[Fraction(base) ** x, Fraction(x), Fraction(1)] for x in xs[:3]]
    v = [Fraction(y) for y in ys[:3]]
    # Cramer
    def det(a):
        return (a[0][0] * (a[1][1] * a[2][2] - a[1][2] * a[2][1]) - a[0][1] * (a[1][0] * a[2][2] - a[1][2] * a[2][0])
                + a[0][2] * (a[1][0] * a[2][1] - a[1][1] * a[2][0]))
    d = det(m)
    coef = []
    for k in range(3):
        mk = [row[:] for row in m]
        for r in range(3):
            mk[r][k] = v[r]
        coef.append(det(mk) / d)
    A, B, C = coef
    return lambda x: A * Fraction(base) ** x + B * x + C, (A, B, C)


def extrapolate(L, R, twin, K=5, lo=12, top=27):
    """The epoch from L | R, by shortened tracks. Returns a dict like that of `epoch`, or raises ValueError."""
    s, Z = track(R)
    Z0 = Z % 3
    while Z0 < lo:
        Z0 += 3
    if Z0 + 3 * (K - 1) > top:
        Z0 = max(Z0 - 3 * (Z0 + 3 * (K - 1) - top) // 3, 3)
    if Z0 + 3 * (K - 1) >= Z:
        return epoch(L, R, twin)        # short enough: run it
    xs, runs = list(range(K)), []
    for k in xs:
        runs.append(epoch(L, R[:s] + "0" * (Z0 + 3 * k) + R[s + Z:], twin))
    target = Fraction(Z - Z0, 3)
    res = {"Lb": None, "Rb": None, "Z": Z, "Z0": Z0}
    for key in ("La", "Ra"):
        codes = [rle(e[key]) for e in runs]
        if any([c for c, _ in r] != [c for c, _ in codes[0]] for r in codes):
            raise ValueError(f"{key}: the run structure changes with the track length")
        out = []
        for j in range(len(codes[0])):
            f = fit_affine(xs, [r[j][1] for r in codes])
            if any(f(x) != r[j][1] for x, r in zip(xs, codes)):
                raise ValueError(f"{key}: run {j} is not affine in the track length")
            v = f(target)
            if v.denominator != 1 or v < 1:
                raise ValueError(f"{key}: run {j} extrapolates to {v}")
            out.append([codes[0][j][0], int(v)])
        res[key] = unrle(out)
    for key in ("ovs", "rsteps"):
        f = fit_affine(xs, [e[key] for e in runs])
        if any(f(x) != e[key] for x, e in zip(xs, runs)):
            raise ValueError(f"{key} not affine")
        res[key] = int(f(target))
    f, coef = fit_exp(xs, [e["steps"] for e in runs], 4)
    if any(f(x) != e["steps"] for x, e in zip(xs, runs)):
        raise ValueError("steps not of the form A 4^i + B i + C: " + str(coef))
    v = f(target)
    if v.denominator != 1:
        raise ValueError("steps extrapolate to a fraction")
    res["steps"] = int(v)
    res["coef"] = coef
    return res


START = {False: (22706655, "", "01001100110011111100111" + "0" * 27 + "100010"),
         True: (22706588, "", "01001100110011111100111" + "0" * 27 + "10000")}


def show(L, R):
    def c(s):
        return " ".join(f"{ch}^{n}" if n > 3 else " ".join(ch * n) for ch, n in rle(s)) if s else "e"
    return c(L) + " | " + c(R)


# (points, shortest track, longest track): the longest tracks cost about 4^(track/3) machine steps to simulate
ATTEMPTS = [(5, 12, 27), (4, 18, 27), (3, 21, 27)]


def run(n, twin):
    t, L, R = START[twin]
    print(f"epoch start at step {t}: {show(L, R)}")
    for k in range(n):
        e, why = None, []
        for K, lo, top in ATTEMPTS:
            try:
                e = extrapolate(L, R, twin, K=K, lo=lo, top=top)
                break
            except ValueError as err:
                why.append(f"tracks from {lo}, {K} points: {err}")
        if e is None:
            print("extrapolation failed:", "; ".join(why))
            return
        t += e["steps"]
        how = (f"extrapolated from {K} shortened tracks 0^{e['Z0']}, 0^{e['Z0'] + 3}, ...; "
               + ("laws checked on the extra points" if K > 3 else "only 3 points: the laws are fitted, not checked")
               if "Z0" in e else "simulated")
        print(f"epoch {k + 1}: track 0^{track(R)[1]}, {e['ovs']} overflows, {e['steps']} steps ({how})")
        print(f"   next epoch starts at step {t} (~2^{t.bit_length() - 1}): {show(e['La'], e['Ra'])}")
        sys.stdout.flush()
        L, R = e["La"], e["Ra"]


def check(twin):
    t, L, R = START[twin]
    e1 = extrapolate(L, R, twin, K=4, lo=12, top=21)   # tracks 12..21 for the track 0^27 of this epoch
    e2 = epoch(L, R, twin)
    same = all(e1[k] == e2[k] for k in ("steps", "ovs", "La", "Ra", "rsteps"))
    print("epoch from step", t, "extrapolated vs simulated:", "agree" if same else "DIFFER")
    if not same:
        print(e1)
        print(e2)


if __name__ == "__main__":
    a = sys.argv[1:]
    tw = "twin" in a
    if a[:1] == ["run"] and len(a) >= 2:
        run(int(a[1]), tw)
    elif a[:1] == ["check"]:
        check(tw)
    else:
        sys.exit(__doc__)
