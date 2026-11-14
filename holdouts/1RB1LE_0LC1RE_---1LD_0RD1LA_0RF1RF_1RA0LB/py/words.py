"""Words of pairs and one right-end visit of the machine on them.

A *visit* is the head in A on the blank cell right of the tape.  The tape left of the head is read in pairs of cells
from the head leftwards: X = `0 1`, Y = `1 1` (Z = `1 0` and O = `0 0` only occur at the left edge).  A word is also
written as *digits*: the lengths of the runs of Y between the X's, so `2 1 4 4` is `Y Y X Y X Y Y Y Y X Y Y Y Y`.

`visit(w, bnd)` runs the machine from the visit with word `w` (blank to the left of the word) to the next visit and
returns `(new word, steps, info)`; `new word` is None when the machine halts.  `bnd` is a cell boundary (a negative
cell position, the head is at 0): `info["sig"]` lists the crossings of it (`<C` the head goes left across it and is
then in C, `>E` it comes back and is then in E), `info["times"]` the step counts at the crossings and
`info["left"]` the number of steps made left of it.

The run is done in C (`../c/cvisit.c`, compiled into a temporary directory) when a compiler is there, else in Python;
`python3 words.py` checks one against the other.
"""
import ctypes, os, re, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
M = "1RB1LE_0LC1RE_---1LD_0RD1LA_0RF1RF_1RA0LB"
TABLE = {}
for _s, _row in enumerate(M.split("_")):
    for _r in range(2):
        _q = _row[3 * _r:3 * _r + 3]
        TABLE[_s, _r] = None if _q[0] == "-" else (int(_q[0]), 1 if _q[1] == "R" else -1, ord(_q[2]) - 65)
CELLS = {"X": (0, 1), "Y": (1, 1), "Z": (1, 0), "O": (0, 0)}
NAME = {(0, 1): "X", (1, 1): "Y", (1, 0): "Z", (0, 0): "O"}


def d2w(digits):
    return "X".join("Y" * d for d in digits)


def w2d(w):
    return [len(x) for x in w.split("X")]


def fmt(w):
    """digits, with 4^n for n blocks `4` and (0 3)^n"""
    d = " ".join(map(str, w2d(w))) + " "
    d = re.sub(r"((?:4 ){3,})", lambda m: "4^%d " % (len(m.group(1)) // 2), d)
    d = re.sub(r"((?:0 3 ){3,})", lambda m: "(0 3)^%d " % (len(m.group(1)) // 4), d)
    return d.strip()


def visit_py(w, bnd=None, maxsteps=10 ** 9):
    left = []                      # left[i] = cell -(i+1)
    for ch in w:
        a, b = CELLS[ch]
        left.append(b); left.append(a)
    right = {}
    p = s = n = nleft = 0
    maxw = -1
    sig, times = [], []
    while True:
        if p >= 0:
            r = right.get(p, 0)
        else:
            i = -p - 1
            if i >= len(left):
                left.extend([0] * (i - len(left) + 16))
            r = left[i]
        tr = TABLE[s, r]
        if tr is None:
            return None, n, {"halt": "ABCDEF"[s], "pos": p, "edge": -2 * len(w), "sig": "".join(sig),
                             "times": times, "left": nleft}
        if p >= 0:
            right[p] = tr[0]
        else:
            left[-p - 1] = tr[0]
        maxw = max(maxw, p)
        p2 = p + tr[1]
        if bnd is not None:
            if p >= bnd > p2:
                sig.append("<" + "ABCDEF"[tr[2]]); times.append(n + 1)
            if p < bnd <= p2:
                sig.append(">" + "ABCDEF"[tr[2]]); times.append(n + 1)
            if p < bnd:
                nleft += 1
        p, s, n = p2, tr[2], n + 1
        if s == 0 and p > 0 and p > maxw:
            break
        if n > maxsteps:
            raise RuntimeError("no visit in %d steps" % maxsteps)
    cells = [right.get(k, 0) for k in range(p - 1, -1, -1)] + left
    while cells and cells[-1] == 0:
        cells.pop()
    if len(cells) % 2:
        cells.append(0)
    out = "".join(NAME[cells[i + 1], cells[i]] for i in range(0, len(cells), 2))
    return out, n, {"sig": "".join(sig), "times": times, "left": nleft}


_lib = None


def _load():
    global _lib
    if _lib is not None:
        return _lib
    _lib = False
    try:
        d = os.path.join(tempfile.gettempdir(), "bb6-23376-%d" % os.getuid())
        os.makedirs(d, exist_ok=True)
        so = os.path.join(d, "cvisit.so")
        src = os.path.join(HERE, "..", "c", "cvisit.c")
        if not os.path.exists(so) or os.path.getmtime(so) < os.path.getmtime(src):
            subprocess.check_call(["gcc", "-O2", "-shared", "-fPIC", "-o", so, src])
        lib = ctypes.CDLL(so)
        lib.cvisit.argtypes = [ctypes.c_char_p, ctypes.c_long, ctypes.c_long, ctypes.c_char_p, ctypes.c_long,
                               ctypes.POINTER(ctypes.c_longlong), ctypes.c_char_p, ctypes.c_int]
        lib.ctimes.restype = ctypes.POINTER(ctypes.c_longlong)
        lib.setm(M.encode())
        _lib = lib
    except Exception:
        _lib = False
    return _lib


def visit(w, bnd=None, maxsteps=10 ** 11):
    lib = _load()
    if not lib:
        return visit_py(w, bnd, maxsteps)
    cap = len(w) + 8192
    out = ctypes.create_string_buffer(cap); sig = ctypes.create_string_buffer(256); info = (ctypes.c_longlong * 6)()
    rc = lib.cvisit(w.encode(), maxsteps, bnd or 0, out, cap, info, sig, 256)
    s = sig.value.decode()
    ct = lib.ctimes()
    times = [ct[i] for i in range(len(s) // 2)]
    if rc == 1:
        return None, info[0], {"halt": "ABCDEF"[info[2]], "pos": info[3], "edge": -2 * len(w), "sig": s,
                               "times": times, "left": info[4]}
    if rc:
        raise RuntimeError("cvisit: error %d" % rc)
    return out.value.decode(), info[0], {"sig": s, "times": times, "left": info[4]}


FIRST = ("XY", 9)       # the first visit: the word and the step count


def main():
    w, st = FIRST
    for v in range(2, 1500):
        a = visit_py(w, -10)
        b = visit(w, -10)
        assert a == b, v
        w, st = a[0], st + a[1]
    print("1,499 visits (%d steps): the C and the Python visit agree (word, steps, crossings)" % st)


if __name__ == "__main__":
    main()
