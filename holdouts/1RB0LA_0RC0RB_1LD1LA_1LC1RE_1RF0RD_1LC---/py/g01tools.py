"""Small shared helpers for the G01 machines analysed in this folder and its siblings (they import this file by path).

* `events(M, start, N, state, side)`: run machine M from a tape written like 'A> 00 (10)^5 01' (blank elsewhere,
  head on the first cell after 'S>') for N steps with `../c/from.c`, yielding (steps, tape) each time the head, in
  `state`, is at the `side` ('L'/'R') end of the visited cells; the tape is the string from the leftmost to the
  rightmost 1 (or head) with the head's state letter written just before the cell it reads.  The last item is
  ('halted'|'running', steps).
* `show(t)`: that tape string run-length compressed into words, '(10)^5'.
* `Map`: the next event of given shapes (regular expressions on the tape string) after a start configuration.
The C program is compiled on first use into $BB_G01_BIN (default /tmp/bb_g01_bin)."""
import os, re, subprocess

HERE = os.path.dirname(os.path.abspath(__file__))
CDIR = os.path.join(HERE, "..", "c")
BIN = os.environ.get("BB_G01_BIN", "/tmp/bb_g01_bin")


def binary(name):
    exe = os.path.join(BIN, name)
    src = os.path.join(CDIR, name + ".c")
    if not os.path.exists(exe) or os.path.getmtime(exe) < os.path.getmtime(src):
        os.makedirs(BIN, exist_ok=True)
        subprocess.run(["gcc", "-O2", "-o", exe, src], check=True)
    return exe


def expand(s):
    o = ""
    for t in s.split():
        m = re.fullmatch(r"\(?([01]+)\)?\^(\d+)", t)
        o += m.group(1) * int(m.group(2)) if m else t
    return o


def events(M, start, N, st, side, K=10**9):
    l, r = start.split(">")
    S = l.strip()[-1]
    L, R = expand(l.strip()[:-1]), expand(r)
    p = subprocess.Popen([binary("from"), M, L + S + R, str(N), st, side, str(K)], stdout=subprocess.PIPE, text=True)
    try:
        for line in p.stdout:
            a, b = line.split()
            if a in ("halted", "running", "tape"):
                yield (a, int(b))
                return
            yield (int(a), b)
    finally:
        p.kill()
        p.wait()


def compress(s, minrep=2, maxw=8):
    res, i = [], 0
    while i < len(s):
        best = (1, s[i])
        for w in range(1, maxw + 1):
            u = s[i:i + w]
            if len(u) < w:
                break
            n = 1
            while s[i + n * w:i + (n + 1) * w] == u:
                n += 1
            if n >= minrep and (n - 1) * w > (best[0] - 1) * len(best[1]):
                best = (n, u)
        n, u = best
        if n > 1:
            res.append(f"({u})^{n}" if len(u) > 1 else f"{u}^{n}")
            i += n * len(u)
        else:
            res.append(u)
            i += 1
    out, lit = [], ""
    for r in res:
        if len(r) == 1:
            lit += r
        else:
            if lit:
                out.append(lit)
                lit = ""
            out.append(r)
    if lit:
        out.append(lit)
    return " ".join(out)


def show(t, minrep=2):
    i = next(j for j, c in enumerate(t) if c in "ABCDEF")
    return (compress(t[:i], minrep) + " " + t[i] + "> " + compress(t[i + 1:], minrep)).strip()


class Map:
    """forms: {name: (start template with %d fields, regex on the tape string)}; `nxt(name, *args)` is the first
    event (skipping the first `skip` steps) whose tape matches one of the forms: (steps, form, group lengths...)."""

    def __init__(self, M, st, side, forms, skip=0):
        self.M, self.st, self.side, self.skip = M, st, side, skip
        self.forms = {k: (t, re.compile(p)) for k, (t, p) in forms.items()}

    def nxt(self, name, *args, N=10**9):
        for k, t in events(self.M, self.forms[name][0] % args, N, self.st, self.side):
            if isinstance(t, int):
                return (k, t)
            if k <= self.skip:
                continue
            for nm, (_, p) in self.forms.items():
                mm = p.fullmatch(t)
                if mm:
                    return (k, nm) + tuple(len(g) for g in mm.groups())
        return None
