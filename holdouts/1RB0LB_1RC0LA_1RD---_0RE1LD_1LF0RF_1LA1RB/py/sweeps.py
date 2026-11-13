"""Shared tools for the six G01 machines whose tapes are a periodic background crossed by defects ("gliders").

Used by the py/ scripts of
  1RB0LA_0LC0RA_1LA1LD_1LC0LE_1RF0LF_0RB---   1RB---_0RC1RD_1LA0LA_1LE0RB_1LF1LE_1LC0LD
  1RB0LC_1RC1RA_0RD1LE_1RE1RF_1LC0RB_---1RD   1RB0LB_1RC0LA_1RD---_0RE1LD_1LF0RF_1LA1RB (this folder)
  1RB0LB_1RC1LD_1LD0RD_1LE0RC_1LF---_0LA1RF   1RB0LE_0RC---_1RD0LA_1RE0RA_0LF1LD_1LC1RF

* `snapshots(M, steps, state, side, every)`: the whole tape each time the head, in `state` (or any state: '*'),
  stands on the left (L) or right (R) end of the visited cells; from `c/snap.c` in this folder (compiled on demand).
* `defect_image(...)`: a picture with one row per such moment (one sweep of the head, or `every` of them) and a dark
  pixel wherever the tape differs from itself P cells further on, i.e. wherever the periodic background of period P
  is broken.  Long-lived defects ("gliders") are lines; their slope is their speed.
* `tokens(t, w)`: the tape read as runs of the background word w (`[n]`) and the literal cells between them.
* `record_clusters(M, steps, side)`: the times the visited part of the tape grows on `side`, grouped into clusters
  (a cluster = one event at that end).
* `excursions(M, steps, state, side, start)`: how far the head goes from that end between consecutive visits;
  the lengths show at which defect it turns back (`c/excursions.c`).
* `rules_lean(M, ns, rules, doc)`: a Lean file of rules proved by `bbtools.symtm.prove` (shift rules over the
  background words, `TM.cross_r` / `TM.cross_l`), checked by Lean's kernel.
"""
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
sys.path.insert(0, os.path.join(REPO, "tools", "py"))

SNAP_SRC = os.path.join(HERE, "..", "c", "snap.c")
SNAP_BIN = os.path.join(os.environ.get("TMPDIR", "/tmp"), "g01_snap")


def snap_bin():
    if not os.path.exists(SNAP_BIN) or os.path.getmtime(SNAP_BIN) < os.path.getmtime(SNAP_SRC):
        subprocess.run(["gcc", "-O2", "-o", SNAP_BIN, SNAP_SRC], check=True)
    return SNAP_BIN


def snapshots(m, steps, state, side, every=1, k=10 ** 9):
    """Yield (step, state, lo, hi, head, tape) with tape a string of 0/1 from lo to hi."""
    p = subprocess.Popen([snap_bin(), m, str(int(steps)), "at", state, side, str(k), str(every)],
                         stdout=subprocess.PIPE, text=True)
    for line in p.stdout:
        f = line.split()
        if len(f) < 6:
            if f and f[0] == "HALT":
                raise RuntimeError("halted: " + line)
            continue
        yield int(f[0]), f[1], int(f[2]), int(f[3]), int(f[4]), f[5]


def defect_image(m, steps, state, side, every, P, out, rows=1500, width=900):
    """Write a PNG: rows = snapshots, x = absolute cell (min-pooled to at most `width` columns), dark where
    t[x] != t[x+P].  Returns (cells, rows, last step)."""
    import numpy as np
    from PIL import Image
    data = []
    for k, s, lo, hi, h, t in snapshots(m, steps, state, side, every, rows):
        a = np.frombuffer(t.encode(), np.uint8) - 48
        d = np.zeros(len(a), bool)
        d[:-P] = a[:-P] != a[P:]
        data.append((lo, d, k))
    lo = min(r[0] for r in data)
    hi = max(r[0] + len(r[1]) for r in data)
    W, H = hi - lo, len(data)
    img = np.full((H, W), 255, np.uint8)
    for i, (a, d, k) in enumerate(data):
        img[i, a - lo:a - lo + len(d)] = np.where(d, 0, 225)
    f = max(1, -(-W // width))
    Wp = -(-W // f) * f
    pad = np.full((H, Wp), 255, np.uint8)
    pad[:, :W] = img
    small = pad.reshape(H, Wp // f, f).min(axis=2)
    Image.fromarray(small).save(out, optimize=True)
    return W, H, data[-1][2]


def tokens(t, w):
    out, i, n, lit = [], 0, 0, ""
    while i < len(t):
        if t.startswith(w, i):
            if lit:
                out.append(lit)
                lit = ""
            n += 1
            i += len(w)
            continue
        if n:
            out.append(f"[{n}]")
            n = 0
        lit += t[i]
        i += 1
    if n:
        out.append(f"[{n}]")
    if lit:
        out.append(lit)
    return out


def record_clusters(m, steps, side, gap=1000):
    """Times (first step of each cluster) when the visited cells grow on `side`, and the width then."""
    tm = os.path.join(os.environ.get("TMPDIR", "/tmp"), "g01_tmrun")
    src = os.path.join(REPO, "tools", "c", "tmrun.c")
    if not os.path.exists(tm):
        subprocess.run(["gcc", "-O2", "-o", tm, src], check=True)
    p = subprocess.Popen([tm, m, str(int(steps)), "records", "1000000000"], stdout=subprocess.PIPE, text=True)
    out, last = [], -10 ** 18
    for line in p.stdout:
        f = line.split()
        if f[0] in ("running", "halted"):
            break
        if f[1] != side:
            continue
        k = int(f[0])
        if k - last > gap:
            out.append((k, int(f[2])))
        last = k
    return out


def excursions(m, steps, state, side, start=0):
    """Yield (step, length) for each visit of the head, in `state`, to the `side` end of the tape after step
    `start`: length = how far the head went from that end since the previous visit (c/excursions.c)."""
    src = os.path.join(HERE, "..", "c", "excursions.c")
    exe = os.path.join(os.environ.get("TMPDIR", "/tmp"), "g01_excursions")
    if not os.path.exists(exe) or os.path.getmtime(exe) < os.path.getmtime(src):
        subprocess.run(["gcc", "-O2", "-o", exe, src], check=True)
    p = subprocess.Popen([exe, m, str(int(steps)), state, side, "1"], stdout=subprocess.PIPE, text=True)
    for line in p.stdout:
        f = dict(x.split("=") for x in line.split()[1:])
        k = int(line.split()[0])
        if k < start:
            continue
        yield k, (int(f["maxhead"]) - int(f["lo"])) if side == "L" else (int(f["hi"]) - int(f["minhead"]))


def rules_lean(m, ns, rules, doc):
    """rules: list of (name, docstring, start, end[, options]) for bbtools.symtm.prove (options: a dict of its keyword
    arguments, e.g. {"rotate": true}).  Returns the Lean file text."""
    from bbtools.symtm import prove, rules_file
    thms = []
    for r in rules:
        name, d, start, end = r[:4]
        opts = r[4] if len(r) > 4 else {}
        text, fin = prove(m, name, start, end, doc=d, **opts)
        thms.append(text)
    text = rules_file("Machine", ns, thms, doc)
    # one copy of a long word is a long `rfl` (60 steps for 1RB0LE_0RC---_...): raise Lean's recursion limit
    return text.replace("\nopen TM\n", "\nopen TM\n\nset_option maxRecDepth 10000\n", 1)
