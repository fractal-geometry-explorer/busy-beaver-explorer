"""One engine for the Lean-proved finite-variable maps of the open BB(6) holdouts.

Each map lives in `maps/<slug>.py` and defines

    MACHINE  the machine in standard text format (with ---)
    LEAN     where the map and its halts_iff theorem are, e.g. "lean/Macro.lean: next, halts_iff"
    VARS     names of the state components, e.g. ("k", "u", "v")
    START    the start state, a tuple (tags are str/bool, numbers are int)
    HALT     one line: the halting case, in words
    KIND     a short family tag (see README.md)
    step(s)  -> (s2, label); s2 is None when s is the halting case. label is a short str naming the branch taken.
             raise Stuck(msg) if s is outside what the Lean theorem covers (the run then stops and says so).
    margin(s) (optional) -> int: the distance to the halting case in bits (bit length of how far the deciding
             quantity is from its halting value). The engine records the closest approach as
             closeness = (bits of the largest number in the state) - margin, maximised over the run after step 1000:
             a closeness of c means the halting test missed by about 2^-c of the numbers' size.
    accel(s)  (optional) -> (s2, n, label) doing n >= 1 exact steps at once (s2 None = halted at the n-th);
             used instead of step when present.
    BOUND    (optional) the previous best run, a str for the report.

Numbers are Python ints converted to gmpy2.mpz by the engine when gmpy2 is available (same semantics).

usage:
    python3 tools/sweep/engine.py list
    python3 tools/sweep/engine.py run SLUG [--seconds S (total over resumes)] [--steps N] [--ckpt DIR] [--every SEC]
    python3 tools/sweep/engine.py orbit SLUG N        # print the first N states with labels
"""
import importlib
import json
import os
import sys
import time

try:
    import gmpy2
    from gmpy2 import mpz
except ImportError:  # pragma: no cover
    gmpy2 = None
    mpz = int

sys.set_int_max_str_digits(0)
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)


from maps._common import Stuck  # noqa: E402


def load(slug):
    m = importlib.import_module("maps." + slug)
    m.SLUG = slug
    return m


def slugs():
    out = []
    for f in sorted(os.listdir(os.path.join(HERE, "maps"))):
        if f.endswith(".py") and not f.startswith("_"):
            out.append(f[:-3])
    return out


def to_mpz(s):
    return tuple(mpz(x) if isinstance(x, int) and not isinstance(x, bool) else x for x in s)


def enc(s):
    return [("i", format(int(x), "x")) if (isinstance(x, int) or type(x).__name__ == "mpz") and not isinstance(x, bool)
            else ("t", x) for x in s]


def dec(v):
    out = []
    for k, x in v:
        out.append(mpz(int(x, 16)) if k == "i" else (tuple(x) if isinstance(x, list) else x))
    return tuple(out)


def bits(s):
    b = 0
    for x in s:
        if (isinstance(x, int) or type(x).__name__ == "mpz") and not isinstance(x, bool):
            b = max(b, int(x).bit_length() if not gmpy2 else gmpy2.bit_length(x))
    return b


def fmtn(n):
    n = int(n)
    return str(n) if n < 10**15 else f"~1e{len(str(n)) - 1}"


def run(slug, seconds=None, steps=None, ckpt=None, every=60.0, quiet=False):
    m = load(slug)
    path = os.path.join(ckpt, slug + ".json") if ckpt else None
    st = {"slug": slug, "machine": m.MACHINE, "n": 0, "state": enc(m.START), "labels": {}, "closest": None,
          "closest_at": None, "result": "running", "seconds": 0.0, "max_bits": 0}
    if path and os.path.exists(path):
        with open(path) as f:
            st = json.load(f)
        if st["result"] != "running" or (seconds is not None and st["seconds"] >= seconds):
            return st
    s = dec(st["state"]) if gmpy2 else tuple(int(x, 16) if k == "i" else x for k, x in st["state"])
    n = st["n"]
    labels = st["labels"]
    mm, mmat = st["closest"], st["closest_at"]
    hasmargin = hasattr(m, "margin")
    acc = getattr(m, "accel", None)
    t0 = time.time()
    tlast = t0
    base_sec = st["seconds"]
    result = "running"

    def save():
        st.update(n=n, state=enc(s), labels=labels, closest=mm, closest_at=mmat, result=result,
                  seconds=base_sec + time.time() - t0, max_bits=bits(s))
        if path:
            tmp = path + ".tmp"
            with open(tmp, "w") as f:
                json.dump(st, f)
            os.replace(tmp, path)

    chk = 0
    while True:
        try:
            if acc:
                s2, k, lab = acc(s)
                k = int(k)
            else:
                s2, lab = m.step(s)
                k = 1
        except Stuck as e:
            result = "stuck: " + str(e)
            break
        n += k
        labels[lab] = labels.get(lab, 0) + k
        if s2 is None:
            result = "HALT"
            break
        s = s2
        if hasmargin and n > 1000:
            g = m.margin(s)
            if g is not None:
                g = bits(s) - g  # closeness: bits of the state minus bits of the distance to halting
                if mm is None or g > mm:
                    mm, mmat = int(g), n
        chk += 1
        if chk >= 64:
            chk = 0
            now = time.time()
            if steps is not None and n >= steps:
                break
            if seconds is not None and base_sec + now - t0 >= seconds:
                break
            if now - tlast >= every:
                tlast = now
                save()
                if not quiet:
                    print(f"{slug}: n={fmtn(n)} bits={bits(s)} closest={mm}@{mmat} {base_sec + now - t0:.0f}s", flush=True)
        elif steps is not None and n >= steps:
            break
    save()
    if not quiet:
        print(f"{slug}: {result} n={fmtn(n)} bits={bits(s)} closest={mm}@{mmat}", flush=True)
    return st


def orbit(slug, N):
    m = load(slug)
    s = to_mpz(m.START)
    for i in range(N):
        s2, lab = m.step(s)
        print(i, tuple(int(x) if type(x).__name__ == "mpz" else x for x in s), lab)
        if s2 is None:
            print("HALT")
            return
        s = s2


def main(a):
    if not a or a[0] == "list":
        for sl in slugs():
            m = load(sl)
            print(sl, m.MACHINE, m.KIND, getattr(m, "BOUND", ""), sep="\t")
        return
    if a[0] == "run":
        kw = {}
        it = iter(a[2:])
        for x in it:
            if x == "--seconds":
                kw["seconds"] = float(next(it))
            elif x == "--steps":
                kw["steps"] = int(float(next(it)))
            elif x == "--ckpt":
                kw["ckpt"] = next(it)
            elif x == "--every":
                kw["every"] = float(next(it))
        run(a[1], **kw)
    elif a[0] == "orbit":
        orbit(a[1], int(a[2]))


if __name__ == "__main__":
    main(sys.argv[1:])
