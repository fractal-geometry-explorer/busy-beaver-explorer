"""The rebuild map of the up/down two-counter machines, and a macro simulator built on it.

At the moment the down-counter V reaches 0 the tape is clean:

    0^inf  F  U  G  S>  H  (P0)^n  1  0^inf

F is the counter's top word (the sentinel; its form is fixed per machine, see FORMS), U the up-counter's L digits,
G the gap, H the header, (P0)^n the n digits of V, all 0, and a single 1 after them.  The up-counter together with
its top word is one number N (`value`).  This is the macro state (H, n, N).

`rebuild` writes that tape and runs the machine (the tick runs of the sub-phases jumped with the proved tick rule,
everything else simulated cell by cell, as in counters.py) until the next clean tick configuration

    0^inf  F'  U'  G  S>  H'  V'  1  0^inf

and returns (H', n', N', V').  From there the ticks (U+1, V-1, proved for every carry and borrow) run V' times
without leaving the clean family (top-word overflows are ordinary ticks), so the next macro state is
(H', n', N' + V') and the steps it takes are a closed formula in N' and V' (`phase_cost`).

usage: python3 rebuild.py MACHINE run [REBUILDS] [SECONDS]      the macro run from blank tape
       python3 rebuild.py MACHINE validate [SECONDS]            compare with counters.py's run, event by event
       python3 rebuild.py MACHINE one H n N                     one rebuild (N in any Python integer syntax)
"""
import os, sys, time, math, ast
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from counters import make, sum_tz, MACHINES, learn_headers

# The top word of the up-counter at clean configurations: '1' is a single 1 (value 2^L), '1000x' the variant
# where the leading 1 sits four cells further out and the cell x is the top bit (value 2^(L+1) + x 2^L),
# '' a counter whose digit 1 carries its own leading 1 (D1 = 100; value U).
FORMS = {
    "1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LB": ["1"],
    "1RB1LC_0RC0RB_1LD0LA_1LE---_1LF1RA_1LA1LC": ["1", "10000", "10001"],
    "1RB1LD_1RC0RB_1LA1RC_1LE0LA_1LF---_1LC---": ["1"],
    "1RB1LE_1RC0RB_1LD1RC_1LA1LE_1LF0LA_1LC---": ["1", "10000", "10001"],
    "1RB1LE_1RC0RB_1RD1LF_1LA0LC_1LD0LA_---0RE": [""],
}
HEADERS = {M: ["0110101", "0110111"] for M in FORMS}
HEADERS["1RB1LE_1RC0RB_1RD1LF_1LA0LC_1LD0LA_---0RE"] = ["01101010101", "01101011101"]

_hdr = {}
_failed = {}


class Rebuilder:
    def __init__(self, M, forms=None):
        self.M = M
        self.cfg = dict(MACHINES[M])
        self.S = self.cfg.get("S")
        self.W = self.cfg.get("W", 5); self.D0 = self.cfg.get("D0", "00000"); self.D1 = self.cfg.get("D1", "00001")
        self.G = self.cfg.get("G", "00"); self.P0 = "11"; self.P1 = "01"
        self.forms = forms if forms is not None else FORMS[M]
        c = make(M, log=lambda *a: None)
        for H in HEADERS[M]:
            key = (self.G, H)
            if (M, key) not in _hdr:
                assert c.learn(key), key
                _hdr[(M, key)] = c.headers[key]
        self.hdr = {H: _hdr[(M, (self.G, H))] for H in HEADERS[M]}
        # the tick that carries out of a top word 1000x with x = 1 (N + 1 a power of 2) is not quite an ordinary
        # tick: measure its cost against the formula once, for both parities of V and two lengths
        self.delta = 0
        if "10001" in self.forms:
            ds = set()
            for H in self.hdr:
                for L in (3, 6):
                    for vb in ("01", "1101"):
                        left = "10001" + self.D1 * L
                        c = self.setup(left + self.G + H + vb + "01011", len(left) + len(self.G))
                        while True:
                            c.step_to_S(10 ** 6); mt = c.match()
                            if mt and mt[0] == "tick": break
                        a0, b0, cu, cv = self.hdr[H]
                        ds.add(c.steps - (a0 if vb == "01" else b0) - cu * (L + 2))
            assert len(ds) == 1, ds
            self.delta = ds.pop()

    # numbers <-> top word + digits
    @staticmethod
    def family(form):
        return "1000" if form.startswith("1000") else form

    def value(self, form, L, U):
        if form == "1": return (1 << L) + U
        if form == "": return U
        if len(form) == 5 and form.startswith("1000"): return (1 << (L + 1)) + (int(form[4]) << L) + U
        raise ValueError(form)

    def encode(self, N, form):
        if form == "1":
            L = N.bit_length() - 1; U = N - (1 << L); top = "1"
        elif form == "":
            L = N.bit_length(); U = N; top = ""
        else:
            L = N.bit_length() - 2; top = "1000" + str((N >> L) & 1); U = N & ((1 << L) - 1)
        return top + "".join(self.D1 if (U >> j) & 1 else self.D0 for j in reversed(range(L)))

    def classify(self, c, lc, key, nb):
        """the form of a tick configuration if it is clean, else None"""
        L, U, q = lc
        if key[0] != self.G: return None
        left = "".join(str(c.get(i)) for i in range(c.lo, q)).lstrip("0")
        if left not in self.forms: return None
        r0 = c.pos + len(key[1]) + 2 * nb
        right = "".join(str(c.get(i)) for i in range(r0, c.hi + 1)).rstrip("0")
        return left if right == "1" else None

    def setup(self, tape, pos):
        c = make(self.M, log=lambda *a: None)
        for H in HEADERS[self.M]:
            c.headers[(self.G, H)] = self.hdr[H]
        for key, v in _hdr.items():
            if key[0] == self.M: c.headers[key[1]] = v
        c.failed = _failed.setdefault(self.M, set())
        sz = 1 << max(16, (3 * len(tape)).bit_length())
        c.c = bytearray(sz); c.off = sz // 3
        c.c[c.off:c.off + len(tape)] = tape.encode().translate(bytes.maketrans(b"01", b"\x00\x01"))
        c.lo = 0; c.hi = len(tape) - 1; c.pos = pos; c.state = "ABCDEF".index(self.S); c.steps = 0
        return c

    def rebuild(self, H, n, N, form=None, maxd=10 ** 9, trace=None):
        """from the V=0 configuration (H, n, N): ('OK', steps, (H', n', N', V', form', L')) or ('HALT', steps) or
        ('STUCK', steps)"""
        form = self.family(self.forms[0]) if form is None else form
        left = self.encode(N, form)
        tape = left + self.G + H + self.P0 * n + "1"
        c = self.setup(tape, len(left) + len(self.G))
        subs = 0; cands = []
        while True:
            k = c.step_to_S(maxd)
            if c.halted: return ("HALT", c.steps, subs)
            if k >= maxd: return ("STUCK", c.steps, subs)
            mt = c.match()
            if mt is not None and mt[0] == "cand":
                # an unknown header (sub-phases of some machines use others): learn it as counters.py does
                cands.append((mt[2], c.get_r(300)))
                if len(cands) >= 48:
                    for G in set(g for g, _ in cands):
                        for Hc in learn_headers([x for g, x in cands if g == G]):
                            key = (G, Hc)
                            if key not in c.headers and key not in c.failed:
                                if c.learn(key): _hdr[(self.M, key)] = c.headers[key]
                                else: c.failed.add(key)
                    cands = []
                continue
            if mt is None or mt[0] != "tick": continue
            cands = []
            _, lc, key, V, nb = mt
            f = self.classify(c, lc, key, nb)
            if f is not None:
                L, U, q = lc
                return ("OK", c.steps, (key[1], nb, self.value(f, L, U), V, self.family(f), L), subs)
            subs += 1
            if trace: trace(c, lc, key, V, nb)
            c.jump(lc, key, V, nb)

    def phase_cost(self, H, N, V, form="1"):
        """steps of V ticks from a clean configuration with up-counter value N and down-counter V (all carries
        counted as trailing ones of N, all borrows as trailing zeros of V)"""
        a0, b0, cu, cv = _hdr[(self.M, (self.G, H))]
        k = V
        nbz = V // 2
        cost = a0 * k + cu * sum_tz(N + 1, N + k) + (b0 - a0 - cv) * nbz + cv * sum_tz(1, V)
        if form == "1000":
            cost += self.delta * max(0, (N + k).bit_length() - 1 - N.bit_length() + 1)   # powers of 2 in [N+1, N+k]
        return cost


def first_state(M, rb, secs=60):
    """run counters.py from blank tape to the first V=0 moment of a clean configuration: (H, n, N, form, steps)"""
    c = make(M, log=lambda *a: None)
    orig = c.jump; found = []

    class Done(Exception): pass

    def j(lc, key, V, nb):
        L, U, q = lc
        f = rb.classify(c, lc, key, nb)
        k = orig(lc, key, V, nb)
        if k == V and k > 0 and f is not None:
            found.append((key[1], nb, rb.value(f, L, U) + k, rb.family(f), c.steps)); raise Done
        return k
    c.jump = j
    try:
        c.run(1e400, max_direct=10 ** 10)
    except Done:
        return found[0]
    return None


def macro_run(M, rebuilds, secs, out=print):
    rb = Rebuilder(M)
    H, n, N, form, steps = first_state(M, rb)
    t0 = time.time()
    out(("start", H, n, N, form, steps))
    for it in range(rebuilds):
        r = rb.rebuild(H, n, N, form)
        if r[0] != "OK":
            out((r[0], it, steps + r[1], H, n, N)); return r[0], steps + r[1]
        steps += r[1]
        H2, n2, N2, V2, f2, L2 = r[2]
        steps += rb.phase_cost(H2, N2, V2, f2)
        H, n, N, form = H2, n2, N2 + V2, f2
        out((it, H, n, N, form, steps, r[1], r[3], N2, (1 << n2) - V2))
        if time.time() - t0 > secs: break
    return "max", steps


def validate(M, secs):
    """the V=0 events of counters.py's accelerated run (tested against tools/c/tmrun.c) against the macro run"""
    rb = Rebuilder(M)
    c = make(M, log=lambda *a: None)
    orig = c.jump; ev = []; t0 = time.time()

    class Done(Exception): pass

    def j(lc, key, V, nb):
        L, U, q = lc
        f = rb.classify(c, lc, key, nb)
        k = orig(lc, key, V, nb)
        if k == V and k > 0 and f is not None:
            ev.append((key[1], nb, rb.value(f, L, U) + k, c.steps))
        if time.time() - t0 > secs: raise Done
        return k
    c.jump = j
    try:
        c.run(1e400, max_direct=10 ** 10)
    except Done:
        pass
    mine = []
    macro_run(M, len(ev) + 1, 1e9, out=lambda x: mine.append(x))
    got = [(x[1], x[2], x[3], x[5]) for x in mine if x[0] not in ("HALT", "STUCK")]
    ok = all(a == b for a, b in zip(ev, got))
    print(f"{M}: {len(ev)} V=0 events of counters.py (last at ~10^{len(str(ev[-1][3])) - 1} steps) "
          f"{'all equal' if ok else 'DIFFER'} to the macro run")
    if not ok:
        for a, b in zip(ev, got):
            print(" ", a == b, a[:2], a[3] if a[3] < 10 ** 30 else "", "|", b[:2], b[3] if b[3] < 10 ** 30 else "")
    return ok


if __name__ == "__main__":
    M = sys.argv[1]; cmd = sys.argv[2]
    if cmd == "run":
        nreb = int(sys.argv[3]) if len(sys.argv) > 3 else 10 ** 9
        secs = float(sys.argv[4]) if len(sys.argv) > 4 else 600
        t0 = time.time()

        def show(x):
            if x[0] == "start":
                print(f"first V=0 at step {x[5]}: H={x[1]} n={x[2]} N={x[3]}", flush=True); return
            if x[0] in ("HALT", "STUCK"):
                print(f"{x[0]} in rebuild {x[1]} at step {x[2]}", flush=True); return
            it, H, n, N, form, steps, rs, subs, N2, d = x
            print(f"{it} H={H} n={n} bits(N)={N.bit_length()} log10(steps)={steps.bit_length() * math.log10(2):.1f} "
                  f"rebuild={rs} steps, {subs} sub-phases  t={time.time() - t0:.0f}s", flush=True)
        r = macro_run(M, nreb, secs, show)
        print(r[0], "after", f"~10^{r[1].bit_length() * math.log10(2):.1f}", "steps")
    elif cmd == "validate":
        sys.exit(0 if validate(M, float(sys.argv[3]) if len(sys.argv) > 3 else 60) else 1)
    elif cmd == "one":
        rb = Rebuilder(M)
        H, n, N = sys.argv[3], int(sys.argv[4]), ast.literal_eval(sys.argv[5])
        print(rb.rebuild(H, n, N))
