"""Node search with exact linear counts inside a round, using rlepds tail summaries where the head enters the
unknown tail.  Experimental: it settles no machine.  See README.md, "Tail summaries from rlepds".

usage: python3 run_tail.py --rlepds PATH [--k0 42] [--cap 400] [--sumk 2] [--maxnodes N] [--check N] [--nodes]

The start is the round point `0^inf 01 (011)^k 0101 A> ANY` of 1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---.
- A node is a configuration whose head faces the bare unknown tail.  Its big counts are lower bounds, kept exact
  below --cap.  Between two nodes every count is an exact linear form, and sweeps are accelerated by loop rules.
- At a node, the literal cells next to the head are the left context.  `rlepds ... enter=Qh lctx=CELLS` lists every
  way the head can leave that context to the left, for every tail; the search goes on from each of them.
- When the head faces a zero-run of unknown length in front of the unknown tail, the unknown part is forgotten.
"""
import re
import subprocess
import sys
import search
from search import Prover, subsumed, nstr
from engine import K, Halt, canon, cfg_str, norm_side, subst_cfg

M = '1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---'
SUMARGS = "2 1 9 9 3 3 3 1".split()      # K P E1 T1 M1 E2 T2 M2 of rlepds; --sumk changes K


class TailProver(Prover):
    def __init__(self, machine, rlepds, **kw):
        super().__init__(machine, **kw)
        self.rlepds = rlepds
        self.sums = {}
        self.stats['tailcalls'] = 0
        self.ctxmax = 30      # cells of left context given to a tail summary
        self.ctxrun = 12      # a repeat longer than this is not put into the context

    def summary(self, q, h, ctx=""):
        """Every way out to the left from state q on a tail cell h, with any tape to the right of it and the cells
        ctx (farthest first) just left of it: list of (state, items).  The head ends on the cell left of ctx."""
        key = (q, h, ctx)
        if key not in self.sums:
            cmd = [self.rlepds, self.eng.m] + SUMARGS + [f"enter={'ABCDEF'[q]}{h}", "limit=5000000"]
            if ctx:
                cmd.append("lctx=" + ctx)
            out = subprocess.run(cmd, capture_output=True, text=True).stdout
            res = re.search(r"^RESULT .* (NONHALT|HALTREACH|LIMIT) ", out, re.M).group(1)
            exits = []
            for ln in out.splitlines():
                mm = re.match(r"\s+exit (\w) \|(.*) ANY$", ln)
                if mm:
                    exits.append((ord(mm.group(1)) - 65, self.read_items(mm.group(2))))
            self.sums[key] = (res, exits)
        return self.sums[key]

    @staticmethod
    def read_items(text):
        """rlepds's abstract side as a list of (word, kind, n, md): word repeated exactly n times ('eq') or
        n + md*j times ('ge').  A repeated digit whose zero-run is itself only a class cannot be written with one
        count; the list is cut there (what follows is ANY, which is weaker and so still correct)."""
        def cls(t):
            b = re.fullmatch(r">=(\d+)%(\d+)=(\d+)", t)
            if not b:
                return ('eq', int(t), 0)
            lo, md, r = int(b.group(1)), int(b.group(2)), int(b.group(3))
            return ('ge', lo + (r - lo) % md, md)
        items = []
        for pat, pc, sym, sc in re.findall(r"\[([^\]]*)\]\^(\S+)|([01])\^(\S+)", text):
            if sym:
                items.append(((int(sym),),) + cls(sc))
                continue
            runs = [(int(x), cls(y)) for x, y in re.findall(r"([01])\^(\S+)", pat)]
            if all(k[0] == 'eq' for _, k in runs):
                items.append((tuple(b for b, k in runs for _ in range(k[1])),) + cls(pc))
            else:
                # at least one copy: its runs one by one, then ANY
                items.extend(((b,),) + k for b, k in runs)
                break
        return items

    def advance(self, c):
        q, f, L, R = c
        if f == 'R':
            R = norm_side(R)
            if not R[0] and R[1] == 'A':
                return self.tail(c)
            if R[0] and not any(R[0][0][0]) and R[0][0][1][1] and R[1] == 'A':
                # facing a zero-run of unknown length before the unknown tail: keep its known part, forget the rest
                self.stats['forget'] = self.stats.get('forget', 0) + 1
                n = R[0][0][1][0]
                return [(canon((q, f, L, ((((0,), K(n)),) if n else (), 'A'))), ())]
        return super().advance(c)

    def advance_first(self, c):
        if c[1] == 'R' and not norm_side(c[3])[0] and c[3][1] == 'A':
            return self.tail(c)
        return super().advance_first(c)

    def is_checkpoint(self, c):
        """Nodes are made only where the head enters the unknown tail."""
        return c[1] == 'R' and not norm_side(c[3])[0] and c[3][1] == 'A'

    def context(self, L):
        """Split the left side into its literal cells next to the head (nearest first, at most ctxmax) and the rest."""
        items, term = norm_side(L)
        cells = []
        n = 0
        while n < len(items):
            w, e = items[n]
            if e[1] or e[0] * len(w) > self.ctxrun or len(cells) + e[0] * len(w) > self.ctxmax:
                break
            cells.extend(w * e[0])
            n += 1
        return cells, (items[n:], term)

    def tail(self, c):
        q, f, L, R = c
        self.stats['tailcalls'] += 1
        cells, rest = self.context(L)
        ctx = "".join(map(str, reversed(cells)))
        outs = []
        for h in (0, 1):
            res, exits = self.summary(q, h, ctx)
            if res != 'NONHALT':
                raise Halt(f"tail summary {'ABCDEF'[q]}{h} lctx={ctx}: {res}   at {cfg_str(c)}")
            for q2, items in exits:
                it = []
                for b, kind, n, md in items:
                    if kind == 'eq':
                        it.append((b, K(n)))
                    else:
                        it.append((b, (n, ((self.eng.fresh(), md),))))
                outs.append((canon((q2, 'L', rest, (tuple(it), 'A'))), ()))
        return outs

    def apply_loop(self, c, P, d):
        """As in search.Prover, and when a count with a variable is below the rule's minimum, split that variable
        into its small values (one plain move each) and the rest (the rule applies)."""
        r = super().apply_loop(c, P, d)
        if r is not None:
            return r
        rule = self.rules.get((self.lshape(P), d))
        if rule is None:
            return None
        for e, mm in zip(self.counts(c), rule.m):
            if mm is not None and e[0] < mm and e[1]:
                v, a = e[1][0]
                t = -(-(mm - e[0]) // a)
                outs = []
                for r0 in range(t):
                    x = canon(subst_cfg(c, v, K(r0)))
                    outs.extend((y, ((v, K(r0)),) + sb) for y, sb in self.advance(x))
                y = (t, ((self.eng.fresh(), 1),))
                x = subst_cfg(c, v, y)
                rr = self.apply_loop(x, P, d)
                if rr is None:
                    rr = self.advance(x)
                outs.extend((z, ((v, y),) + sb) for z, sb in rr)
                self.stats['splits'] = self.stats.get('splits', 0) + 1
                return outs
        return None

    # ------------------------------------------------------------------ sampling check of the summaries used
    def check_summaries(self, n, seed=1, maxsteps=20000):
        """Run the real machine from every (state, cell, context) summary used so far on n random tails each, and
        check that every way out to the left is one of the summary's exits.  Returns (runs that came out, misses)."""
        import random
        rnd = random.Random(seed)
        T = self.eng.T
        out = 0
        bad = []
        for (q0, h, ctx), (res, exits) in sorted(self.sums.items()):
            for _ in range(n):
                p1 = rnd.choice([0.05, 0.2, 0.5, 0.8, 0.95])
                tape = [int(x) for x in ctx] + [h]
                pos, q = len(ctx), q0
                for _ in range(maxsteps):
                    if pos < 0:
                        break
                    while pos >= len(tape):
                        tape.append(1 if rnd.random() < p1 else 0)
                    t = T[(q, tape[pos])]
                    if t is None:
                        bad.append(("halt", q0, h, ctx))
                        break
                    tape[pos] = t[0]
                    pos += 1 if t[1] == 'R' else -1
                    q = t[2]
                if pos >= 0:
                    continue
                out += 1
                if not any(q == q2 and self.covers(items, tape) for q2, items in exits):
                    bad.append(("exit", 'ABCDEF'[q0], h, ctx, 'ABCDEF'[q], "".join(map(str, tape[:24]))))
        return out, bad

    @staticmethod
    def covers(items, tape):
        """Does the tape (a prefix; anything may follow) start with these runs?  A run with a lower bound and a
        residue may be followed by more of the same symbol only if the next item or ANY allows it."""
        def rec(i, p):
            if i == len(items):
                return True
            w, kind, n, md = items[i]
            m = 0
            while tuple(tape[p + m * len(w):p + (m + 1) * len(w)]) == w:
                m += 1
            if kind == 'eq':
                return m >= n and rec(i + 1, p + n * len(w))
            return any(rec(i + 1, p + x * len(w)) for x in range(n, m + 1, md))
        return rec(0, 0)


if __name__ == "__main__":
    import argparse
    import time
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--k0", type=int, default=42, help="the round point is (011)^k with k >= k0")
    ap.add_argument("--cap", type=int, default=400, help="lower bounds are exact below this value")
    ap.add_argument("--sumk", type=int, default=2, help="runs of the tail that a summary remembers")
    ap.add_argument("--sumargs", default="", help="all rlepds parameters and options of a summary, in one string")
    ap.add_argument("--maxnodes", type=int, default=6000)
    ap.add_argument("--rlepds", default="rlepds")
    ap.add_argument("--check", type=int, default=0, help="random tails per summary for the sampling check")
    ap.add_argument("--nodes", action="store_true", help="print every node with its parent")
    a = ap.parse_args()
    SUMARGS[0] = str(a.sumk)
    if a.sumargs:
        SUMARGS[:] = a.sumargs.split()
    search.TS[0] = 8
    search.LEVELS[:] = list(range(8, a.cap))
    P = TailProver(M, a.rlepds, T=a.cap, keep=64, maxdepth=20000, maxnodes=a.maxnodes, verbose=True)
    L = (((1, 0), K(1)), ((1, 0), K(1)), ((1, 1, 0), K(a.k0)), ((1, 0), K(1)))
    c = canon((0, 'R', (L, 'B'), ((), 'A')))
    print("round point", cfg_str(c), " (the count is generalised to a lower bound)")
    t0 = time.time()
    r = P.attempt(c)
    print(r[0], r[1] if r[0] != 'ok' else f"{len(r[1])} nodes", f"{time.time() - t0:.0f}s", P.stats,
          f"summaries {len(P.sums)}")
    if r[0] == 'halt':
        for x in r[3][:40]:
            print("   <-", x[:200])
    if a.nodes:
        for i, (N, p) in enumerate(zip(P.nodes, P.parent)):
            print(i, p, nstr(N)[:200])
    if a.check:
        out, bad = P.check_summaries(a.check)
        print(f"summary check: {out} sampled excursions came out, {len(bad)} not covered")
        for b in bad[:10]:
            print("   MISS", b)
