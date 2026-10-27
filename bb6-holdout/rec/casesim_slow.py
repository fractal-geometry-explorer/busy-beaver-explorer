"""Certified fast simulation: runs the machine using only the proven theorems (proofs.py) as macro steps.

Before each macro step the current configuration is checked to be exactly an instance of the theorem's start
pattern (same_config on the instantiated pattern), so every reported configuration and step count follows from
the proven theorems; a configuration no theorem covers stops the run with an error."""
import sys, json
from symtm import *
from symtm import _unroll_front, _unroll_back
import proofs

TH = {t["name"]: t for t in proofs.THEOREMS}
# the iterated bounces (induction in proofs.prove_iteration)
TH["BOUNCE^k"] = dict(start=("L 0 0", "E", "0 (10)^M 1 1 0 R"), end=("L (01)^k 0 0", "E", "0 (10)^m 1 1 0 (10)^k R"),
                      steps=lambda v: 6 * v["k"] * v["m"] + 6 * v["k"] ** 2 + 24 * v["k"])
TH["WALLBOUNCE^k"] = dict(start=("L 0 0", "E", "0 (10)^M 0 R"), end=("L (01)^k 0 0", "E", "0 (10)^m 0 R"),
                          steps=lambda v: 6 * v["k"] * v["m"] + 3 * v["k"] ** 2 + 9 * v["k"])

class Uncovered(Exception): pass

def inst(side, L, R, v):
    out = []
    for part in side.split(" | "):
        if part.strip() == "0^inf": out.append(Blank()); continue
        for t in tokens(part, **{k: Lin(x) for k, x in v.items()}):
            if t == Ctx("L"): out.extend(L)
            elif t == Ctx("R"): out.extend(R)
            else: out.append(t)
    return out

def apply(cfg, name, L, R, v):
    th = TH[name]
    s = th["start"]; e = th["end"]
    start = Config(inst(s[0], L, R, v), s[1], inst(s[2], L, R, v))
    if not same_config(start, cfg):
        raise Uncovered(f"{name} does not match {cfg}")
    st = th["steps"](v) if callable(th["steps"]) else th["steps"].subs(v)
    new = Config(inst(e[0], L, R, v), e[1], inst(e[2], L, R, v), cfg.steps + st)
    new.left, new.right = compact(new.left), compact(new.right)
    return new

def compact(seq):
    out = canon(seq)
    res = []
    for t in out:
        res.append(t)
        while len(res) >= 3 and all(isinstance(x, int) for x in res[-2:]) and isinstance(res[-3], Rep) and res[-3].word == (res[-2], res[-1]):
            r = res[-3]; res[-3:] = [Rep(r.word, r.n + 1)]
    fin = []; i = 0
    while i < len(res):
        if (i + 3 < len(res) and all(isinstance(res[x], int) for x in range(i, i + 4)) and res[i] == res[i + 2]
                and res[i + 1] == res[i + 3] and res[i] != res[i + 1]):
            w = (res[i], res[i + 1]); kk = 0
            while i + 1 < len(res) and isinstance(res[i], int) and isinstance(res[i + 1], int) and (res[i], res[i + 1]) == w:
                kk += 1; i += 2
            fin.append(Rep(w, Lin(kk)))
        else:
            fin.append(res[i]); i += 1
    return fin

def peek(seq, n, back=False):
    """First n cells of seq (or last n, in tape order), expanding repeats; Blank gives 0s. Returns cells, rest."""
    s = list(seq); cells = []
    for _ in range(n):
        if back:
            if not s: break
            if isinstance(s[-1], Blank): cells.insert(0, 0); continue
            _unroll_back(s); cells.insert(0, s.pop())
        else:
            if not s: break
            if isinstance(s[0], Blank): cells.append(0); continue
            _unroll_front(s); cells.append(s.pop(0))
    return cells, s

def pairs10(seq):
    """Count (10) pairs at the front; a final 1 followed by blank tape also counts as a pair."""
    k, rest = count_pairs(seq, (1, 0))
    c = canon(rest)
    if len(c) == 2 and c[0] == 1 and c[1] == Blank():
        return Lin(k.k + 1), [Blank()]
    return k, rest

def starts_with_blank(seq):
    return bool(seq) and isinstance(canon(seq)[0], Blank)

def ends_with_blank(seq):
    return bool(seq) and isinstance(canon(seq)[-1], Blank)


def gap_phase(cfg):
    """Head E on the last 0 of the active gap. Returns the configuration after the next macro step(s)."""
    lc, Lr = peek(cfg.left, 2, back=True)           # the gap's first two 0s
    assert lc == [0, 0], cfg
    r = list(cfg.right); c0, r = peek(r, 1); assert c0 == [0]
    M, after = pairs10(r); M = M.k
    nxt, _ = peek(after, 4)
    if starts_with_blank(after):
        kind = "blank"
    elif nxt[:3] == [1, 1, 0] or (nxt[:2] == [1, 1] and starts_with_blank(peek(after, 2)[1])):
        kind = "marker"
    elif nxt[:4] == [1, 1, 1, 0]:
        kind = "block"
    elif nxt[:1] == [0]:
        kind = "wall"
    else:
        raise Uncovered(f"gap phase: next cells {nxt} in {cfg}")
    if kind == "marker":
        k, m = M // 2, M % 2
        if k:
            _, R = peek(after, 3)
            cfg = apply(cfg, "BOUNCE^k", Lr, R, dict(M=M, k=k, m=m))
        lc, L3 = peek(cfg.left, 3, back=True); assert lc == [1, 0, 0], cfg
        _, R = peek(cfg.right, 4 if m == 0 else 6)
        return apply(cfg, "SWAP" if m == 0 else "MERGE", L3, R, {})
    if kind in ("wall", "blank"):
        if M:
            _, R = peek(after, 1)                       # the wall's extra 0 (or a blank cell)
            cfg = apply(cfg, "WALLBOUNCE^k", Lr, R, dict(M=M, k=M, m=0))
        lc, L3 = peek(cfg.left, 3, back=True); assert lc == [1, 0, 0], cfg
        _, r2 = peek(cfg.right, 2)                       # E's 0 and the wall's extra 0
        return meet(cfg, L3, r2)
    if kind == "block":
        _, rb = peek(after, 4)
        j, rest = pairs10(rb)
        return shift_target(cfg, "BLOCK", peek(cfg.left, 3, back=True)[1], rest, dict(m=M, j=j.k))

def meet(cfg, L3, r2):
    j, rest = pairs10(r2)
    if starts_with_blank(rest) and j.k == 0 and starts_with_blank(r2):
        return apply(cfg, "GAP->blankend", L3, [], {})
    return shift_target(cfg, "MEET", L3, rest, dict(j=j.k))

def shift_target(cfg, prefix, L3, rest, v):
    nxt, _ = peek(rest, 4)
    if starts_with_blank(rest):
        return apply(cfg, prefix + "->blank", L3, [], v)
    if nxt[:3] == [1, 1, 0] or (nxt[:2] == [1, 1] and starts_with_blank(peek(rest, 2)[1])):
        return apply(cfg, prefix + "->marker", L3, peek(rest, 3)[1], v)
    if nxt[:4] == [1, 1, 1, 0]:
        return apply(cfg, prefix + "->block", L3, peek(rest, 4)[1], v)
    if nxt[:2] == [0, 1]:                            # pattern (10)^j 0 1: the next wall
        return apply(cfg, prefix + "->wall", L3, peek(rest, 2)[1], v)
    raise Uncovered(f"{prefix} shift target {nxt} in {cfg}")

def packet_phase(cfg):
    """Head A on a packet (A> 1 1 ...) heading left."""
    try_lemma(cfg, use=("CARRY",))
    cfg.left, cfg.right = compact(cfg.left), compact(cfg.right)
    _, R2 = peek(cfg.right, 2)
    if ends_with_blank(cfg.left) and len(canon(cfg.left)) == 1:
        return apply(cfg, "PACKET->leftend", [], R2, {}), "round"
    tail, _ = peek(cfg.left, 7, back=True)
    def L(n): return peek(cfg.left, n, back=True)[1]
    if tail[-3:] == [0, 0, 0]:
        return apply(cfg, "PACKET->gap", L(3), R2, {}), None
    if tail[-3:] == [1, 0, 0]:
        return apply(cfg, "PACKET->wall", L(3), R2, {}), None
    if tail[-2:] == [1, 1]:
        raise Uncovered("packet reaches a block: the machine would halt")
    if tail[-1:] == [1]:                               # the first 1 of a marker
        before = L(1)
        if ends_with_blank(before) and len(canon(before)) == 1:
            return apply(cfg, "PACKET->leftend-marker", [], R2, {}), "round"
        if tail[-3:] == [1, 0, 1]:
            return apply(cfg, "PACKET->marker", L(3), R2, {}), "packet"
        if tail[-5:] == [1, 0, 0, 0, 1]:
            return apply(cfg, "PACKET->marker-after-gap", L(5), R2, {}), "packet"
    raise Uncovered(f"packet phase: left cells {tail} in {cfg}")


def marks_of(cfg):
    """Runs of length >= 2 in the content, positions relative to the leftmost 1 (for comparing with the model)."""
    cells = []
    for t in cfg.left + [("HEAD",)] + cfg.right:
        if isinstance(t, Blank) or t == ("HEAD",): cells.append(t); continue
        if isinstance(t, Rep):
            n = t.n.k
            if n <= 3: cells.extend(list(t.word) * n)
            else: cells.extend([t.word[0], t.word[1], ("ALT", 2 * n - 4), t.word[0], t.word[1]])
        else: cells.append(t)
    seq = [c for c in cells if c != ("HEAD",) and not isinstance(c, Blank)]
    # positions with ALT runs expanded by length
    pos = 0; items = []
    for c in seq:
        if isinstance(c, tuple): pos += c[1]; items.append(("ALT", pos)); continue
        items.append((c, pos)); pos += 1
    first1 = next(p for c, p in items if c == 1); last1 = max(p for c, p in items if c == 1)
    marks = []; i = 0
    lits = [(c, p) for c, p in items]
    while i < len(lits):
        c, p = lits[i]
        if c in (0, 1):
            jj = i
            while jj + 1 < len(lits) and lits[jj + 1][0] == c and lits[jj + 1][1] == lits[jj][1] + 1: jj += 1
            n = jj - i + 1
            if n >= 2 and first1 <= p and lits[jj][1] <= last1:
                t = {(0, 2): "W", (0, 3): "G", (1, 2): "M", (1, 3): "B"}.get((c, n), f"{'XZ'[c == 0]}{n}")
                marks.append((t, p - first1))
            i = jj + 1
        else:
            i += 1
    return last1 - first1 + 1, marks


def run_from_blank(max_rounds, check=None, report_every=0):
    cfg = Config([Blank()], "A", [Blank()])
    while not proofs.is_pass_position(cfg):             # the first 17 steps: plain steps and cycle lemmas
        if not try_lemma(cfg): step(cfg)
    rounds = [(cfg.steps.k,) + marks_of(cfg)]
    cleans = []
    phase = "gap"
    while len(rounds) < max_rounds:
        if phase == "gap":
            cfg = gap_phase(cfg)
            phase = "gap" if proofs.is_pass_position(cfg) else "packet"
        else:
            # clean tape check: 0^inf A> 1 1 (10)^n 1 1 0^inf, reached by the carry
            probe = cfg.copy(); try_lemma(probe, use=("CARRY",))
            if ends_with_blank(probe.left) and len(canon(probe.left)) == 1:
                rr = canon(probe.right)
                if rr[:2] == [1, 1]:
                    n_, rest = count_pairs(rr[2:], (1, 0))
                    if canon(rest) == [1, 1, Blank()]: cleans.append((probe.steps.k - 1, n_.k))
            cfg, kind = packet_phase(cfg)
            if kind in ("round",):
                phase = "gap"; rounds.append((cfg.steps.k,) + marks_of(cfg))
                if report_every and len(rounds) % report_every == 0:
                    print(len(rounds), rounds[-1][0], rounds[-1][1], cleans[-1] if cleans else None, flush=True)
            elif kind is None:
                phase = "gap"
            else:
                phase = "packet"
    return rounds, cleans


if __name__ == "__main__":
    import os
    nr = int(sys.argv[1]) if len(sys.argv) > 1 else 1434
    rounds, cleans = run_from_blank(nr)
    print(f"{len(rounds)} rounds using only proven rules: step {rounds[-1][0]}, tape width {rounds[-1][1]}, "
          f"{len(cleans)} clean tapes (last: n = {cleans[-1][1]} at step {cleans[-1][0]})")
    if not os.path.exists("../m2/rounds3e9.txt"):
        sys.exit()
    real = [l.split() for l in open("../m2/rounds3e9.txt") if l.strip()]
    ok = 0
    for (st, w, mk), r in zip(rounds, real):
        want = (int(r[0]), int(r[1][1:]), [(x[0], int(x[1:])) for x in r[2:]])
        if (st, w, mk) == want: ok += 1
        else:
            print("MISMATCH", (st, w, mk), want); break
    print(f"{len(rounds)} rounds, {ok} match the step-by-step run (steps and marks)")
    known = [tuple(x[:2]) for x in json.load(open("../m2/clean3e9.json"))]
    print("clean tapes match:", cleans[:len(known)] == known[:len(cleans)], len(cleans))
