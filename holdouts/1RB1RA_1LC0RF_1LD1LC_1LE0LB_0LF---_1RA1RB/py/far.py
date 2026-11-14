"""FAR (finite automata reduction, direct): a DFA on the left tape (far end first), the right NFA by saturation.
DFA = observed states of a run-length window automaton (rlg.GSide) + a sink."""
import sys, collections
import rlf, rlg
from rlctl import Machine, STATES

def mirror(mt):
    return "_".join("".join((t if t == "---" else t[0] + ("L" if t[1] == "R" else "R") + t[2]) for t in (r[:3], r[3:])) for r in mt.split("_"))

def observe_left(mt, side, steps):
    """run the machine, push every left tape into `side`; returns the set of observed (dfa state) and transitions"""
    m = Machine.parse(mt)
    N = 1 << 22
    tape = bytearray(N); Ls = [0] * N
    p = N // 2; s = 0
    for step in range(steps):
        t = m.table[s][tape[p]]
        w, d, s2 = t
        tape[p] = w
        if d == 1:
            Ls[p] = side.push(Ls[p - 1], w)[0]
            p += 1
        else:
            p -= 1
        s = s2
    return m

def far(m, side, verbose=False):
    n = len(side.states); SINK = n
    delta = [[SINK, SINK] for _ in range(n + 1)]
    for (j, x, q) in side.edges: delta[q][x] = j
    delta[0][0] = 0
    pred = [[[], []] for _ in range(n + 1)]
    for q in range(n + 1):
        for x in (0, 1): pred[delta[q][x]][x].append(q)
    HALT = (n + 1) * 6
    def nid(q, f): return q * 6 + f
    T = [[set(), set()] for _ in range(HALT + 1)]
    T[HALT][0].add(HALT); T[HALT][1].add(HALT)
    Lrules = []
    for q in range(n + 1):
        for f in range(6):
            for r in (0, 1):
                t = m.table[f][r]
                if t is None: T[nid(q, f)][r].add(HALT)
                else:
                    w, d, t2 = t
                    if d == 1: T[nid(q, f)][r].add(nid(delta[q][w], t2))
                    else: Lrules.append((nid(q, f), r, w, t2, q))
    rounds = 0
    while True:
        changed = False; rounds += 1
        for (src, r, w, t2, q) in Lrules:
            tgt = T[src][r]
            for b in (0, 1):
                for q1 in pred[q][b]:
                    for X1 in list(T[nid(q1, t2)][b]):
                        new = T[X1][w] - tgt
                        if new: tgt |= new; changed = True
        if not changed: break
    # accepting: can reach HALT by zeros
    seen = {nid(0, 0)}; todo = [nid(0, 0)]
    while todo:
        x = todo.pop()
        for y in T[x][0]:
            if y not in seen: seen.add(y); todo.append(y)
    ok = HALT not in seen
    if verbose: print("dfa states", n + 1, "nfa transitions", sum(len(a) + len(b) for a, b in T), "rounds", rounds, "start accepted:", not ok)
    return ok, delta, T, HALT

if __name__ == "__main__":
    mt = sys.argv[1]; mir = sys.argv[2] == "R"
    M, c1, c0, cg = map(int, sys.argv[3:7]); steps = int(float(sys.argv[7])); feats = sys.argv[8]; m1, mg = int(sys.argv[9]), int(sys.argv[10])
    if mir: mt = mirror(mt)
    side = rlg.GSide(M, c1, c0, cg, feats, m1, mg)
    m = observe_left(mt, side, steps)
    ok, delta, T, HALT = far(m, side, True)
    print("PROVED non-halting" if ok else "no proof", sys.argv[2:])
