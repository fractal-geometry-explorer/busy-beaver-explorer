"""The stack model of 1RB1RA_1LC0LF_1RA1LD_1LB1LE_0LC0RD_---0RA: the whole recursion on words, with step counts.

Tokens b = 110, c = 111.  During a visit the tape is

    0^inf [1^n1 0^z1] [1^n2 0^z2] ... [1^nk 0^zk]  +  the active part

a stack of *frames* (n ones, then z zeros; n, z >= 1) and, right of them, one of

    RET(q, v)    1^(q-1) C>1 :: v      the head comes back, on the q-th cell right of the top frame
    Z(v)         C>0 :: v              the head on the last zero of the top frame
    CALL(m, X)   1^m B> X              the head goes right, m ones behind it

where ":: v" is the word v written as  v0, 1 1 v1, 1 1 v2, ...  (bit 0 for b, 1 for c) and X is written
1 1 x0, 1 1 x1, ..., both followed by blank tape.  The transitions (machine steps in brackets):

    RET(q, v), q >= 4      -> RET(q-3, b v)                                             [5]
    RET(3, v)              -> Z(b v)                                                    [5]
    RET(2, v)              -> Z(b v) with one zero less; or, z = 1: pop, RET(n, b v)    [3]
    RET(1, v), z >= 3      -> Z(c v) with two zeros less                                [3]
    RET(1, v), z = 2       -> pop the frame (n, 2): RET(n, c v)                         [3]
    RET(1, v), z = 1       -> pop (n, 1); n >= 2: push (n-2, 1), CALL(1, v)             [5]
                              n = 1: **the machine halts**                              [4, the halting step included]
    Z(c^a b X)             -> one zero less, CALL(3a+2, X)                              [3a+2]
    Z(c^a), a >= 1         -> one zero less, CALL(3a, empty)                            [3a]
    CALL(m, c^j b Y)       -> push (m-1, 3j+2), RET(1, c Y)                             [9j+7]
    CALL(m, c^j), j >= 1   -> push (m-1, 3j), RET(1, c)                                 [9j+1]
    CALL(m, empty)         -> RET(m, c)                                                 [1]

A frame whose zeros run out merges its ones into the m of the next CALL; pushing a frame with no ones (m = 1) adds
its zeros to the frame below.  The bottom of the stack is the blank tape on the left (infinitely many zeros).  A
*visit* is RET(1, v) on the empty stack, the tape 0^inf C>1 :: v: two steps later the head is in B on a blank cell
with blank tape on its left and the word v on its right.

Two calls in a row give the rules of the first write-up:  CALL(m, b R) -> RET(m-1, c c R) [10],
CALL(m, c^j b c^i b Z) -> push (m-1, 3j-1), CALL(3i+8, Z) [9j+3i+18]  (j >= 1).  On words where the right end is not
reached every frame has z = 2 mod 3 and the model is the recursion on words
    F(c^a b X) = b^(a+1) T(X)   (the visit),      T(c^j b Y) = c F^j(c Y)   (the call: j visits inside the visit).

usage: python3 model.py word WORD          the transitions of one visit
       python3 model.py all N              every word of fewer than N tokens: the next word and the step count
                                           (or the halt) against a direct run of the machine
       python3 model.py run VISITS         the run from blank tape, against a direct run (words and step numbers)
       python3 model.py rec N              the recursion F, T on N random words, against the model
"""
import sys, itertools, random

INF = float("inf")
M = "1RB1RA_1LC0LF_1RA1LD_1LB1LE_0LC0RD_---0RA"
T = {}
for s in range(6):
    for b in range(2):
        t = M[s * 7 + b * 3:s * 7 + b * 3 + 3]
        if t[0] != '-':
            T[(s, b)] = (int(t[0]), 1 if t[1] == 'R' else -1, ord(t[2]) - 65)


class Halt(Exception):
    pass


def lead(v):
    return len(v) - len(v.lstrip('c'))


def leave(st, m, z):
    """CALL(m, ..) leaves m - 1 ones and z >= 1 zeros behind"""
    if m == 1:
        st[-1][1] += z
    else:
        st.append([m - 1, z])


def step(st, mode):
    """one transition: (new mode, machine steps); raises Halt(steps up to and including the halting one)"""
    k = mode[0]
    if k == 'RET':
        _, q, v = mode
        n, z = st[-1]
        if q >= 4:
            return ('RET', q - 3, 'b' + v), 5
        if q == 3:
            return ('Z', 'b' + v), 5
        if q == 2:
            if z >= 2:
                st[-1][1] -= 1
                return ('Z', 'b' + v), 3
            st.pop()
            return ('RET', n, 'b' + v), 3
        if z >= 3:
            st[-1][1] -= 2
            return ('Z', 'c' + v), 3
        if z == 2:
            st.pop()
            return ('RET', n, 'c' + v), 3
        st.pop()
        if n == 1:
            raise Halt(4)
        if n == 2:
            st[-1][1] += 1
        else:
            st.append([n - 2, 1])
        return ('CALL', 1, v), 5
    if k == 'Z':
        _, u = mode
        st[-1][1] -= 1
        e = st.pop()[0] if st[-1][1] == 0 else 0
        a = lead(u)
        if a < len(u):
            return ('CALL', e + 3 * a + 2, u[a + 1:]), 3 * a + 2
        return ('CALL', e + 3 * a, ''), 3 * a
    _, m, X = mode
    j = lead(X)
    if j < len(X):
        leave(st, m, 3 * j + 2)
        return ('RET', 1, 'c' + X[j + 1:]), 9 * j + 7
    if j == 0:
        return ('RET', m, 'c'), 1
    leave(st, m, 3 * j)
    return ('RET', 1, 'c'), 9 * j + 1


def visit(w, trace=False):
    """from the visit on w (head in B on the blank left of w) to the next visit: (word, steps); ('HALT', steps)"""
    st = [[0, INF]]
    mode = ('RET', 1, w)
    steps = -2
    first = True
    while True:
        if trace:
            print(f"{steps:7d}  frames {st[1:]}  {mode[0]}({', '.join(map(str, mode[1:]))})")
        if not first and mode[0] == 'RET' and mode[1] == 1 and len(st) == 1:
            return mode[2], steps + 2
        first = False
        try:
            mode, n = step(st, mode)
        except Halt as h:
            return 'HALT', steps + h.args[0]
        steps += n


def direct(w, limit=10 ** 8):
    """the same by running the machine: to the next moment the head is in B on a blank cell with blank tape on its
    left (the left end of the tape can move right during a visit, so "a new cell on the left" is not the test)"""
    cells = {i + 1: x for i, x in enumerate(x for t in w for x in ((1, 1, 0) if t == 'b' else (1, 1, 1)))}
    ones = set(i for i, x in cells.items() if x)
    p, s = 0, 1
    for n in range(limit):
        k = (s, cells.get(p, 0))
        if n and k == (1, 0) and p < min(ones):
            hi = max(ones)
            return "".join("c" if cells.get(i + 2, 0) else "b" for i in range(p + 1, hi + 1, 3)), n
        if k not in T:
            return 'HALT', n + 1
        wr, d, s = T[k]
        cells[p] = wr
        if wr:
            ones.add(p)
        else:
            ones.discard(p)
        p += d
    raise RuntimeError("limit")


class RightEnd(Exception):
    pass


def F(w):
    """the visit as a recursion on words; raises RightEnd where the recursion does not apply"""
    a = lead(w)
    if a == len(w):
        raise RightEnd()
    return 'b' * (a + 1) + Tcall(w[a + 1:])


def Tcall(X):
    j = lead(X)
    if j == len(X):
        raise RightEnd()
    v = 'c' + X[j + 1:]
    for _ in range(j):
        v = F(v)
    return 'c' + v


def main(a):
    if a[0] == "rec":
        sys.setrecursionlimit(100000)
        rnd = random.Random(3)
        ok = bad = end = 0
        for _ in range(int(a[1])):
            w = "".join(rnd.choice("bbc") for _ in range(rnd.randint(1, 60)))
            try:
                r = F(w)
            except RightEnd:
                end += 1
                continue
            if visit(w)[0] == r:
                ok += 1
            else:
                bad += 1
        print(f"{ok + bad + end} random words: the recursion gives the model's next word on {ok}, another word on {bad}; "
              f"{end} reach the right end")
    elif a[0] == "word":
        print(visit(a[1], trace=True))
    elif a[0] == "all":
        tot = bad = halts = 0
        for n in range(1, int(a[1])):
            for t in itertools.product("bc", repeat=n):
                w = "".join(t)
                tot += 1
                r, d = visit(w), direct(w)
                halts += r[0] == 'HALT'
                if r != d:
                    bad += 1
                    if bad < 10:
                        print("MISMATCH", w, r, d)
        print(f"{tot} words: {bad} mismatches with the direct run (next word and step count); {halts} halt")
    else:
        w, steps, bad = "c", 4, 0          # the first visit of the run from blank tape: step 4, word c
        N = int(a[1])
        cells, ones, p, s, n, k = {}, set(), 0, 0, 0, 0
        while k < N:
            if s == 1 and cells.get(p, 0) == 0 and ones and p < min(ones):
                k += 1
                hi = max(ones)
                dw = "".join("c" if cells.get(i + 2, 0) else "b" for i in range(p + 1, hi + 1, 3))
                if (dw, n) != (w, steps):
                    bad += 1
                w, d = visit(w)
                steps += d
            wr, dd, s2 = T[(s, cells.get(p, 0))]
            cells[p] = wr
            if wr:
                ones.add(p)
            else:
                ones.discard(p)
            p += dd
            s = s2
            n += 1
        print(f"{k} visits of the run from blank tape ({n} steps): {bad} mismatches between the model and the direct run")


if __name__ == "__main__":
    main(sys.argv[1:])
