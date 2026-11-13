"""The first end event of 1RB0RD_1LC0RA_1LF1LD_0RE0LC_---1LB_1RB1RC by a straight-line program, and its Lean
certificate.

The first arrival of A at the counter from blank tape (step 30,225, a wall of 10 pairs) has the counter digits
x1..x109 (each followed by a separator 1) and the last cell x110 = 1.  The k-th sweep after it runs into x110 exactly
when the word a^k, applied to x1..x109 digit by digit, leaves a non-empty word of sections at the end (the sections
are the carry states; the identity is left out).  The words are kept as a straight-line program with
hash-consing, so a^k for k ~ 10^10 is a table of a few thousand nodes; a binary search finds the first such k.

Writes lean/Cert.lean: the table, the entries (node, digit) -> (section node, digit) that the digit-by-digit run
used, the node P of a^(k-1), the digits before and after.  Lean checks the entries (`okAll`, `Orbit.lean`).

usage: python3 py/slp.py            (well under a second)
"""
import os
import sys

sys.setrecursionlimit(100000)
HERE = os.path.dirname(os.path.abspath(__file__))
ACT = {('a', 0): (1, None), ('a', 1): (0, 'b'), ('b', 0): (1, 'a'), ('b', 1): (0, 'c'),
       ('c', 0): (0, 'c'), ('c', 1): (1, 'a')}
# the right part of the tape at the first arrival (head on its first cell), from blank tape: step 30,225
R0 = ("11010111011111010111110111010111010111010111010111010111010111010111010111010111010111010111010111010111010111"
      "010111010111010111010111010111010111010111010111010111010111010111010111110101010101010111010101010101110101111")
WALL0, STEP0 = 10, 30225


class SLP:
    def __init__(self):
        self.ids, self.table, self.memo = {}, [], {}
        self.EPS = self.mk(('eps',))

    def mk(self, t):
        if t not in self.ids:
            self.ids[t] = len(self.table)
            self.table.append(t)
        return self.ids[t]

    def cat(self, x, y):
        if x == self.EPS:
            return y
        if y == self.EPS:
            return x
        return self.mk(('cat', x, y))

    def power(self, k):
        r, p = self.EPS, self.mk(('g', 'a'))
        while k:
            if k & 1:
                r = self.cat(r, p)
            k >>= 1
            if k:
                p = self.cat(p, p)
        return r

    def trans(self, n, x):
        """Node n on digit x: (node of the sections, new digit)."""
        if (n, x) not in self.memo:
            t = self.table[n]
            if t[0] == 'eps':
                r = (self.EPS, x)
            elif t[0] == 'g':
                o, g = ACT[(t[1], x)]
                r = (self.mk(('g', g)) if g else self.EPS, o)
            else:
                s1, x1 = self.trans(t[1], x)
                s2, x2 = self.trans(t[2], x1)
                r = (self.cat(s1, s2), x2)
            self.memo[(n, x)] = r
        return self.memo[(n, x)]

    def run(self, w, digits):
        out = []
        for i, x in enumerate(digits):
            if w == self.EPS:
                return out + list(digits[i:]), w
            w, y = self.trans(w, x)
            out.append(y)
        return out, w


def main():
    assert len(R0) == 221 and all(R0[i] == '1' for i in range(1, 221, 2)) and R0[0] == '1'
    X = [int(R0[i]) for i in range(2, 220, 2)]
    x110 = int(R0[220])

    def runs_into_end(k):
        s = SLP()
        return s.run(s.power(k), X)[1] != s.EPS

    lo, hi = 0, 1
    while not runs_into_end(hi):
        lo, hi = hi, 2 * hi
    while hi - lo > 1:
        m = (lo + hi) // 2
        lo, hi = (lo, m) if runs_into_end(m) else (m, hi)
    K = hi - 1                                  # sweeps that stop inside x1..x109
    s = SLP()
    P = s.power(K)
    Y, w = s.run(P, X)
    assert w == s.EPS
    q = 'a'
    for d in Y:
        q = ACT[(q, d)][1]
        assert q is not None
    wall = WALL0 + K
    print(f"{K:,} sweeps stop inside the digits; sweep {K + 1:,} (from the arrival with a wall of {wall:,} pairs) "
          f"runs into x110 = {x110} in state {q}")
    print(f"steps from blank tape to that arrival: about {3.0 * wall * wall:.3e}")
    print(f"straight-line program: {len(s.table)} nodes, {len(s.memo)} entries")

    def enc(t):
        return 'e' if t[0] == 'eps' else t[1] if t[0] == 'g' else f"{t[1]},{t[2]}"
    N = len(s.table)
    nodes = ' '.join(enc(t) for t in s.table)
    ents = ' '.join((f"{s.memo[(i, x)][0]},{s.memo[(i, x)][1]}" if (i, x) in s.memo else '-')
                    for i in range(N) for x in (0, 1))
    bits = lambda v: ''.join(map(str, v))
    lens, todo = {}, [P]                        # the exponents of the nodes P is built from
    while todo:
        n = todo.pop()
        if n in lens:
            continue
        t = s.table[n]
        if t[0] == 'g':
            lens[n] = 1
        elif all(c in lens for c in t[1:]):
            lens[n] = lens[t[1]] + lens[t[2]]
        else:
            todo += [n] + list(t[1:])
    assert lens[P] == K
    lenstr = ', '.join(f"({n}, {m})" for n, m in sorted(lens.items()))
    path = os.path.join(HERE, '..', 'lean', 'Cert.lean')
    with open(path, 'w') as f:
        f.write(CERT.format(N=N, NE=2 * N, P=P, K=K, X=bits(X), Y=bits(Y), nodes=nodes, ents=ents, lens=lenstr))
    print("wrote", os.path.normpath(path))


CERT = '''import Orbit

/-! The certificate for the first end event, generated by `py/slp.py`; do not edit by hand.

A straight-line program of {N} nodes (`nodeStr`: `e` empty, a generator, or `i,j` for node i then node j) and the
entries the digit-by-digit run used (`entStr`, for node 0 digit 0, node 0 digit 1, node 1 digit 0, ...: `s,y` or `-`).
Node {P} is a^{K} (`lens0`); `X0` are the digits x1..x109 at the first arrival, `Y0` the digits {K} sweeps later. -/

namespace H74982

def parseNode (t : String) : Node :=
  match t.splitOn "," with
  | ["e"] => .eps
  | ["a"] => .gen .a
  | ["b"] => .gen .b
  | ["c"] => .gen .c
  | [i, j] => .cat i.toNat! j.toNat!
  | _ => .eps

def parseEnt (t : String) : Option (Nat × Bool) :=
  match t.splitOn "," with
  | [s, y] => some (s.toNat!, y == "1")
  | _ => none

def bits (s : String) : List Bool := s.toList.map (· == '1')

def nodeStr : String := "{nodes}"

def entStr : String := "{ents}"

def nodesA : Array Node := ((nodeStr.splitOn " ").map parseNode).toArray

def entsA : Array (Option (Nat × Bool)) := ((entStr.splitOn " ").map parseEnt).toArray

def T0 (i : Nat) : Node := nodesA.getD i .eps

def E0 (i : Nat) (x : Bool) : Option (Nat × Bool) := entsA.getD (2 * i + if x then 1 else 0) none

/-- The digits x1..x109 at the first arrival (step 30,225, a wall of 10 pairs). -/
def X0 : List Bool := bits "{X}"

/-- The digits after {K} sweeps. -/
def Y0 : List Bool := bits "{Y}"

theorem cert_size : entsA.size = {NE} := by native_decide

theorem cert_ok : okAll T0 E0 {N} = true := by native_decide

/-- The nodes that are powers of `a`, with their exponents. -/
def lens0 : List (Nat × Nat) := [{lens}]

theorem cert_pow : lens0.all (fun p => okPow T0 lens0 p.1 p.2) = true := by native_decide

theorem P_mem : ({P}, {K}) ∈ lens0 := by decide

theorem cert_chain : chain T0 E0 {P} X0 = some Y0 := by native_decide

theorem E0_lt (i : Nat) (x : Bool) (e : Nat × Bool) (h : E0 i x = some e) : i < {N} := by
  have hs := cert_size
  apply Classical.byContradiction
  intro hc
  have : ¬ (2 * i + if x then 1 else 0) < entsA.size := by cases x <;> simp <;> omega
  simp [E0, Array.getD, this] at h

/-- {K} sweeps from the first arrival all stop inside the digits x1..x109. -/
theorem sweeps_X0 : sweeps {K} X0 = some Y0 := by
  apply sweeps_of_trW
  rw [← pow_sound T0 lens0 cert_pow {P} {K} P_mem]
  exact chain_sound T0 E0 {N} cert_ok E0_lt {P} X0 Y0 cert_chain

end H74982
'''

if __name__ == "__main__":
    main()
