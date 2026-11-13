"""The block-level law of this machine as a program, checked against the machine itself.

The three machines 1RB0RC_1LC1LA_1RD0LB_1RE1RC_1RA0RF_1RC--- (the reference), 1RB0RF_1RC0RD_1LD1LB_1RE0LC_1RA1RD_1RD---
(the same table, states renamed) and 1RB1RE_1LC0RA_1LD1LB_1LE0LF_1LA0LB_1LB--- (its mirror image, states renamed) follow
one law; they differ only in where they start.  This file is the same in the three folders.  Everything is printed in
the reference orientation (blocks on the left of the head, gaps on the right) with the reference machine's state
names B, C, D, F; for the mirror machine read left as right.

A configuration is
  L   the closed blocks behind the head (a block `1^b 0` is the number b), the nearest one last in the Python list
  o   the length of the open block next to the head
  q   C, D, F (the head moves outward, on the first cell of the gap g) or B (it moves back; z zeros lie between it
      and the next 1; with o = 0 it stands on the separator of the last block of L)
  G   the gaps ahead (a gap `0^g 1` is the number g), the nearest one last in the Python list
The rule names are those of the theorems of lean/Law.lean, where each rule is proved for all sizes.

usage (from the repository root):
  python3 holdouts/MACHINE/py/law.py check [MACRO_STEPS]      compare with the machine step by step (default 100000 rules)
  python3 holdouts/MACHINE/py/law.py turns [FROM_STEP] [COUNT]  the configuration at every turn of the head
  python3 holdouts/MACHINE/py/law.py ends [FROM_STEP] [COUNT]   the gap list each time the head turns at the block end of the tape
  python3 holdouts/MACHINE/py/law.py rules [MACRO_STEPS]      how often each rule is used
  python3 holdouts/MACHINE/py/law.py words [MAXLEN]           tapes made of the words S, P, Q that halt (see README)
"""
import itertools
import os
import sys
from collections import Counter

MACHINE = os.path.basename(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
REF = "1RB0RC_1LC1LA_1RD0LB_1RE1RC_1RA0RF_1RC---"
# k: the start is the return state on blank tape with k ones behind the head, reached after n0 machine steps;
# names: this machine's name for the reference states A..F; mirror: the tape is the mirror image
INFO = {
    "1RB0RC_1LC1LA_1RD0LB_1RE1RC_1RA0RF_1RC---": dict(k=1, n0=1, names="ABCDEF", mirror=False),
    "1RB0RF_1RC0RD_1LD1LB_1RE0LC_1RA1RD_1RD---": dict(k=2, n0=2, names="BCDEAF", mirror=False),
    "1RB1RE_1LC0RA_1LD1LB_1LE0LF_1LA0LB_1LB---": dict(k=0, n0=0, names="EABCDF", mirror=True),
}.get(MACHINE, dict(k=1, n0=1, names="ABCDEF", mirror=False))
INF = float("inf")


class Halt(Exception):
    pass


class Law:
    def __init__(self, k=None, n0=None):
        k = INFO["k"] if k is None else k
        self.L = [k] if k else []
        self.o, self.q, self.z, self.g, self.G = 0, "B", INF, None, []
        self.steps = INFO["n0"] if n0 is None else n0
        self.rule = None

    def pop_l(self):
        return self.L.pop() if self.L else 0

    def pop_g(self):
        return self.G.pop() if self.G else INF

    def push_g(self, g):
        if g != INF:
            self.G.append(g)

    def step(self):
        """one rule; sets self.rule to its name in lean/Law.lean (without the _end/_last/_inf suffixes)"""
        if self.q == "B":
            o, z = self.o, self.z
            if o >= 3:
                self.rule, self.o, self.z = "b_triple", o - 3, 1
                self.push_g(z + 1)
                self.steps += 5
            elif o == 2:
                self.rule, self.o, self.q, self.g = "b_turn2", self.pop_l() + 3, "D", z
                self.steps += 7
            elif o == 1:
                b = self.pop_l()
                if b >= 1:
                    self.rule, self.o, self.z = "b_one", b - 1, 1
                    self.push_g(z + 1)
                    self.steps += 7
                else:
                    self.rule, self.o, self.q, self.g = "b_turn1", self.pop_l() + 3, "D", z
                    self.steps += 9
            else:
                b = self.pop_l()
                if b >= 1:
                    self.rule, self.o, self.z = "b_zero", b - 1, 1
                    self.push_g(z)
                    self.steps += 2
                else:
                    self.rule, self.o, self.q, self.g = "b_turn0", self.pop_l() + 2, "C", z
                    self.steps += 3
            return
        g = self.g
        if self.q == "C":
            if g == 0:
                self.rule, self.q, self.z = "c_turn0", "B", 1 + self.pop_g()
                self.steps += 1
            elif g == 1:
                self.rule, self.o, self.g = "c_gap1", self.o + 2, self.pop_g()
                self.steps += 2
            elif g == 2:
                self.L.append(self.o + 2)
                self.rule, self.o, self.q, self.g = "c_gap2", 0, "F", self.pop_g()
                self.steps += 3
            elif g == 3:
                self.L.append(self.o + 3)
                self.rule, self.o, self.g = "c_gap3", 0, self.pop_g()
                self.steps += 4
            else:
                self.turn(4, "c_turn4", "c_turn5")
        elif self.q == "F":
            if g == 0:
                self.rule = "halt"
                raise Halt()
            self.rule, self.o, self.g, self.q = "f_step", self.o + 1, g - 1, "C"
            self.steps += 1
        else:
            if g == 0:
                self.rule, self.o, self.q, self.g = "d_gap0", self.o + 1, "C", self.pop_g()
                self.steps += 1
            elif g == 1:
                self.L.append(self.o + 1)
                self.rule, self.o, self.q, self.g = "d_gap1", 0, "F", self.pop_g()
                self.steps += 2
            elif g == 2:
                self.L.append(self.o + 2)
                self.rule, self.o, self.q, self.g = "d_gap2", 0, "C", self.pop_g()
                self.steps += 3
            else:
                self.turn(3, "d_turn3", "d_turn4")

    def turn(self, k, exact, longer):
        """k ones written; the head turns on the next cell (the 1 that ends the gap, or one more 0)"""
        self.q = "B"
        self.steps += k
        if self.g == k:
            self.rule, self.o, self.z = exact, self.o + k + 1, self.pop_g()
        else:
            self.L.append(self.o + k)
            self.rule, self.o, self.z = longer, 0, self.g - k - 1

    def decode(self):
        """(cells between the outermost 1s, index of the head in them, state): the tape in the reference orientation"""
        left = "".join("1" * b + "0" for b in self.L) + "1" * self.o
        if self.q == "B":
            if self.o == 0 and not self.L:
                left = "0"
            hp = len(left) - 1
            right = "" if self.z == INF else "0" * self.z + "1"
        else:
            hp = len(left)
            right = "" if self.g == INF else "0" * self.g + "1"
        for g in reversed(self.G):
            right += "0" * g + "1"
        cells = left + right
        a, b = cells.find("1"), cells.rfind("1")
        if a < 0:
            return "", 0, self.q
        return cells[a:b + 1], hp - a, self.q


def parse(m):
    t = {}
    for s, part in enumerate(m.split("_")):
        for r in range(2):
            x = part[3 * r:3 * r + 3]
            t[(s, r)] = None if x[2] == "-" else (int(x[0]), 1 if x[1] == "R" else -1, ord(x[2]) - 65)
    return t


def comp(lens):
    out, i = [], 0
    while i < len(lens):
        j = i
        while j < len(lens) and lens[j] == lens[i]:
            j += 1
        out.append(str(lens[i]) if j - i == 1 else f"{lens[i]}^{j - i}")
        i = j
    return " ".join(out)


def check(n):
    """run the law and the machine side by side: after every rule the tape, the head and the state must agree"""
    t = parse(MACHINE)
    size = 1 << 22
    tape = bytearray(size)
    p, st, k = size // 2, 0, 0
    lo = hi = p
    back = {name: "ABCDEF"[i] for i, name in enumerate(INFO["names"])}   # this machine's state -> reference state
    m = Law()
    for i in range(n):
        while k < m.steps:
            w, d, st2 = t[(st, tape[p])]
            tape[p], p, st, k = w, p + d, st2, k + 1
            lo, hi = min(lo, p), max(hi, p)
        x = bytes(tape[lo:hi + 1])
        a, b = x.find(1), x.rfind(1)
        if a < 0:
            got = ("", 0, back["ABCDEF"[st]])
        elif INFO["mirror"]:
            got = ("".join("01"[c] for c in x[a:b + 1])[::-1], b - (p - lo), back["ABCDEF"[st]])
        else:
            got = ("".join("01"[c] for c in x[a:b + 1]), (p - lo) - a, back["ABCDEF"[st]])
        want = m.decode()
        if got[0] != want[0] or got[2] != want[2] or (got[0] and got[1] != want[1]):
            print("MISMATCH after", i, "rules,", m.steps, "steps:", got, want)
            sys.exit(1)
        m.step()
    print(f"{MACHINE}: the law and the machine agree after each of the first {n} rules ({m.steps} machine steps)")


def turns(start, count, ends_only=False, width=70):
    m = Law()
    seen = 0
    while seen < count:
        was = m.q
        m.step()
        if m.steps < start or (was == "B") == (m.q == "B"):
            continue
        if ends_only:
            if m.q != "B" and not m.L:
                seen += 1
                print(f"{m.steps:>12} {m.q} open {m.o} | {m.g} {comp(m.G[::-1])}")
            continue
        seen += 1
        x = m.z if m.q == "B" else m.g
        print(f"{m.steps:>12} {'<' if m.q == 'B' else '>'} ..{comp(m.L)[-width:]:>{width}} [{m.o:>2}] {m.q} {x} | {comp(m.G[::-1])[:width + 30]}")


def rules(n):
    m = Law()
    use = Counter()
    for _ in range(n):
        m.step()
        use[m.rule] += 1
    print(f"{n} rules, {m.steps} machine steps")
    for name, c in sorted(use.items(), key=lambda kv: -kv[1]):
        print(f"  {name:10} {c}")


WORDS = {"S": [1], "P": [2, 2], "Q": [4, 2]}


def run_word(start, word, max_rules):
    """the law from the block end of a tape whose gaps spell `word`; start C (open block 2) or D (open block 3), gap 1"""
    m = Law(0, 0)
    m.G = [g for w in word for g in WORDS[w]][::-1]
    m.q, m.o, m.g = (("C", 2, 1) if start == "C" else ("D", 3, 1))
    try:
        for _ in range(max_rules):
            m.step()
    except Halt:
        return m.steps
    return None


def words(maxlen, max_rules=20000):
    """every tape made of the even-length words S = `01`, P = `001001`, Q = `00001001` up to maxlen words"""
    halting, with_sq, without_sq, total = [], 0, 0, 0
    for n in range(1, maxlen + 1):
        for w in itertools.product("SPQ", repeat=n):
            w = "".join(w)
            for start in "CD":
                total += 1
                r = run_word(start, w, max_rules)
                if r is not None:
                    halting.append((start, w, r))
                    if "SQ" in w:
                        with_sq += 1
                    else:
                        without_sq += 1
    print(f"{total} tapes of at most {maxlen} words, two starts each, {max_rules} rules each: {len(halting)} halt;")
    print(f"  {with_sq} of them contain S immediately followed by Q, {without_sq} do not")
    for start, w, r in halting[:12]:
        print(f"  start {start}, gaps {' '.join(str(g) for x in w for g in WORDS[x])} ({w}): halts after {r} steps")


if __name__ == "__main__":
    a = sys.argv[1:]
    cmd = a[0] if a else "check"
    if cmd == "check":
        check(int(a[1]) if len(a) > 1 else 100000)
    elif cmd in ("turns", "ends"):
        turns(int(a[1]) if len(a) > 1 else 0, int(a[2]) if len(a) > 2 else 40, cmd == "ends")
    elif cmd == "rules":
        rules(int(a[1]) if len(a) > 1 else 1000000)
    elif cmd == "words":
        words(int(a[1]) if len(a) > 1 else 6)
    else:
        print(__doc__)
