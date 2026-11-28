"""The other ticks of 1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB--- that do not need the left end: new turn pieces for
the chain machinery of lean/Chain.lean, and a check that every tick of the run is an instance of a Lean theorem.

usage: python3 py/chain2.py                 writes lean/Chain2.lean
       python3 py/chain2.py check B.txt     B.txt from `c/blocks STEPS`: every tick, which theorem it is an instance of

The turn shapes (block notation, p any block, a odd, the e's even):

    x | p | a . e1 . b1 . c1 . … . d . e     an odd number of even blocks after a: the turn is at the separator
                                             before p (p even: `turn_pe`, p odd ≥ 3: `turn_po`, p = 1: `turn_p1`)
    x | 1 | a . b1 . c1 . … . d . e          an even number: as `tick_chain_oo`, with a first block of length 1
                                             (`turn_1o`)
    x | p | a . e                            one even block: whole ticks (`tick_pe_last`, `tick_po_last`,
                                             `tick_p1_last`)

Each piece is a symbolic run (`bbtools.symtm`, rebracketed by `py/tapeeq.py`); the passes are those of Chain.lean.
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "py"))
from bbtools.symtm import Config, run, rules_file, tokens, left_term, canon  # noqa: E402
from bbtools.machine import Machine  # noqa: E402
from tapeeq import rule  # noqa: E402

NS = "H103746"
M = Machine.parse("1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---")

PB = {"e": "1 (1010)^p+1", "o": "1 1 0 (1010)^p 1 0 1 0", "1": "1 1 0"}   # `| p` for p even, odd ≥ 3, p = 1
OA = "1 1 0 (1010)^a 1 0 1 0"      # `| a`, a odd
EV = "0 (1010)^c+1"                 # `. e1`, even
NAME = {"e": "pe", "o": "po", "1": "p1"}

# chain.py's tape pieces, for the check
Q = "0 (1010)^d+1 0 (1010)^e+1"
PC = "0 (1010)^b+1 0 (1010)^c+1"
V = "(1010)^b 1 0 1 0 1 1 (0101)^c 0 1 1 0"
FIN = "(1010)^d 1 0 1 0 1 1 (0101)^e 0 1 0 1 0"
TO2 = "0 1 0 1 (0101)^p 0 1 0 1 0 1 1 (0101)^a 0 1 0 1 1 0"
T2 = "0 1 (0101)^a 0 1 0 1 1 0"


def end_left(start, stop):
    c = Config.parse(start)
    run(M, c, stop, max_moves=200000, rotate=True)
    return c


A0100 = canon(tokens("(0101)^b 0 1 0 0 R"))


def turn_end(front):
    c = end_left(f"L {front} 0 1 0 1 (0101)^b D> 0 1 0 R", lambda c: c.state == 0 and canon(list(c.right)) == A0100)
    return " ".join(map(str, c.left))[2:]        # without the leading `L `


def last_end(front):
    c = end_left(f"L {front} A> 1 1 0^inf", lambda c: c.state == 0 and len(c.right) == 3 and c.right[0] == 1
                 and c.right[1] == 1 and not c.steps.is_zero())
    return " ".join(map(str, c.left))[2:]


def shapes():
    """name -> (vars, front before the head, front after) for the turns and the last ticks"""
    out = {}
    for k in "eo1":
        pv = [] if k == "1" else ["p"]
        f = f"{PB[k]} {OA} 0 (1010)^a2+1"
        out[f"turn_{NAME[k]}"] = (pv + ["a", "a2"], f, turn_end(f))
        f = f"{PB[k]} {OA} {EV}"
        out[f"tick_{NAME[k]}_last"] = (pv + ["a", "c"], f, last_end(f))
    f = f"1 1 0 {OA}"
    out["turn_1o"] = (["a"], f, turn_end(f))
    return out


def lt(s):
    return left_term(tokens(s))


LEAN_TICKS = """
/-- A whole tick of `x | p | a . a2 . b1 . c1 . … . bk . ck . d . e` ({doc}; a odd, the rest even, any k). -/
theorem tick_chain_{nm}{bnd} (a a2 d e : Nat) (ps : List (Nat × Nat)) (L : Tape) : ∃ n,
    steps n ⟨Q d e (P ps (T{nm}{args} a a2 L)), cons true (cons true blank), .A⟩ =
      some ⟨Fin d e (W ps d (T{nm}'{args} a a2 L)), cons true (cons true blank), .A⟩ := by
  obtain ⟨n1, h1⟩ := left_pass (T{nm}{args} a a2 L) ps d (R0 e)
  obtain ⟨n2, h2⟩ := right_pass (T{nm}'{args} a a2 L) ps d (R0 e)
  exact ⟨_, steps_seq trans (enter d e (P ps (T{nm}{args} a a2 L)))
    (steps_seq trans h1 (steps_seq trans (turn_{nm}{args} a a2 _ L _)
      (steps_seq trans h2 (leave d e (W ps d (T{nm}'{args} a a2 L))))))⟩
"""

LEAN_1O = """
/-- A whole tick of `x | 1 | a . b1 . c1 . … . bk . ck . d . e` (a odd, the rest even, any k). -/
theorem tick_chain_1o (a d e : Nat) (ps : List (Nat × Nat)) (L : Tape) : ∃ n,
    steps n ⟨Q d e (P ps (T1o a L)), cons true (cons true blank), .A⟩ =
      some ⟨Fin d e (W ps d (T1o' a L)), cons true (cons true blank), .A⟩ := by
  obtain ⟨n1, h1⟩ := left_pass (T1o a L) ps d (R0 e)
  obtain ⟨n2, h2⟩ := right_pass (T1o' a L) ps d (R0 e)
  exact ⟨_, steps_seq trans (enter d e (P ps (T1o a L)))
    (steps_seq trans h1 (steps_seq trans (turn_1o a _ L _) (steps_seq trans h2 (leave d e (W ps d (T1o' a L))))))⟩
"""

DOC_P = {"pe": "p even", "po": "p odd, at least 3", "p1": "p = 1"}


def main():
    sh = shapes()
    parts = ["set_option maxRecDepth 100000\n"]
    for k in "eo1":
        nm = NAME[k]
        pv = [] if k == "1" else ["p"]
        bnd = " (p : Nat)" if pv else ""
        vs, f, g = sh[f"turn_{nm}"]
        parts.append(f"/-- `L | p | a . a2` ({DOC_P[nm]}, a odd, a2 even), where the tick turns. -/\n"
                     f"def T{nm}{bnd} (a a2 : Nat) (L : Tape) : Tape := {lt('L ' + f)}\n"
                     f"/-- The same after the turn. -/\ndef T{nm}'{bnd} (a a2 : Nat) (L : Tape) : Tape := {lt('L ' + g)}\n")
        args = " p" if pv else ""
        parts += rule(f"turn_{nm}", f"L {f} 0 1 0 1 (0101)^b D> 0 1 0 R", f"L {g} A> (0101)^b 0 1 0 0 R",
                      vs + ["b"], f"⟨Rot b (T{nm}{args} a a2 L), D010 R, .D⟩", f"⟨T{nm}'{args} a a2 L, A0100 b R, .A⟩",
                      f"The turn at the separator before p ({DOC_P[nm]}).")
        vs, f, g = sh[f"tick_{nm}_last"]
        parts += rule(f"tick_{nm}_last", f"L {f} A> 1 1 0^inf", f"L {g} A> 1 1 0^inf", vs,
                      f"⟨{lt('L ' + f)}, cons true (cons true blank), .A⟩",
                      f"⟨{lt('L ' + g)}, cons true (cons true blank), .A⟩",
                      f"A whole tick of `x | p | a . c` ({DOC_P[nm]}, a odd, c even), from one right-end turn to the next.")
        parts.append(LEAN_TICKS.format(nm=nm, bnd=bnd, args=args, doc=DOC_P[nm]))
    vs, f, g = sh["turn_1o"]
    parts.append(f"/-- `L | 1 | a` (a odd), where the tick turns. -/\ndef T1o (a : Nat) (L : Tape) : Tape := {lt('L ' + f)}\n"
                 f"/-- The same after the turn. -/\ndef T1o' (a : Nat) (L : Tape) : Tape := {lt('L ' + g)}\n")
    parts += rule("turn_1o", f"L {f} 0 1 0 1 (0101)^b D> 0 1 0 R", f"L {g} A> (0101)^b 0 1 0 0 R", ["a", "b"],
                  "⟨Rot b (T1o a L), D010 R, .D⟩", "⟨T1o' a L, A0100 b R, .A⟩",
                  "The turn at `| 1 | a`, a odd.")
    parts.append(LEAN_1O)
    doc = "# More tick shapes over chains of even blocks\n\n" + __doc__.split("\n\n", 2)[2].strip() + \
        "\n\nGenerated by `py/chain2.py`."
    with open(os.path.join(HERE, "..", "lean", "Chain2.lean"), "w") as fh:
        fh.write(rules_file("Chain", NS, parts, doc))
    print("wrote lean/Chain2.lean")
    for k, (vs, f, g) in sh.items():
        print(f"{k:16s} {f}  ->  {g}")


# ---------------------------------------------------------------- the check against the run
def expand(s, env):
    out = bytearray()
    for t in s.split():
        if t.startswith("("):
            w, e = t[1:].split(")^")
            n = sum(int(x) if x.isdigit() else env[x] for x in e.split("+"))
            out += bytes(int(ch) for ch in w) * n
        else:
            out += bytes(int(ch) for ch in t)
    return out


def encode(blocks, seps):
    out = bytearray(b"\x01\x00" * blocks[0])
    for n, sp in zip(blocks[1:], seps):
        out += (b"\x01" if sp == "|" else b"\x00") + b"\x01\x00" * n
    return out


def decode(bits):
    """the block list of a left tape (bytes of 0/1), as c/blocks.c prints it"""
    s = bits.index(1)
    out, start, p = "", s, s
    while True:
        a, b = bits.find(b"\x00\x00", p), bits.find(b"\x01\x01", p)
        cand = [x for x in (a, b) if x >= 0 and x < len(bits) - 1]
        if not cand:
            break
        q = min(cand)
        sep = q if bits[q] else q + 1
        out += str((sep - start) // 2) + ("|" if bits[q] else ".")
        start = sep + 1
        p = sep + 1
    return out + str((len(bits) - start) // 2)


def parse(lst):
    nums = list(map(int, re.findall(r"\d+", lst)))
    return nums, re.findall(r"[|.]", lst)


def ev(n):
    return (n - 2) // 2


def od(n):
    return (n - 3) // 2


def match(blocks, seps):
    """(theorem, start pieces, end pieces, first block index of the suffix) or None; pieces are (string, env)"""
    m = len(blocks)
    js = [i + 1 for i, sp in enumerate(seps) if sp == "|"]
    if not js:
        return None
    j = js[-1]
    if any(sp != "." for sp in seps[j:]):
        return None
    rest = blocks[j:]
    sh = SHAPES

    def chain(evens):
        """pairs and Q for a list of even blocks (an even number of them, at least 2)"""
        st, en = [], []
        for i in range(0, len(evens) - 2, 2):
            env = {"b": ev(evens[i]), "c": ev(evens[i + 1])}
            st.append((PC, env))
            en.append((V, env))
        env = {"d": ev(evens[-2]), "e": ev(evens[-1])}
        return st + [(Q, env)], en + [(FIN, env)]
    if all(n % 2 == 0 and n >= 2 for n in rest):
        if len(rest) == 1:
            return "tick_last", [("1 (1010)^k", {"k": rest[0] // 2})], [("0 1 (0101)^k 0 1 0", {"k": rest[0] // 2})], j
        if len(rest) % 2 == 1:
            st, en = chain(rest[1:])
            env = {"a": ev(rest[0])}
            return "tick_chain", [("1 (1010)^a+1", env)] + st, [(T2, env)] + en, j
        return None
    a, evens = rest[0], rest[1:]
    if a % 2 == 0 or a < 3 or j < 2 or seps[j - 2] != "|" or not all(n % 2 == 0 and n >= 2 for n in evens):
        return None
    p = blocks[j - 1]
    if p == 1:
        k = "1"
    elif p % 2:
        k = "o"
    else:
        k = "e"
    if p % 2 and p >= 3 and not evens:
        env = {"a": od(p), "b": od(a)}
        return ("tick_oo", [("1 1 0 (1010)^a 1 0 1 0 1 1 0 (1010)^b 1 0 1 0", env)],
                [("0 1 0 1 (0101)^a 0 1 0 1 0 1 1 (0101)^b 0 1 0 1 0 1 0", env)], j - 1)
    if not evens:
        return None
    penv = {} if k == "1" else {"p": od(p) if k == "o" else ev(p)}
    if len(evens) % 2 == 0:
        st, en = chain(evens)
        if k == "o":
            env = {"p": od(p), "a": od(a)}
            return "tick_chain_oo", [("1 1 0 (1010)^p 1 0 1 0 1 1 0 (1010)^a 1 0 1 0", env)] + st, [(TO2, env)] + en, j - 1
        if k == "1":
            _, f, g = sh["turn_1o"]
            env = {"a": od(a)}
            return "tick_chain_1o", [(f, env)] + st, [(g, env)] + en, j - 1
        return None
    if len(evens) == 1:
        _, f, g = sh[f"tick_{NAME[k]}_last"]
        env = dict(penv, a=od(a), c=ev(evens[0]))
        return f"tick_{NAME[k]}_last", [(f, env)], [(g, env)], j - 1
    _, f, g = sh[f"turn_{NAME[k]}"]
    env = dict(penv, a=od(a), a2=ev(evens[0]))
    st, en = chain(evens[1:])
    return f"tick_chain_{NAME[k]}", [(f, env)] + st, [(g, env)] + en, j - 1


SHAPES = None


def check(path):
    global SHAPES
    from collections import Counter
    SHAPES = shapes()
    rows = [ln.split() for ln in open(path) if ln.strip()]
    cnt, bad, none = Counter(), [], []
    for (step, lst, *_), (_, nxt, *_) in zip(rows, rows[1:]):
        blocks, seps = parse(lst)
        r = match(blocks, seps)
        if r is None:
            none.append(int(step))
            continue
        name, st, en, j = r
        # the tape left of the suffix is untouched: compare from its last block on
        # (from the last nonempty one: a block 0 has no cells)
        k = j - 1
        while k > 0 and blocks[k] == 0:
            k -= 1
        last = encode(blocks[k:j], seps[k:j - 1])
        start = b"".join(expand(s, e) for s, e in st)
        if last + start != encode(blocks[k:], seps[k:]):
            bad.append((step, lst, name, "start"))
            continue
        head = "".join(f"{n}{sp}" for n, sp in zip(blocks[:k], seps))
        if head + decode(last + b"".join(expand(s, e) for s, e in en)) != nxt:
            bad.append((step, lst, name, "end"))
            continue
        cnt[name] += 1
    for k, v in cnt.most_common():
        print(f"{v:7d}  {k}")
    print(f"{sum(cnt.values())} of {len(rows) - 1} ticks are instances of a Lean theorem (Rules, Chain, Chain2), "
          f"{len(none)} need the left end, {len(bad)} mismatches")
    for b in bad[:10]:
        print("  MISMATCH", b)
    return none


if __name__ == "__main__":
    if sys.argv[1:2] == ["check"]:
        check(sys.argv[2])
    else:
        main()
