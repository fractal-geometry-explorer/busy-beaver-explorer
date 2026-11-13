"""Write lean/FrontierRules.lean and lean/Frontier.lean: the left-end phase as a local rewriting system.

In the left-end phase, at each moment the head stands on a new leftmost cell in state A, the tape (read from the head)
is a list of *units* `(01)^b 0 0110`, then a *frontier* `(01)^a w` where `w` is the first word that is not part of a
unit or of `(01)^a`, and then an untouched rest `R`. After a maximal `(01)^a`, the next cells are `1...` or `00...`, so
`w` begins with one of

    1, 00101, 001001, 0001, 0000, 001000   (G1, G2, K, H, X0, X1)
    00110                                  (a unit: the frontier lies further right)
    00111                                  (never seen in the run; not covered here)

One round trip (from the left end over the units to the frontier and back) rewrites only `(01)^a w` and the first unit.
The rules below are those rewrites, proved for every `a` (written `a+3`; the cases `a = 0, 1, 2` are separate rules)
and every rest `R`:

* `tu*` / `su*`: the turn at the frontier when at least one unit lies before it (left context `1 1 0 1 0`, the end of
  a passed unit). `lean/Frontier.lean` turns each into a whole round trip for every list of units.
* `te*` / `se*`: the whole round trip when no unit lies before the frontier (left context blank tape).

The rewrites were found by simulating single round trips and are proved by `tools/py/bbtools/symtm.py`. Seven small cases do not fit the form of `tu*` (the rewrite starts a new unit; see
`README.md`), and are not covered.

usage: python3 holdouts/1RB0LC_1RC0RA_1LA0LD_1LE0RB_1RD1LF_0LA---/py/gen_frontier.py
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "py"))
from bbtools.symtm import prove, rules_file  # noqa: E402

M = "1RB0LC_1RC0RA_1LA0LD_1LE0RB_1RD1LF_0LA---"
CTX = "L 1 1 0 1 0 A> "
EDGE = "0^inf A> "

RULES = [
    ('tuG1', 'L 1 1 0 1 0 A> (01)^a+3 1 R',
     'L 1 1 0 1 0 A> 1 1 (01)^a+2 0 R'),
    ('teG1', '0^inf A> (01)^a+3 1 R',
     '0^inf A> (01)^a+4 0 R'),
    ('tuG2', 'L 1 1 0 1 0 A> (01)^a+3 0 0 1 0 1 R',
     'L 1 1 0 1 0 A> 1 1 (01)^a+4 1 R'),
    ('teG2', '0^inf A> (01)^a+3 0 0 1 0 1 R',
     '0^inf A> (01)^a+6 1 R'),
    ('tuK', 'L 1 1 0 1 0 A> (01)^a+3 0 0 1 0 0 1 R',
     'L 1 1 0 1 0 A> 1 1 (01)^a+5 R'),
    ('teK', '0^inf A> (01)^a+3 0 0 1 0 0 1 R',
     '0^inf A> (01)^a+7 R'),
    ('tuH', 'L 1 1 0 1 0 A> (01)^a+3 0 0 0 1 R',
     'L 1 1 0 1 0 A> 1 1 (01)^a 0 0 1 1 0 0 1 1 R'),
    ('teH', '0^inf A> (01)^a+3 0 0 0 1 R',
     '0^inf A> (01)^a+2 0 0 1 1 0 0 1 1 R'),
    ('tuX0', 'L 1 1 0 1 0 A> (01)^a+3 0 0 0 0 R',
     'L 1 1 0 1 0 A> 1 1 (01)^a 0 0 1 1 0 0 1 0 R'),
    ('teX0', '0^inf A> (01)^a+3 0 0 0 0 R',
     '0^inf A> (01)^a+2 0 0 1 1 0 0 1 0 R'),
    ('tuX1', 'L 1 1 0 1 0 A> (01)^a+3 0 0 1 0 0 0 R',
     'L 1 1 0 1 0 A> 1 1 (01)^a+4 0 0 R'),
    ('teX1', '0^inf A> (01)^a+3 0 0 1 0 0 0 R',
     '0^inf A> (01)^a+6 0 0 R'),
    ('seG10', '0^inf A> 1 R',
     '0^inf A> 0 1 0 R'),
    ('suG11', 'L 1 1 0 1 0 A> 0 1 1 R',
     'L 1 1 0 1 0 A> 1 1 0 R'),
    ('seG11', '0^inf A> 0 1 1 R',
     '0^inf A> 0 1 0 1 0 R'),
    ('suG12', 'L 1 1 0 1 0 A> 0 1 0 1 1 R',
     'L 1 1 0 1 0 A> 1 1 0 1 0 R'),
    ('seG12', '0^inf A> 0 1 0 1 1 R',
     '0^inf A> 0 1 0 1 0 1 0 R'),
    ('suG20', 'L 1 1 0 1 0 A> 0 0 1 0 1 R',
     'L 1 1 0 1 0 A> 1 1 0 1 1 R'),
    ('seG20', '0^inf A> 0 0 1 0 1 R',
     '0^inf A> 0 1 0 1 0 1 1 R'),
    ('suG21', 'L 1 1 0 1 0 A> 0 1 0 0 1 0 1 R',
     'L 1 1 0 1 0 A> 1 1 0 1 0 1 1 R'),
    ('seG21', '0^inf A> 0 1 0 0 1 0 1 R',
     '0^inf A> 0 1 0 1 0 1 0 1 1 R'),
    ('suG22', 'L 1 1 0 1 0 A> 0 1 0 1 0 0 1 0 1 R',
     'L 1 1 0 1 0 A> 1 1 0 1 0 1 0 1 1 R'),
    ('seG22', '0^inf A> 0 1 0 1 0 0 1 0 1 R',
     '0^inf A> 0 1 0 1 0 1 0 1 0 1 1 R'),
    ('suK0', 'L 1 1 0 1 0 A> 0 0 1 0 0 1 R',
     'L 1 1 0 1 0 A> 1 1 0 1 0 1 R'),
    ('seK0', '0^inf A> 0 0 1 0 0 1 R',
     '0^inf A> 0 1 0 1 0 1 0 1 R'),
    ('suK1', 'L 1 1 0 1 0 A> 0 1 0 0 1 0 0 1 R',
     'L 1 1 0 1 0 A> 1 1 0 1 0 1 0 1 R'),
    ('seK1', '0^inf A> 0 1 0 0 1 0 0 1 R',
     '0^inf A> 0 1 0 1 0 1 0 1 0 1 R'),
    ('suK2', 'L 1 1 0 1 0 A> 0 1 0 1 0 0 1 0 0 1 R',
     'L 1 1 0 1 0 A> 1 1 0 1 0 1 0 1 0 1 R'),
    ('seK2', '0^inf A> 0 1 0 1 0 0 1 0 0 1 R',
     '0^inf A> 0 1 0 1 0 1 0 1 0 1 0 1 R'),
    ('seH0', '0^inf A> 0 0 0 1 R',
     '0^inf A> 0 1 0 1 0 1 1 1 R'),
    ('seH1', '0^inf A> 0 1 0 0 0 1 R',
     '0^inf A> 0 0 1 1 0 0 1 1 R'),
    ('seH2', '0^inf A> 0 1 0 1 0 0 0 1 R',
     '0^inf A> 0 1 0 0 1 1 0 0 1 1 R'),
    ('seX00', '0^inf A> 0 0 0 0 R',
     '0^inf A> 0 1 0 1 0 1 1 0 R'),
    ('seX01', '0^inf A> 0 1 0 0 0 0 R',
     '0^inf A> 0 0 1 1 0 0 1 0 R'),
    ('seX02', '0^inf A> 0 1 0 1 0 0 0 0 R',
     '0^inf A> 0 1 0 0 1 1 0 0 1 0 R'),
    ('suX10', 'L 1 1 0 1 0 A> 0 0 1 0 0 0 R',
     'L 1 1 0 1 0 A> 1 1 0 1 0 0 R'),
    ('seX10', '0^inf A> 0 0 1 0 0 0 R',
     '0^inf A> 0 1 0 1 0 1 0 0 R'),
    ('suX11', 'L 1 1 0 1 0 A> 0 1 0 0 1 0 0 0 R',
     'L 1 1 0 1 0 A> 1 1 0 1 0 1 0 0 R'),
    ('seX11', '0^inf A> 0 1 0 0 1 0 0 0 R',
     '0^inf A> 0 1 0 1 0 1 0 1 0 0 R'),
    ('suX12', 'L 1 1 0 1 0 A> 0 1 0 1 0 0 1 0 0 0 R',
     'L 1 1 0 1 0 A> 1 1 0 1 0 1 0 1 0 0 R'),
    ('seX12', '0^inf A> 0 1 0 1 0 0 1 0 0 0 R',
     '0^inf A> 0 1 0 1 0 1 0 1 0 1 0 0 R'),]

NAMES = {"G1": "1", "G2": "00101", "K": "001001", "H": "0001", "X0": "0000", "X1": "001000"}


def lean_word(pat, tail):
    """The Lean tape for a pattern such as '(01)^a+3 0 0 1' (no context letters), in front of `tail`."""
    toks = pat.split()
    acc = tail
    for t in reversed(toks):
        if t in ("0", "1"):
            acc = f"cons {'true' if t == '1' else 'false'} ({acc})"
        else:
            m = re.fullmatch(r"\(01\)\^(a(?:\+\d+)?)", t)
            assert m, t
            acc = f"rep ({m.group(1).replace('+', ' + ')}) [false, true] ({acc})"
    return acc


def strip(s, head):
    assert s.startswith(head) and s.endswith(" R"), s
    return s[len(head):-2].strip()


def split_args(t):
    """Split `f (x) (y) z` style text at top-level spaces."""
    out, depth, cur = [], 0, ""
    for ch in t:
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        if ch == " " and depth == 0:
            if cur:
                out.append(cur)
            cur = ""
        else:
            cur += ch
    if cur:
        out.append(cur)
    return out


def unparen(t):
    t = t.strip()
    while t.startswith("(") and t.endswith(")"):
        depth = 0
        for i, ch in enumerate(t):
            depth += ch == "("
            depth -= ch == ")"
            if depth == 0 and i < len(t) - 1:
                return t
        t = t[1:-1].strip()
    return t


def rhs_tape(text):
    """The right tape `r` of the final configuration in a symtm theorem statement."""
    stmt = text[text.index("= some ⟨") + len("= some ⟨"):]
    depth, parts, cur = 0, [], ""
    for ch in stmt:
        if ch in "(⟨":
            depth += 1
        elif ch in ")⟩":
            if depth == 0:
                break
            depth -= 1
        if ch == "," and depth == 0:
            parts.append(cur)
            cur = ""
        else:
            cur += ch
    return unparen(parts[1])


def peel_true(t):
    """`u` with `t` = `cons true u` (up to unfolding one `rep`), as Lean text."""
    a = split_args(unparen(t))
    if a[0] == "cons" and a[1] == "true":
        return unparen(a[2])
    if a[0] == "rep" and a[2] == "[true," and a[3] == "false]":
        n = unparen(a[1])
        m = re.fullmatch(r"a \+ (\d+)", n)
        assert m, n
        k = int(m.group(1)) - 1
        rest = unparen(a[4])
        inner = f"rep (a + {k}) [true, false] ({rest})" if k else f"rep a [true, false] ({rest})"
        return f"cons false ({inner})"
    raise ValueError(t)


def trip_theorem(name, s, text):
    """The whole round trip for a `tu`/`su` rule, from `tripGen`."""
    w_in = strip(s, CTX)
    has_a = "a" in w_in
    args = "(x a : Nat)" if has_a else "(x : Nat)"
    In = lean_word(w_in, "S")
    Out = re.sub(r"\bR\b", "S", peel_true(peel_true(rhs_tape(text))))
    final = f"cons false (cons true (cons false (cons true (cons false (cons true ({Out}))))))"
    rule_args = "a L S" if has_a else "L S"
    return (f"/-- One round trip at the frontier `{w_in}` for every list of units (rule `{name}`). -/\n"
            f"theorem trip_{name} {args} (bs : List Nat) (S : Tape) :\n"
            f"    ∃ n, steps n ⟨blank, Un (x + 2) (UL bs ({In})), .A⟩ =\n"
            f"      some ⟨blank, Un (x + 1) (UL bs ({final})), .A⟩ :=\n"
            f"  tripGen ({In}) ({Out}) (fun L => ⟨_, {name} {rule_args}⟩) x bs\n")


FDOC = ("The frontier rules of the left-end phase of " + M + ", written by `tools/py/bbtools/symtm.py` and checked by "
        "the kernel; see `py/gen_frontier.py` for what they mean. Regenerate with `py/gen_frontier.py`.")

HEAD = '''import FrontierRules
import Cursor

/-!
# The left-end phase as a local rewriting system

`tripGen`: if the head, standing just right of a passed unit (left context `1 1 0 1 0`), turns at the word `In` and
leaves `1 1 Out` behind, then for every first unit `(01)^(x+2) 0 0110` and every list `bs` of units
`(01)^(b+2) 0 0110` the whole round trip from the left end takes

    A> (01)^(x+2) 0 0110  units(bs)  In     to     A> (01)^(x+1) 0 0110  units(bs)  0 1 0 1 0 1 Out .

The `trip_*` theorems apply it to each frontier rule of `FrontierRules.lean` (written by `py/gen_frontier.py`). The
`te*`/`se*` rules there are already whole round trips (no unit before the frontier).
-/

namespace H14847

open TM

/-- The left context `1 1 0 1 0` (stored nearest cell first) in front of `L`. -/
def Vc (L : Tape) : Tape := cons false (cons true (cons false (cons true (cons true L))))

theorem tripGen (In Out : Tape)
    (hturn : ∀ L, ∃ n, steps n ⟨Vc L, In, .A⟩ = some ⟨Vc L, cons true (cons true Out), .A⟩)
    (x : Nat) (bs : List Nat) :
    ∃ n, steps n ⟨blank, Un (x + 2) (UL bs In), .A⟩ =
      some ⟨blank, Un (x + 1) (UL bs (cons false (cons true (cons false (cons true (cons false (cons true
        Out))))))), .A⟩ := by
  have h1 := unitR (x + 2) blank (UL bs In)
  obtain ⟨n2, h2⟩ := passR bs (Vn (x + 2) blank) In
  obtain ⟨m, L', e⟩ := VL_shape bs (x + 2) blank
  obtain ⟨n3, h3⟩ := hturn (rep m [false, true] L')
  rw [show Vc (rep m [false, true] L') = VL bs (Vn (x + 2) blank) by rw [e]; rfl] at h3
  obtain ⟨n4, h4⟩ := passL bs (Vn (x + 2) blank) (cons true Out)
  have h5 := unitL x blank (ZL bs (cons true Out))
  have h6 := edgeL (Zn x (ZL bs (cons true Out)))
  rw [shiftX, shiftL] at h6
  exact ⟨_, steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (steps_seq trans h4
    (steps_seq trans h5 h6))))⟩

'''

if __name__ == "__main__":
    texts, body = [], []
    for name, s, e in RULES:
        doc = f"Frontier rule `{name}`: `{s}` to `{e}`."
        text, _ = prove(M, name, s, e, doc=doc, rotate=True, count_first=True, max_seg=40)
        texts.append(text)
        if name.startswith(("tu", "su")):
            body.append(trip_theorem(name, s, text))
    with open(os.path.join(HERE, "..", "lean", "FrontierRules.lean"), "w") as f:
        f.write(rules_file("Machine", "H14847", texts, FDOC))
    with open(os.path.join(HERE, "..", "lean", "Frontier.lean"), "w") as f:
        f.write(HEAD + "\n".join(body) + "\nend H14847\n")
