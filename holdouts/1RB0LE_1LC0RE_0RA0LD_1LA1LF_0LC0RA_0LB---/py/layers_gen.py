"""Write lean/Layers.lean: the law of the layered right side, for any number of layers.

Layout of an event (cells right of the head; the head, in state A, is on the event cell):

    A> 0 [Z] (11 [Q] 01 [P] 10)* 11 [Q] 01 [R] 0^inf

Z: digits 0010 = 0, 1010 = 1; Q: 0001 = 0, 0101 = 1; P and R: 1000 = 0, 1010 = 1; all lowest digit first, any
width (Q and P may be empty).  The law: Z + 1; a wrap of Z sends one unit into the chain; a unit into an item adds
3 to its Q; every wrap of Q adds 3 to its P; every wrap of P sends one unit to the next item.  Lean proves it for
every layout (by induction on the list of items), as long as no carry leaves R.

usage (from the repository root):
  python3 holdouts/1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RA_0LB---/py/layers_gen.py MACHINE NAMESPACE > holdouts/MACHINE/lean/Layers.lean
(adapted from the generator of 1RB---_1LC0RF_0RA0LD_1LE1LA_1RF0LF_0LC0RA: the same layout and law; the visit rows
here use E where that machine uses F, A where it uses E in P, and the first visit of a unit bounces once in E)"""
import json, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', '..', '..', 'tools', 'py'))
from rowgen import table, row
from bbtools.symtm import prove

M = sys.argv[1] if len(sys.argv) > 1 else "1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RA_0LB---"
NS = sys.argv[2] if len(sys.argv) > 2 else "H66280"
tr = table(M)
# The siblings with E1 = 0RE make one more visit in E before each increment of Q and inside each unit (it bounces).
BOUNCE = M.split('_')[4][3:] == '0RE'

ROWS = [  # name, state, block, nested visits, expected exit, expected block after, doc
    ("l_e", "A", "0", [("B", "C")], "D", "0", "The event cell: a visit of Z in state B."),
    ("l_z_B_0", "B", "0010", [], "C", "1010", "Z: a digit 0 becomes 1."),
    ("l_z_B_1c", "B", "1010", [("B", "C")], "C", "0010", "Z: a digit 1 becomes 0, carry into the next digit."),
    ("l_z_B_1u", "B", "1010", [("B", "E"), ("A", "E"), ("B", "C")], "C", "0010",
     "Z: the last digit 1 becomes 0, one unit (visits B, A, B) into the chain."),
    ("l_d_B_dd", "B", "11", [("A", "D"), ("E", "C"), ("A", "D")], "E", "01",
     "First visit of a unit: two increments of Q (with a bounce in E between them)."),
    ("l_d_B_cdcd", "B", "11", [("A", "C"), ("A", "D"), ("E", "C"), ("A", "C"), ("A", "D")], "E", "01",
     "First visit of a unit, Q empty: two increments (each two visits of the block 01), a bounce between them."),
    ("l_d_A_d", "A", "01", [("E", "C"), ("A", "D")], "E", "01", "Second visit of a unit: one increment of Q."),
    ("l_d_A_cd", "A", "01", [("E", "C"), ("A", "C"), ("A", "D")], "E", "01", "Second visit of a unit, Q empty."),
    ("l_d_B_01", "B", "01", [], "C", "11", "Third visit of a unit: back to 11."),
    ("l_q_A_0", "A", "0001", [], "D", "0101", "Q: a digit 0 becomes 1."),
    ("l_q_A_1d", "A", "0101", [("E", "C"), ("A", "D")], "D", "0001", "Q: a digit 1 becomes 0, carry."),
    ("l_q_A_1cd", "A", "0101", [("E", "C"), ("A", "C"), ("A", "D")], "D", "0001",
     "Q: the last digit 1 becomes 0, carry into the block 01."),
    ("l_q_E_0", "E", "0001", [], "C", "0001", "A visit in E bounces off a Q digit."),
    ("l_q_E_1", "E", "0101", [], "C", "0101", "A visit in E bounces off a Q digit."),
    ("l_c_A", "A", "01", [("E", "A"), ("B", "A"), ("B", "A")], "C", "00",
     "The block 01 after Q: a carry of Q sends three visits E, B, B (an addition of 3) into P."),
    ("l_c_A0", "A", "00", [], "D", "01", "The block 01 restored."),
    ("l_c_E", "E", "01", [], "C", "01", "A visit in E bounces off the block 01."),
    ("l_p_E_0", "E", "1000", [], "A", "1010", "P: a digit 0 becomes 1."),
    ("l_p_B_0", "B", "1000", [], "A", "1010", "P: a digit 0 becomes 1."),
    ("l_p_E_1", "E", "1010", [("B", "A")], "A", "1000", "P: a digit 1 becomes 0, carry."),
    ("l_p_B_1", "B", "1010", [("B", "A")], "A", "1000", "P: a digit 1 becomes 0, carry."),
    ("l_a_E", "E", "10", [("B", "E"), ("A", "E"), ("B", "C")], "A", "10",
     "The block 10 after P: a carry of P sends one unit (visits B, A, B) into the next item."),
    ("l_a_B", "B", "10", [("B", "E"), ("A", "E"), ("B", "C")], "A", "10",
     "The block 10 after P: a carry of P sends one unit (visits B, A, B) into the next item."),
]

if BOUNCE:
    U = [("B", "E"), ("E", "C"), ("A", "E"), ("B", "C")]
    VAR = {"l_z_B_1u": U, "l_a_E": U, "l_a_B": U,
           "l_d_B_dd": [("E", "C"), ("A", "D"), ("E", "C"), ("A", "D")],
           "l_d_B_cdcd": [("E", "C"), ("A", "C"), ("A", "D"), ("E", "C"), ("A", "C"), ("A", "D")]}
    ROWS = [(n, q, b, VAR.get(n, c), r, a, d) for n, q, b, c, r, a, d in ROWS]
    ROWS.append(("l_d_E_01", "E", "01", [], "C", "01", "A visit in E bounces off the block 01 left by a unit's first visit."))

D3 = {0: "1 0 0", 1: "1 1 0", 2: "0 1 0"}
def nparts():
    out = []
    for x in (0, 1):
        out.append((f"n{x}t0", f"L {D3[x]}", f"L {D3[x+1]}", f"N's lowest digit {x} becomes {x+1}"))
        out.append((f"n{x}t1", f"L {D3[x]} {D3[2]}", f"L {D3[x+1]} {D3[0]}", f"N ends in {x}2: becomes {x+1}0"))
        out.append((f"n{x}tk", f"L {D3[x]} (010)^k {D3[2]} {D3[2]}", f"L {D3[x+1]} (100)^k {D3[0]} {D3[0]}", f"N ends in {x} and k+2 digits 2: carry"))
    out.append(("nov1", f"0^inf 1 0 {D3[2]}", f"0^inf 1 0 {D3[0]} {D3[0]}", "N = 2: wraps to 00 (one digit more)"))
    out.append(("nov2", f"0^inf 1 0 {D3[2]} {D3[2]}", f"0^inf 1 0 {D3[0]} {D3[0]} {D3[0]}", "N = 22: wraps to 000"))
    out.append(("novk", f"0^inf 1 0 (010)^k {D3[2]} {D3[2]}", f"0^inf 1 0 {D3[0]} {D3[0]} (100)^k {D3[0]}", "N = 2...2 (k+2 digits): wraps to k+3 zeros"))
    return out

out = [f"""import Visit

/-! # The layered right side of {M}, for any number of layers

Generated by `py/layers_gen.py`; do not edit by hand.

At an event the head is in state A on the event cell, with the base-3 counter N to its left and to its right

    0 [Z] (11 [Q] 01 [P] 10)* 11 [Q] 01 [R] 0^inf

Z: binary, digits `0010` = 0, `1010` = 1; every item: a binary word Q (digits `0001` = 0, `0101` = 1) and a binary
word P (digits `1000` = 0, `1010` = 1); the last item's P is R, followed by blank tape.  All lowest digit first, of
any width; Q and P may be empty.  (The plain cascade layout of `Cascade.lean` is one item, (C, R); the X layout of
`Xlayer*.lean` is two items, (empty, X) and (C, R); the later eras of the run add more items, see `py/wordchain.py`.
The same layout and law were first proved for 1RB---_1LC0RF_0RA0LD_1LE1LA_1RF0LF_0LC0RA; this file is generated by
this family's copy of that generator, whose rows use E where that machine uses F, A for its E as the exit of P,
and one more bounce in E in the first visit of a unit (and, for E1 = 0RE, before every increment of Q).)

**The law** (`layer_event`): from one event to the next, N + 1 and Z + 1; when Z wraps it sends one *unit* into the
first item; a unit adds 3 to Q; every wrap of Q adds 3 to P; every wrap of P sends a unit into the next item.  So a
carry is multiplied by 3 at every block `11` and every block `01`: in one line, the number
Z + 2^|Z|/3 · (Q₁ + 2^|Q₁|/3 · (P₁ + 2^|P₁|/3 · (Q₂ + …))) grows by exactly 1 per event.
The functions `incB`, `pInc`, `pUnit`, `qInc`, `qUnit`, `dU`, `evNext` compute it on the digit lists, in the order
the machine does it; `evNext` is `none` only when a carry leaves R (the overflow of R, not covered).

Proof: 23 visit rows of blocks of 1, 2 and 4 cells (each a run of the machine between nested visits, by `rfl`),
composed by induction over the digits of each word and over the list of items.  The visit relation `Vis` is the
one of `Visit.lean`. -/

namespace {NS}

open TM
"""]
for name, q, blk, calls, r, after, doc in ROWS:
    r2, a2, text = row(tr, name, q, blk, calls, doc)
    assert (r2, a2) == (r, after), (name, r2, a2)
    out.append(text)

tpl = open(os.path.join(HERE, 'Layers.lean.tpl')).read()
if BOUNCE:
    for a, b in json.load(open(os.path.join(HERE, 'layers_bounce.json'))):
        assert a in tpl, a
        tpl = tpl.replace(a, b)
out.append(tpl)

nths = []
for nn, ns, ne, nd in nparts():
    t, _ = prove(M, f"ln_{nn}", f"{ns[:-2]} D> 0 0 T", f"{ne} A> 0 T", doc=f"The end of an event: {nd}.", rotate=True,
                 count_first=True, max_seg=40)
    out.append(t)
    nths.append((nn, nd, t))
import re
out.append("/-! ## The layer law for each case of N (`layer_event` with the end of the event `ln_*`) -/\n")
for nn, nd, t in nths:
    m = re.search(r"theorem ln_\S+ (.*?) :\n\s*steps \(.*?\) ⟨(.*), cons false \(cons false \(T\)\), \.D⟩ = some ⟨(.*), cons false \(T\), \.A⟩ := by", t)
    params, l0, l1 = m.groups()
    params = params.replace("(L T : Tape)", "(L : Tape)").replace("(T : Tape)", "").strip()
    args = " ".join(re.findall(r"\((\w+)", params.replace("(L : Tape)", "(L)")))
    out.append(f"""/-- The layer law when {nd}. -/
theorem layer_event_{nn} {params} {{z : List Bool}} {{its : List Item}} {{l : Item}} {{r : List Bool × List Item × Item}}
    (hz : z ≠ []) (h : evNext z its l = some r) :
    ∃ t, steps t ⟨cons false ({l0}), cons false (enc zd z (encT its l)), .A⟩ =
      some ⟨{l1}, cons false (enc zd r.1 (encT r.2.1 r.2.2)), .A⟩ :=
  layer_event hz h (fun T => ⟨_, ln_{nn} {args} T⟩)
""")
out.append(f"end {NS}\n")
sys.stdout.write("\n".join(out))
