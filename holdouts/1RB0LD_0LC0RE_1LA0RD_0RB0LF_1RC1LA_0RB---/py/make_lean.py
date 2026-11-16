"""Write the visit-law Lean files of the F03 'chaotic small tape' machines that share the two-word sweeper engine.

usage: python3 py/make_lean.py py/lean_config.json lean/      (from the machine's folder)

CONFIG: {"machine", "ns", "steps", "counter": {"side", "origin", "W"}, "stream": {"side", "origin", "W"},
         "rename": {"A": "C", ...} (state names of the engine -> this machine's; identity if absent)}
Writes VisitR.lean / VisitL.lean (the mined rows, proved row by row), Counter.lean (the base-3 counter for every
size) and Stream.lean (the binary stream laws of the sibling 1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RA_0LB---, renamed).
The rows are mined by ../c/vislaws.c (compiled on the fly, or the binary named by $VISLAWS).
"""
import json, os, re, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from gen_visit2 import gen

NEED = ["B 00 ", "B 10 Ba", "B 10 Bc", "E 10 Bc", "A 01 EcAe", "E 01 ", "A 01 EcAd", "A 00 ", "E 00 ", "A 01 EcAcAd",
        "A 01 EaBaBa"]


def vislaws():
    if os.environ.get("VISLAWS"):
        return os.environ["VISLAWS"]
    import tempfile
    exe = os.path.join(tempfile.mkdtemp(), "vislaws")
    subprocess.run(["gcc", "-O2", "-o", exe, os.path.join(HERE, "..", "c", "vislaws.c")], check=True)
    os.environ["VISLAWS"] = exe
    return exe


def mine(m, steps, side, origin, W):
    out = subprocess.run([vislaws(), m, str(steps), side, str(origin), str(W)],
                         capture_output=True, text=True, check=True).stdout
    rows = [json.loads(l) for l in out.splitlines() if l.strip()]
    rows.sort(key=lambda r: (r[0], r[1], r[2]))
    return rows


def counter_file(m, ns, side, imp, rows):
    """The counter rows are q(010) -> nc, 110 ; q(110) -> nc, 100 ; q(100) calls q -> nc or c -> c, 010 ;
    q(000) -> nc, 100.  Find q, nc, c from the rows."""
    P = "Vis" if side == "R" else "VisL"
    pre = "v" if side == "R" else "w"
    q = rows[0][0]
    d = {(r[1], r[2]): r for r in rows}
    nc = d[("010", "")][3]
    c = [r for r in rows if r[1] == "100"][0][3]
    assert d[("010", "")][4] == "110" and d[("110", "")][3] == nc and d[("110", "")][4] == "100"
    assert d[("000", "")][3] == nc and d[("000", "")][4] == "100"
    assert d[("100", q + nc.lower())][3] == c and d[("100", q + c.lower())][3] == c
    sd = "right" if side == "R" else "left"
    return f"""import {imp}

/-! # The base-3 counter of {m}

Read the cells {sd} of the counter's low end in tokens of three cells, nearest cell first:
`d0 = 010`, `d1 = 110`, `d2 = 100` (digit values 0, 1, 2, lowest digit nearest the head).  A visit in state {q} adds
one: trailing 2s become 0s, the first digit that is not 2 goes up by one, and the visit comes out in state {nc} if
there was no carry, in {c} if there was.  A carry through every digit turns the blank cells beyond into a new digit 2.
For every number of digits, from the rows of `{imp}.lean`. -/

namespace {ns}

open TM

def d0 : List Bool := [false, true, false]
def d1 : List Bool := [true, true, false]
def d2 : List Bool := [true, false, false]

/-- A carry through k + 1 digits 2, given what the visit of the rest does (it must come out in {nc} or {c}). -/
theorem n_carry (k : Nat) {{x x' : Tape}} {{r : St}} (hr : r = .{nc} ∨ r = .{c}) (h : {P} .{q} x r x') :
    {P} .{q} (rep (k + 1) d2 x) .{c} (rep (k + 1) d0 x') := by
  induction k with
  | zero =>
    rcases hr with rfl | rfl
    · exact {pre}_{q}_100_{q}{nc.lower()} h
    · exact {pre}_{q}_100_{q}{c.lower()} h
  | succ k ih => exact {pre}_{q}_100_{q}{c.lower()} ih

/-- Lowest digit 0: it becomes 1, out in {nc}. -/
theorem n_inc0 (y : Tape) : {P} .{q} (app d0 y) .{nc} (app d1 y) := {pre}_{q}_010_none

/-- Lowest digit 1: it becomes 2, out in {nc}. -/
theorem n_inc1 (y : Tape) : {P} .{q} (app d1 y) .{nc} (app d2 y) := {pre}_{q}_110_none

/-- k + 1 digits 2, then a 0: the 2s become 0s and the 0 becomes 1, out in {c}. -/
theorem n_inc0_carry (k : Nat) (y : Tape) :
    {P} .{q} (rep (k + 1) d2 (app d0 y)) .{c} (rep (k + 1) d0 (app d1 y)) :=
  n_carry k (Or.inl rfl) (n_inc0 y)

/-- k + 1 digits 2, then a 1: the 2s become 0s and the 1 becomes 2, out in {c}. -/
theorem n_inc1_carry (k : Nat) (y : Tape) :
    {P} .{q} (rep (k + 1) d2 (app d1 y)) .{c} (rep (k + 1) d0 (app d2 y)) :=
  n_carry k (Or.inl rfl) (n_inc1 y)

/-- Blank tape beyond the digits becomes a digit 2. -/
theorem n_new : {P} .{q} blank .{nc} (app d2 blank) := by
  have h := @{pre}_{q}_000_none blank
  simp only [cons_false_blank] at h
  rw [show app d2 blank = cons true blank by simp [d2, cons_false_blank]]
  exact h

/-- All k + 1 digits are 2: they become 0s and a new digit 2 appears beyond them, out in {c}. -/
theorem n_overflow (k : Nat) : {P} .{q} (rep (k + 1) d2 blank) .{c} (rep (k + 1) d0 (app d2 blank)) :=
  n_carry k (Or.inl rfl) n_new

end {ns}
""", (q, nc, c)


def stream_file(m, ns, side, imp, ren):
    t = open(os.path.join(HERE, "Stream.lean.tpl")).read()
    head, body = t.split("namespace NS", 1)
    P = "Vis" if side == "R" else "VisL"
    pre = "v" if side == "R" else "w"
    body = re.sub(r"\bv_([A-F])_(\d+)_([A-Za-z]+)",
                  lambda mm: f"{pre}_{ren[mm.group(1)]}_{mm.group(2)}_" + ("none" if mm.group(3) == "none" else
                  "".join(ren[ch] if ch.isupper() else ren[ch.upper()].lower() for ch in mm.group(3))), body)
    body = re.sub(r"\.([A-F])\b", lambda mm: "." + ren[mm.group(1)], body)
    body = re.sub(r"\bVis\b", P, body)
    body = body.replace("end NS", f"end {ns}")
    # doc comments inside the body mention engine state names; replace them by a neutral note
    body = re.sub(r"/--.*?-/\n", "", body, flags=re.S)
    tok = "right" if side == "R" else "left (nearest cell first)"
    names = ", ".join(f"{k} as {v}" for k, v in ren.items() if k != v) or "the same names"
    doc = f"""import {imp}

/-! # The binary streams of {m}

The stream laws proved for the sibling 1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RA_0LB--- (its `lean/Stream.lean`), here for
this machine, from the rows of `{imp}.lean`; streams on the {tok} side, states of the sibling renamed ({names}).
Tokens of two cells: `z = 00`, `a = 10`, `c = 01`.

* `vb_even`, `vb_odd`, `ve_odd`, **the a/z stream**: a visit in (the sibling's) state B turns the first `z` into `a`
  and every second `a` before it into `z`; with digits `a z` = 0, `a a` = 1 the odd case is a binary increment.
* `m_inc`, `m_wrap`, **the counter M** (digits `z c` = 0, `c c` = 1): one visit in (the sibling's) state A adds one,
  and when M is all ones it wraps and the stream after it gets three visits.

All for every stream beyond, every context, every size. -/

namespace {ns}"""
    return doc + body


def main():
    cfg = json.load(open(sys.argv[1]))
    outdir = sys.argv[2]
    m, ns, steps = cfg["machine"], cfg["ns"], cfg["steps"]
    sd = f"{steps:,} steps"
    ren = cfg.get("rename") or {s: s for s in "ABCDEF"}
    files = {}
    cc = cfg["counter"]; sc = cfg["stream"]
    crow = mine(m, steps, cc["side"], cc["origin"], cc["W"])
    srow = mine(m, steps, sc["side"], sc["origin"], sc["W"])
    cname = "VisitR" if cc["side"] == "R" else "VisitL"
    sname = "VisitR" if sc["side"] == "R" else "VisitL"
    assert cname != sname
    files[cname + ".lean"] = gen(m, ns, cc["side"], crow, "Machine", f"the first {sd}")
    files[sname + ".lean"] = gen(m, ns, sc["side"], srow, "Machine", f"the first {sd}")
    files["Counter.lean"], info = counter_file(m, ns, cc["side"], cname, crow)
    have = {f"{r[0]} {r[1]} {r[2]}" for r in srow}
    for n in NEED:
        q, t, c = n.split(" ")
        q = ren[q]; c = "".join(ren[ch] if ch.isupper() else ren[ch.upper()].lower() for ch in c)
        assert f"{q} {t} {c}" in have, ("missing row", q, t, c)
    files["Stream.lean"] = stream_file(m, ns, sc["side"], sname, ren)
    for k, v in files.items():
        open(os.path.join(outdir, k), "w").write(v + ("\n" if not v.endswith("\n") else ""))
    json.dump({"counter_rows": crow, "stream_rows": srow, "counter_states": info},
              open(os.path.join(outdir, "rows.json"), "w"), indent=0)
    print("wrote", sorted(files), "counter (entry, no carry, carry) =", info, file=sys.stderr)


if __name__ == "__main__":
    main()
