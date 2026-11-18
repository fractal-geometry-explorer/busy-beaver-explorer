"""Write lean/Twin.lean for the ten pairs of F05 machines whose runs have the same block lists.

The two machines of a pair are the same five-state core, in the same frame and with the same start state; they differ
only in D1 (0LF or 1LF, frame A) and F0.  Both enter F only from D1, so their runs agree until D reads a 1.  This script
simulates both machines from that moment, with the cells around the head unknown, and finds the window of cells
that makes them meet again: `0 0 D>1` (two cells) for seven pairs, `1 0 0 0 D>1 1` (five cells) for the three pairs
where one machine has F0 = 0LE (frame A).  If the cell left of D is 1, both halt at once (F reads 1).  The Lean file proves this for every tape
around the window and applies `TM.halt_together` (tools/lean/TM/Resync.lean): the two machines meet a D1 entry
outside the window together, and if they never do, they halt together.

usage: python3 gen_twins.py            # writes the ten files and prints the pairs
       python3 gen_twins.py --check    # only prints the pairs and the windows
       python3 gen_twins.py --records  # also adds the pair to both machines' status.json and README.md
                                       # (claim tag "F05-twin", explainer section "f05-twin"); then build_pages.py
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import frames  # noqa: E402
import gen_family_lean as gfl  # noqa: E402

ROOT = os.path.normpath(os.path.join(HERE, "..", ".."))

PAIRS = [
    ("1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RE---", "1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LB---"),
    ("1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0LE---", "1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LA---"),
    ("1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_0RE---", "1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_1LB---"),
    ("1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_0LB---", "1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_1LD---"),
    ("1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1RE---", "1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_1LD---"),
    ("1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_0RC---", "1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_0LA---"),
    ("1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_0RE---", "1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_1RB---"),
    ("1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0RA---", "1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA1RF_0LD---"),
    ("1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0LA---", "1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_1RC---"),
    ("1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA1RF_0RC---", "1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA1RF_1RE---"),
]

# windows, as cell offsets from D's cell (negative: left); offset 0 is the 1 that D reads
W2 = {-1: 0, -2: 0}
W5 = {-1: 0, -2: 0, -3: 0, -4: 1, 1: 1}


def run(t, tape, n):
    """run frame-A table t from D on the cell 0, tape a dict of known cells; stop when a cell is unknown."""
    tape, pos, st = dict(tape), 0, "D"
    out = [(dict(tape), pos, st)]
    for _ in range(n):
        if pos not in tape:
            return out, pos
        x = t[(st, tape[pos])]
        if x is None:
            return out, "halt"
        w, d, s = x
        tape[pos] = w
        pos += 1 if d == "R" else -1
        st = s
        out.append((dict(tape), pos, st))
    return out, None


def meet(tx, ty, win):
    """(i, j): after i steps of tx and j of ty from D>1 with the window, the same configuration (not in F),
    or None.  Also checks that no configuration on the way is D reading 1 (a new segment start)."""
    a = dict(win)
    a[0] = 1
    ox, ex = run(tx, a, 200)
    oy, ey = run(ty, a, 200)
    for i in range(1, len(ox)):
        for j in range(1, len(oy)):
            if ox[i][1:] == oy[j][1:] and ox[i][0] == oy[j][0] and ox[i][2] != "F":
                for o, n in ((ox, i), (oy, j)):
                    for tp, p, s in o[1:n]:
                        assert not (s == "D" and tp.get(p) == 1)
                return i, j, ox[i][2], ox[i][1]
    return None


def pair_info(x, y):
    fx, fax, sx = frames.info(x)
    fy, fay, sy = frames.info(y)
    assert fx == fy and sx == sy, (x, y)
    tx, ty = gfl.parse(fax), gfl.parse(fay)
    for k in tx:
        if k not in (("D", 1), ("F", 0)):
            assert tx[k] == ty[k], (x, y, k)
    for win, name in ((W2, "W2"), (W5, "W5")):
        m = meet(tx, ty, win)
        if m:
            return dict(frame=fx, start=sx, fax=fax, fay=fay, win=name, meet=m)
    raise ValueError((x, y))


def conj_text(machine):
    fr, fa, st = frames.info(machine)
    txt = gfl.conj(machine, fr, st)
    return txt[:txt.index("/-- **The visit rule")].rstrip() + "\n"


def machine_block(ns, machine):
    fr, fa, st = frames.info(machine)
    return f"""
/-! ## {machine} -/

namespace {ns}

/-- The transition table of {machine}. -/
def trans : St → Bool → Option (Bool × Dir × St)
{gfl.table_rows(machine)}

/-- The configuration of its run from blank tape. -/
abbrev init : Cfg St := TM.blankCfg .A
/-- {machine} halts from blank tape. -/
abbrev HaltsFromBlank : Prop := TM.Halts trans init

namespace FA

/-- The frame-A conjugate of {machine}: {fa}. -/
def trans : St → Bool → Option (Bool × Dir × St)
{gfl.table_rows(fa)}

end FA
{conj_text(machine)}
end {ns}
"""


WIN_TEXT = {
    "W2": ("the two cells left of D are `0 0`", "c.l 0 = false ∧ c.l 1 = true",
           "`1 0 D>1`: the cell left of D is 0 and the one left of it is 1"),
    "W5": ("the tape around D is `1 0 0 0 D>1 1`", "c.l 0 = false ∧\n    ¬ (c.l 1 = false ∧ c.l 2 = false ∧ c.l 3 = true ∧ c.r 1 = true)",
           "`0 D>1` with anything else than `1 0 0 0 D>1 1` around it"),
}


def seg_proof(info):
    i, j = info["meet"][0], info["meet"][1]
    sync = f"""refine ⟨{i - 1}, {j - 1}, clean_of_chk FX notSeg notSeg_ok _ _ rfl, clean_of_chk FY notSeg notSeg_ok _ _ rfl,
          Or.inl ⟨_, ?_, rfl, rfl⟩⟩
        nofun"""
    sync2 = f"""refine ⟨{i - 1}, {j - 1}, clean_of_chk FX notSeg notSeg_ok _ _ rfl, clean_of_chk FY notSeg notSeg_ok _ _ rfl,
          Or.inl ⟨_, ?_, rfl, rfl⟩⟩
        nofun"""
    halt = """exact ⟨1, 1, clean_of_chk FX notSeg notSeg_ok _ _ rfl, clean_of_chk FY notSeg notSeg_ok _ _ rfl,
        Or.inr ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩⟩⟩"""
    head = """    obtain ⟨l, r, q⟩ := c
    obtain ⟨b0, R, rfl⟩ := tape_cell r
    obtain ⟨l0, L, rfl⟩ := tape_cell l
    obtain ⟨h1, h2⟩ := hg
    simp only at h1 h2; subst h1; subst h2
    cases l0
"""
    if info["win"] == "W2":
        return head + f"""    · obtain ⟨l1, L, rfl⟩ := tape_cell L
      cases l1
      · {sync2}
      · exact absurd ⟨rfl, rfl, rfl, rfl⟩ hb
    · {halt}
"""
    return head + f"""    · obtain ⟨l1, L, rfl⟩ := tape_cell L
      obtain ⟨l2, L, rfl⟩ := tape_cell L
      obtain ⟨l3, L, rfl⟩ := tape_cell L
      obtain ⟨r1, R, rfl⟩ := tape_cell R
      by_cases hw : (l1 = false ∧ l2 = false ∧ l3 = true ∧ r1 = true)
      · obtain ⟨rfl, rfl, rfl, rfl⟩ := hw
        {sync}
      · exact absurd ⟨rfl, rfl, rfl, hw⟩ hb
    · {halt}
"""


def file_text(x, y):
    info = pair_info(x, y)
    st = info["start"]
    good, bad_def, bad_txt = WIN_TEXT[info["win"]]
    i, j, mst, mpos = info["meet"]
    return f"""import TM.Resync

/-!
# {x} and {y}: one question for two machines

Generated by `py/gen_twins.py` in the folder of the family's first machine
(holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---); do not edit by hand.

Both machines are the F05 core in the same frame (frame {info["frame"]}), started in frame-A state {st}.  Their frame-A
conjugates `FX` = {info["fax"]} and `FY` = {info["fay"]} differ only in D1 and F0, and F is entered only by D1.  So the
two runs are the same until D reads a 1 (`Seg`).  There:

* if the cell left of D is 1, F reads it and both machines halt;
* if {good}, `FX` makes {i} steps and `FY` makes {j}, and they are in the same configuration again (state {mst}, the
  head {abs(mpos)} cell{"s" if abs(mpos) != 1 else ""} {"left of" if mpos < 0 else "right of" if mpos > 0 else "on"} D's cell), for every tape around;
* otherwise ({bad_txt}) the configuration is *bad*: the two machines may part there.

`resync` checks these three facts for every configuration, and `halt_together` applies `TM.halt_together`: the two
runs from blank tape meet a bad configuration together, and if they never do, the two machines halt together.  In
every F-event of the runs observed (to 10^200 steps), D reads 1 inside `1 0 0 0 D>1 1`, the context `fevent`
in `lean/Family.lean` proves harmless, so the observed runs never meet a bad configuration; whether the real runs never
do is the open question of both machines.  Kernel only (axioms `propext`, `Classical.choice`, `Quot.sound`; no `native_decide`).
-/

namespace Twin

open TM

/-- The states. -/
inductive St where
  | A | B | C | D | E | F
  deriving DecidableEq, Repr
{machine_block("MX", x)}{machine_block("MY", y)}
/-! ## The two frame-A tables have one question -/

abbrev FX := MX.FA.trans
abbrev FY := MY.FA.trans

/-- Not in F: the two runs are synchronised there. -/
def Syn (c : Cfg St) : Prop := c.st ≠ .F
/-- D reads 1: the two machines take different paths from here. -/
def Seg (c : Cfg St) : Prop := c.st = .D ∧ c.r 0 = true
/-- D reads 1 and the cell left of it is 0, but the window is not {good.replace("the two cells left of D are ", "").replace("the tape around D is ", "")}. -/
def Bad (c : Cfg St) : Prop := c.st = .D ∧ c.r 0 = true ∧ {bad_def}

/-- `false` exactly at the starts of segments. -/
def notSeg (c : Cfg St) : Bool := match c.st, c.r 0 with
  | .D, true => false
  | _, _ => true

theorem notSeg_ok (e : Cfg St) (h : notSeg e = true) : ¬ Bad e := by
  obtain ⟨l, r, q⟩ := e
  rintro ⟨h1, h2, -⟩
  simp only at h1 h2; subst h1
  simp [notSeg, h2] at h

/-- The two tables agree off the segments, never halt there, and every good segment closes. -/
theorem resync : Resync FX FY Syn Seg Bad where
  agree c hs hg := by
    obtain ⟨l, r, q⟩ := c
    obtain ⟨b, R, rfl⟩ := tape_cell r
    simp only [Syn, Seg] at hs hg
    cases q <;> cases b
    all_goals first | rfl | (exact absurd rfl hs) | (exact absurd ⟨rfl, rfl⟩ hg)
  live c hs hg := by
    obtain ⟨l, r, q⟩ := c
    obtain ⟨b, R, rfl⟩ := tape_cell r
    simp only [Syn, Seg] at hs hg
    cases q <;> cases b
    all_goals first | (exact absurd rfl hs) | (exact absurd ⟨rfl, rfl⟩ hg) | exact ⟨_, rfl, nofun⟩
  seg c hs hg hb := by
{seg_proof(info)}
/-- **One question.**  The frame-A runs from blank tape (in state {st}) meet a bad configuration together, and if they
never do, {x} and {y} halt together. -/
theorem halt_together :
    (NoBad FX Bad ⟨blank, blank, .{st}⟩ ↔ NoBad FY Bad ⟨blank, blank, .{st}⟩) ∧
    (NoBad FX Bad ⟨blank, blank, .{st}⟩ → (MX.HaltsFromBlank ↔ MY.HaltsFromBlank)) := by
  rw [MX.halts_iff, MY.halts_iff]
  exact TM.halt_together resync (c0 := ⟨blank, blank, .{st}⟩) nofun

end Twin
"""


# ------------------------------------------------------------------------------------------------ records

SHARED = "holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---"
GOOD_HTML = {"W2": "<code>0 0 D&gt;1</code> (the two cells left of D are 0)",
             "W5": "<code>1 0 0 0 D&gt;1 1</code>"}
BAD_HTML = {"W2": "<code>1 0 D&gt;1</code>",
            "W5": "<code>0 D&gt;1</code> with anything else around it than <code>1 0 0 0 D&gt;1 1</code>"}


def trace(t, win, n):
    a = dict(win)
    a[0] = 1
    o, _ = run(t, a, n)
    return o


def trace_html(x, y, info):
    """the two segments side by side: frame-A cells -6..3 around D's cell, the head boxed"""
    tx, ty = gfl.parse(info["fax"]), gfl.parse(info["fay"])
    win = W2 if info["win"] == "W2" else W5
    i, j = info["meet"][0], info["meet"][1]
    ox, oy = trace(tx, win, i), trace(ty, win, j)

    def row(c):
        t, p, st = c
        cells = []
        for k in range(-6, 4):
            v = t.get(k)
            sym = "?" if v is None else str(v)
            if k == p:
                cells.append(f"<b style='outline:2px solid currentColor;padding:0 2px'>{st}&gt;{sym}</b>")
            else:
                cells.append(sym)
        return " ".join(cells)

    def lab(m, fa):
        t = gfl.parse(fa)
        d1, f0 = t[("D", 1)], t[("F", 0)]
        return f"{m} (frame A: D1 = {d1[0]}{d1[1]}F, F0 = {f0[0]}{f0[1]}{f0[2]})"

    def col(o, name):
        rows = "".join(f"<tr><td>{k}</td><td><code>{row(c)}</code></td></tr>" for k, c in enumerate(o))
        return (f"<table><thead><tr><th>step</th><th>{name}: cells −6 … 3</th></tr></thead>"
                f"<tbody>{rows}</tbody></table>")
    return (f"<details><summary>The two paths from D&gt;1 to the meeting point, step by step (? = a cell neither "
            f"machine reads)</summary>{col(ox, lab(x, info['fax']))}{col(oy, lab(y, info['fay']))}</details>")


def records(x, y):
    import html as H
    import json
    info = pair_info(x, y)
    i, j, mst, mpos = info["meet"]
    for m, other in ((x, y), (y, x)):
        home = x
        lean = f"holdouts/{home}/lean/Twin.lean"
        claim = {
            "level": "kernel", "tag": "F05-twin",
            "title": "One question with its twin " + other,
            "text": (f"This machine and <code>{other}</code> are the same core in the same frame with the same start; "
                     f"they differ only in D1 and F0, and F is entered only by D1. <code>resync</code> proves, for every "
                     f"tape, that when D reads 1 the two either both halt (a 1 left of D), or meet again in the same "
                     f"configuration ({x}: {i} steps, {y}: {j}) when the tape around the head is {GOOD_HTML[info['win']]} (frame A), or the "
                     f"configuration is <em>bad</em> ({BAD_HTML[info['win']]}). <code>halt_together</code>: the two "
                     f"runs from blank tape meet a bad configuration together, and if they never do, the two machines "
                     f"halt together. Every F-event observed in the family's runs (to 10<sup>200</sup> steps) is "
                     f"inside <code>1 0 0 0 D&gt;1 1</code>, so any proof that the F-events stay of the proved "
                     f"harmless kind settles both machines at once."),
            "where": f"<code>halt_together</code>, <code>resync</code>, <code>{lean}</code>; "
                     f"<code>TM.halt_together</code>, <code>tools/lean/TM/Resync.lean</code>; "
                     f"<code>{SHARED}/py/gen_twins.py</code>"}
        sec = {"id": "f05-twin", "eyebrow": "A twin", "heading": "One question with its twin",
               "html": [
                   f"<p>The runs of this machine and of <code>{other}</code> have the same block lists at every "
                   f"left-end event the family's simulator recorded. That is not a coincidence, and it is now a "
                   f"theorem: the two tables differ only in what happens after D reads a 1 (D1 and F0), and from "
                   f"there their paths part for a few steps and meet again.</p>",
                   f"<p>In frame A, when D reads a 1: if the cell to its left is 1, F reads it and both machines halt. "
                   f"If the tape around the head is {GOOD_HTML[info['win']]}, <code>{x}</code> takes {i} steps and "
                   f"<code>{y}</code> {j}, and they are in the same configuration again, whatever the rest of the tape holds. "
                   f"Only in a <em>bad</em> configuration ({BAD_HTML[info['win']]}) can they part for good.</p>",
                   f"<p><code>halt_together</code> in <code>{lean}</code> turns this into one question for both "
                   f"machines: their runs from blank tape reach a bad configuration together, and if they never do, "
                   f"they halt together. Every F-event seen so far (to 10<sup>200</sup> steps) has the tape "
                   f"<code>1 0 0 0 D&gt;1 1</code> around it, the harmless kind proved in <code>Family.lean</code>.</p>",
                   trace_html(x, y, info)]}
        sp = os.path.join(ROOT, m, "status.json")
        spec = json.load(open(sp))
        cl = [c for c in spec["claims"] if c.get("tag") != "F05-twin"]
        k = max([n + 1 for n, c in enumerate(cl) if c.get("tag") == "F05"] or [min(3, len(cl))])
        spec["claims"] = cl[:k] + [claim] + cl[k:]
        ss = [q for q in spec["explainer"]["sections"] if q.get("id") != "f05-twin"]
        k = next((n + 1 for n, q in enumerate(ss) if q.get("id") == "f05"), 0)
        spec["explainer"]["sections"] = ss[:k] + [sec] + ss[k:]
        note = (f"<b>Twin.</b> Proved in Lean to share one question with <code>{other}</code>: both runs meet a "
                f"bad F-entry together, and if they never do, the two machines halt together.")
        spec["verdict"] = [v for v in spec.get("verdict", []) if not v.startswith("<b>Twin.</b>")] + [note]
        line = f"python3 {SHARED}/py/gen_twins.py --check    # the ten twin pairs and their windows"
        spec["check"] = [c for c in spec.get("check", []) if "gen_twins.py" not in c] + [line]
        with open(sp, "w") as f:
            json.dump(spec, f, indent=1, ensure_ascii=False)
            f.write("\n")
        good = H.unescape(GOOD_HTML[info["win"]].replace("<code>", "`").replace("</code>", "`"))
        bad = H.unescape(BAD_HTML[info["win"]].replace("<code>", "`").replace("</code>", "`"))
        block = "\n".join([
            "<!-- F05 twin -->", "", "## Twin: one question with " + other, "",
            f"This machine and [`{other}`](../{other}/README.md) are the same core in the same frame with the same "
            f"start; they differ only in D1 and F0. When D reads a 1 (frame A), both halt if the cell to its left is "
            f"1; with {good} around the head they meet again in the same configuration (`{x}`: {i} steps, `{y}`: {j}), for "
            f"every tape; otherwise ({bad}) the configuration is *bad*. "
            f"`halt_together` in [`lean/Twin.lean`](../{home}/lean/Twin.lean) (kernel, using "
            f"`TM.halt_together` from `tools/lean/TM/Resync.lean`): the two runs from blank tape meet a bad "
            f"configuration together, and if they never do, the machines halt together. Every F-event observed in "
            f"the family's runs (to 10^200 steps) has `1 0 0 0 D>1 1` around it, so a proof that the F-events stay "
            f"harmless settles both. See also [EQUIVALENCES.md](../EQUIVALENCES.md).", "",
            "<!-- end F05 twin -->"])
        q = os.path.join(ROOT, m, "README.md")
        text = open(q).read()
        a, b = "<!-- F05 twin -->", "<!-- end F05 twin -->"
        if a in text:
            text = text[:text.index(a)] + block + text[text.index(b) + len(b):]
        elif "<!-- end F05 -->" in text:
            e = text.index("<!-- end F05 -->") + len("<!-- end F05 -->")
            text = text[:e] + "\n\n" + block + text[e:]
        else:
            text = text.rstrip("\n") + "\n\n" + block + "\n"
        with open(q, "w") as f:
            f.write(text)


if __name__ == "__main__":
    for x, y in PAIRS:
        info = pair_info(x, y)
        print(x, y, info["frame"], info["start"], info["win"], info["meet"])
        if "--check" not in sys.argv:
            path = os.path.join(ROOT, x, "lean", "Twin.lean")
            with open(path, "w") as f:
                f.write(file_text(x, y))
        if "--records" in sys.argv:
            records(x, y)
