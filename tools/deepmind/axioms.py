"""Write the cited-axiom files: holdouts/<M>/lean/DeepMind.lean states, as a Lean `axiom` on this repository's
definitions, a result that google-deepmind/cryptids proves on its own definitions (Mathlib's Turing machines) and that
was compiled here (tools/deepmind/README.md).  Each file is added to the machine's lean/check.sh.

Nothing in this repository proves these statements.  What they rest on: DeepMind's proof (compiled, axioms propext,
Classical.choice, Quot.sound), the check that their compiled transition table is this machine's (Audit.lean), and the
translation of their statement into ours, which no proof checks: their `IsHalt (load_rle_machine% M).toBB` (blank
tape, start state A, Mathlib's semantics) is read as `TM.Halts trans (TM.blankCfg .A)` here.  `#print axioms` on any
theorem lists the `deepmind_*` axioms it uses.

For a halts-iff map (COMPILED_MAPS.json, from a cryptids checkout at the same commit), holdouts/<M>/lean/DeepMindMap.lean
copies DeepMind's `State`, `start`, `next` and the definitions `next` uses, verbatim but for `ℕ` → `Nat` (they are
plain recursive functions on numbers, no Mathlib), and states their `IsHalt target ↔ CollatzHalts next start` as
`deepmind_halts_iff`.  Machines with a halts-iff map proved here (SKIP_MAPS) get none.  That the copy computes what
theirs computes is checked by `tools/deepmind/orbits.sh`, which runs both for 120 steps and compares.

usage: python3 tools/deepmind/axioms.py COMPILED.json [COMPILED_MAPS.json CRYPTIDS_DIR]"""
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.join(HERE, "..", "..")
BASE = "https://github.com/google-deepmind/cryptids/blob/3647718/BusyBeaver/BB6/"


def namespace(M):
    with open(os.path.join(ROOT, "holdouts", M, "lean", "Machine.lean")) as f:
        return re.search(r"^namespace (\S+)", f.read(), re.M).group(1)


def add_to_check(M, fname):
    p = os.path.join(ROOT, "holdouts", M, "lean", "check.sh")
    with open(p) as f:
        lines = f.read().split("\n")
    i = max(k for k, l in enumerate(lines) if "tools/lean/check.sh" in l)
    if fname not in lines[i].split():
        lines[i] = lines[i].rstrip() + " " + fname
    with open(p, "w") as f:
        f.write("\n".join(lines))


def verdict_file(M, e):
    ns = namespace(M)
    halts = e["theorem"].endswith(".is_halt")
    name = "deepmind_halts" if halts else "deepmind_not_halts"
    stmt = "HaltsFromBlank" if halts else "¬ HaltsFromBlank"
    path = e["module"].rsplit(".", 1)[1] + ".lean"
    return name, f"""import Machine

/-!
# A cited result: DeepMind's proof that {M} {"halts" if halts else "never halts"}

**Not proved in this repository.**  `{name}` is an axiom: it states on this repository's definitions what
`{e["theorem"]}` proves in google-deepmind/cryptids
(`BusyBeaver/BB6/{path}`, commit {e["commit"]}, Lean {e["lean"]} with Mathlib), namely
`{"IsHalt" if halts else "IsNotHalt"} target` for `target = (load_rle_machine% "{M}").toBB` from the blank tape.

That theorem was compiled here on {e["date"]} (`tools/deepmind/`): it rests only on the axioms
{", ".join(e["axioms"])}, and its transition table was checked against this machine's.  The step from their
statement to this one is a translation, not a proof: their halting (Mathlib's Turing machine semantics, blank tape,
state A) is read as `TM.Halts trans (TM.blankCfg .A)`.  A proof here, or a bridge theorem between the two
semantics, would turn this axiom into a theorem with the same statement.  `#print axioms` lists `{name}` for every
theorem that uses it.  Written by `tools/deepmind/axioms.py`.
-/

namespace {ns}

/-- **Cited, not proved here**: `{e["theorem"]}` (google-deepmind/cryptids, commit {e["commit"]}). -/
axiom {name} : {stmt}

end {ns}
"""


def claim(M, e, name, halts):
    return {"level": "cited", "title": f"Available in Lean here as a cited axiom: it {'halts' if halts else 'never halts'}",
            "text": (f"<code>{name}</code> states on this repository's definitions what DeepMind's compiled theorem proves "
                     f"(<code>{'HaltsFromBlank' if halts else '&not; HaltsFromBlank'}</code>), so proofs here can build on it. "
                     "It is an axiom: nothing in this repository proves it, and the translation from DeepMind's definitions "
                     "(Mathlib's Turing machines) to ours is not checked by Lean. <code>#print axioms</code> names it in "
                     "every theorem that uses it."),
            "where": f"<code>{name}</code>, <code>lean/DeepMind.lean</code> (from <code>tools/deepmind/axioms.py</code>)"}


def add_claim(M, c):
    p = os.path.join(ROOT, "holdouts", M, "status.json")
    with open(p) as f:
        raw = f.read()
    d = json.loads(raw)
    key = re.search(r"lean/DeepMind\w*\.lean", c["where"]).group(0)
    d["claims"] = [x for x in d["claims"] if x.get("level") != "cited" or key not in x.get("where", "")]
    i = next((k for k, x in enumerate(d["claims"]) if x["level"] == "open"), len(d["claims"]))
    d["claims"].insert(i, c)
    ascii_ = not re.search(r"[^\x00-\x7f]", raw)
    indent = len(raw.split("\n")[1]) - len(raw.split("\n")[1].lstrip(" "))
    out = json.dumps(d, indent=indent, ensure_ascii=ascii_)
    if raw.endswith("\n"):
        out += "\n"
    with open(p, "w") as f:
        f.write(out)


# halts-iff maps this repository proves itself (lean/Map.lean, lean/Iff.lean, lean/DMMap.lean)
SKIP_MAPS = {"1RB1LF_0RC1RD_1LA1LD_1LE0RA_---1LC_0LA1LA", "1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE",
             "1RB1RD_1LC0RD_1RF1RB_1LE0RA_0LB0LE_---0RC", "1RB1LE_0LC0LB_1RD1LC_1RD1RA_1RF0LA_---1RE"}
# and every machine whose lean/DMMap.lean proves DeepMind's statement (tools/deepmind/dmproof.py)


def _blocks(src):
    """Top-level declarations, each with the doc comment above it."""
    out, cur = [], []
    for l in src.split("\n"):
        starts = l and not l[0].isspace() and not l.startswith(("--", "|", "-/"))
        if starts and cur and not _in_doc(cur):
            out.append("\n".join(cur))
            cur = []
        cur.append(l)
    out.append("\n".join(cur))
    return out


def _in_doc(cur):
    text = "\n".join(cur)
    return text.count("/-") > text.count("-/")


def _decl(b):
    m = re.search(r"^(?:@\[[^\]]*\]\s*)?(?:private |protected )*(def|abbrev|inductive|structure)\s+([^\s(:]+)", b, re.M)
    return m.group(2) if m else None


def extract(path):
    """`State`, `start`, `next` and every definition they use (not the tape encodings), in file order."""
    with open(path) as f:
        src = f.read()
    defs, order = {}, []
    for b in _blocks(src):
        n = _decl(b)
        if n and "Cfg" not in b and "ListBlank" not in b:
            defs[n] = b
            order.append(n)
    need, got = ["State", "start", "next"], set()
    while need:
        n = need.pop()
        if n in got or n not in defs:
            continue
        got.add(n)
        body = re.sub(r"--.*", "", re.sub(r"/-.*?-/", "", defs[n], flags=re.S))
        need += [i for i in re.findall(r"[A-Za-z_][A-Za-z_0-9']*", body) if i in defs and i not in got]
    missing = {"State", "start", "next"} - got
    if missing:
        raise ValueError(f"{path}: no {missing}")
    return "\n\n".join(defs[n].rstrip() for n in order if n in got).replace("ℕ", "Nat")


def map_file(M, e, defs):
    ns = namespace(M)
    path = e["module"].rsplit(".", 1)[1] + ".lean"
    return f"""import Machine

/-!
# A cited result: DeepMind's halts-iff map for {M}

**Not proved in this repository.**  `deepmind_halts_iff` is an axiom: it states on this repository's definitions
what `{e["theorem"]}` proves in google-deepmind/cryptids
(`BusyBeaver/BB6/{path}`, commit {e["commit"]}, Lean {e["lean"]} with Mathlib), namely
`IsHalt target ↔ CollatzHalts next start` for `target = (load_rle_machine% "{M}").toBB` from the blank tape:
the machine halts if and only if the orbit of `next` from `start` reaches `none`.

`DM.State`, `DM.start`, `DM.next` and the definitions they use are copied from that file, unchanged but for `ℕ`
written `Nat` (their docstrings describe the configuration each state stands for).  `tools/deepmind/orbits.sh` runs
this copy and DeepMind's own `next` for 120 steps from `start` and finds the same states.

The theorem was compiled here on {e["date"]} (`tools/deepmind/`): it rests only on the axioms
{", ".join(e["axioms"])}, and its transition table was checked against this machine's.  The step from their
statement to this one is a translation, not a proof: their halting (Mathlib's Turing machine semantics, blank tape,
state A) is read as `TM.Halts trans (TM.blankCfg .A)`.  A proof here (as for `1RB1RD_1LC0RD_1RF1RB_1LE0RA_0LB0LE_---0RC`,
`lean/DMMap.lean`), or a bridge theorem between the two semantics, would turn the axiom into a theorem with the same
statement.  Written by `tools/deepmind/axioms.py`.
-/

set_option autoImplicit false

namespace {ns}

namespace DM

{defs}

/-- `n` steps of `next` from `start`: DeepMind's `(Option.bind · next)^[n] (some start)` in `CollatzHalts`. -/
def orbit : Nat → Option State
  | 0 => some start
  | n + 1 => Option.bind (orbit n) next

end DM

/-- **Cited, not proved here**: `{e["theorem"]}` (google-deepmind/cryptids, commit {e["commit"]}).  The machine halts
from blank tape if and only if the orbit of DeepMind's `next` stops. -/
axiom deepmind_halts_iff : HaltsFromBlank ↔ ∃ n, (DM.orbit n).isNone = true

end {ns}
"""


def map_claim(M):
    return {"level": "cited", "title": "Available in Lean here as a cited axiom: DeepMind's halts-iff map",
            "text": ("<code>deepmind_halts_iff</code> states on this repository's definitions what DeepMind's compiled "
                     "theorem proves: the machine halts from blank tape if and only if the orbit of their map "
                     "<code>next</code> from <code>start</code> reaches <code>none</code>. The map is copied from their "
                     "file unchanged, and running the copy and theirs for 120 steps gives the same states. It is an "
                     "axiom: nothing in this repository proves it, and the translation from DeepMind's definitions "
                     "(Mathlib's Turing machines) to ours is not checked by Lean. <code>#print axioms</code> names it in "
                     "every theorem that uses it."),
            "where": "<code>deepmind_halts_iff</code>, <code>DM.next</code>, <code>lean/DeepMindMap.lean</code> (from "
                     "<code>tools/deepmind/axioms.py</code>)"}


def main(argv):
    with open(argv[0]) as f:
        compiled = json.load(f)
    for M, e in compiled.items():
        halts = e["theorem"].endswith(".is_halt")
        name, text = verdict_file(M, e)
        with open(os.path.join(ROOT, "holdouts", M, "lean", "DeepMind.lean"), "w") as f:
            f.write(text)
        add_to_check(M, "DeepMind.lean")
        add_claim(M, claim(M, e, name, halts))
        print(M, name)
    if len(argv) < 3:
        return
    with open(argv[1]) as f:
        maps = json.load(f)
    for M, e in maps.items():
        if M in SKIP_MAPS or os.path.exists(os.path.join(ROOT, "holdouts", M, "lean", "DMMap.lean")):
            continue
        mod = os.path.join(argv[2], *e["module"].split(".")) + ".lean"
        with open(os.path.join(ROOT, "holdouts", M, "lean", "DeepMindMap.lean"), "w") as f:
            f.write(map_file(M, e, extract(mod)))
        add_to_check(M, "DeepMindMap.lean")
        add_claim(M, map_claim(M))
        print(M, "deepmind_halts_iff")


if __name__ == "__main__":
    main(sys.argv[1:])
