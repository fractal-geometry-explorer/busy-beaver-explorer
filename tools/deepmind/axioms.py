"""Write the cited-axiom files: holdouts/<M>/lean/DeepMind.lean states, as a Lean `axiom` on this repository's
definitions, a result that google-deepmind/cryptids proves on its own definitions (Mathlib's Turing machines) and that
was compiled here (tools/deepmind/README.md).  Each file is added to the machine's lean/check.sh.

Nothing in this repository proves these statements.  What they rest on: DeepMind's proof (compiled, axioms propext,
Classical.choice, Quot.sound), the check that their compiled transition table is this machine's (Audit.lean), and the
translation of their statement into ours, which no proof checks: their `IsHalt (load_rle_machine% M).toBB` (blank
tape, start state A, Mathlib's semantics) is read as `TM.Halts trans (TM.blankCfg .A)` here.  `#print axioms` on any
theorem lists the `deepmind_*` axioms it uses.

usage: python3 tools/deepmind/axioms.py COMPILED.json"""
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
    d["claims"] = [x for x in d["claims"] if x.get("level") != "cited" or "DeepMind.lean" not in x.get("where", "")]
    i = next((k for k, x in enumerate(d["claims"]) if x["level"] == "open"), len(d["claims"]))
    d["claims"].insert(i, c)
    ascii_ = not re.search(r"[^\x00-\x7f]", raw)
    indent = len(raw.split("\n")[1]) - len(raw.split("\n")[1].lstrip(" "))
    out = json.dumps(d, indent=indent, ensure_ascii=ascii_)
    if raw.endswith("\n"):
        out += "\n"
    with open(p, "w") as f:
        f.write(out)


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


if __name__ == "__main__":
    main(sys.argv[1:])
