#!/usr/bin/env python3
"""Rank the undecided holdouts by how close each one is to being decided, and say what the next concrete step is.

Reads what the repository already records about each machine (the index rows of build_pages.py, every status.json,
families.json, the Collatz triage of tools/collatz/triage.json and the number-theory ranking of
tools/number-theory/ranking.json), puts each undecided machine on one rung of a ladder of "what is left", adjusts the
score for the work already proved, and writes

  holdouts/ranking.json            the ranking (one record per undecided machine) and the top attacks
  holdouts/RANKING.md              the top attacks and the method, for reading on GitHub
  pages/holdouts/ranking.html      the sortable page

The score is a judgement computed from recorded facts, not a probability and not a result. Run:
  python3 holdouts/rank.py
"""
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(HERE)
sys.path.insert(0, HERE)
import build_pages  # noqa: E402
import build_overview  # noqa: E402

ASOF = "21 November 2026"

# The ladder: what is left before the machine is decided. Base scores are on a 0-100 scale.
STAGES = {
    "outside": (92, "Outside proof to compile", "A complete outside proof exists; only checking it is left."),
    "reported": (80, "Halt reported elsewhere", "Another group reports the halting step; a checked proof of it is left."),
    "gap": (62, "One named gap", "A Lean reduction covers every case but one or two named ones."),
    "finite": (46, "Finite or inequality question", "The macro model is proved; what is left is one invariant or inequality with no number theory in sight."),
    "hunt": (36, "Halt hunt", "An exact macro simulator exists and halting looks plausible; a long run could find the halt."),
    "model": (25, "Model partly proved", "Part of the macro structure is proved; the rule that decides halting is not."),
    "number": (14, "Collatz-type question", "Halting is reduced to an orbit of an explicit map that behaves like a Collatz problem."),
    "decode": (10, "Not decoded yet", "The behaviour is described but its rules are not decoded."),
    "cryptid": (5, "Cryptid", "A community cryptid: an open number-theory problem."),
}
ORDER = list(STAGES)

ROUTE = {"halt": "halting", "nonhalt": "non-halting", "either": "either"}
WORK = {"compute": "compute", "lean": "Lean proof", "search": "solver search", "research": "new idea",
        "decode": "decoding"}

# Families (families.json ids) -> (stage, route, work) by default.
FAMILY_DEFAULT = {
    "R00": ("outside", "halt", "compute"),
    "R01": ("number", "nonhalt", "research"),
    "R02": ("finite", "nonhalt", "search"),
    "R03": ("model", "either", "lean"),
    "R04": ("hunt", "halt", "compute"),
    "R05": ("model", "nonhalt", "lean"),
    "R06": ("hunt", "halt", "compute"),
    "R07": ("finite", "either", "lean"),
    "R08": ("model", "either", "lean"),
    "R09": ("model", "either", "lean"),
    "R10": ("hunt", "halt", "compute"),
    "R11": ("hunt", "halt", "compute"),
    "R12": ("decode", "either", "decode"),
    "R13": ("model", "either", "research"),
    "R14": ("decode", "either", "decode"),
    "R15": ("number", "either", "research"),
}

# Collatz triage bucket (tools/collatz/triage.json) -> stage for R15 machines.
COLLATZ = {"external": "outside", "hunt": "hunt", "prove-map": "model", "number-theory": "number", "decode": "decode"}

PASCAL_GAP = ("Prove the two right-turn cases Lean does not cover yet: an even head block meeting a walled zone, and "
              "the crossing phase (the block-lengths-mod-4 summary that the abstraction in py/absz.py lacks). With "
              "them the observed 2-cell-letter invariant becomes a theorem and the machine never halts.")

R08_NEXT = ('Prove a bound on the speed of the front of the cascade (measured: about 3.3 cells per doubling of the time); that would turn the window bounds into astronomically large no-halt bounds, but a decision needs a new idea about what the old zone does once the disturbance from the new zone reaches it.')

# Machine-specific judgements, read from each machine's README and the latest pull requests (up to #348).
OVERRIDES = {
    # Vampire family orbit O2 (its triage record predates the outside report).
    "1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LC---": dict(
        stage="reported", route="halt", work="compute",
        why="Vampire family, orbit O2: Thomas Reus's repository reports a halt at Bell 731,899,010,932 (two computers); Lean proves the halts-iff for orbits inside the 99-context table.",
        next="Run bb6-vampire-family/c/orbit.c to the reported halting pass with context counting, regenerate the table, then evaluate a chunked (2-adic) check in Lean with native_decide on a large machine."),
    # R05, running parity (Pascal's triangle mod 2).
    "1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF": dict(
        stage="gap", route="nonhalt", work="lean",
        why="Lean proves one bounce is one row of Pascal's triangle mod 2 (Lucas), that an odd head block halts, and absorption and walled bounces (PR 348). Every right turn is covered except two cases.",
        next=PASCAL_GAP),
    "1RB0LE_1RC1RB_1RD0RA_0RE---_1LF1LA_1LA1LF": dict(
        stage="gap", route="nonhalt", work="lean",
        why="Same table as 1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF, renamed; Pascal.lean and Lucas.lean are ported (py/port_pascal.py).",
        next="Port Absorb.lean as Pascal.lean was ported, then the same two cases: " + PASCAL_GAP[0].lower() + PASCAL_GAP[1:]),
    "1RB1RA_1LC0RF_1LD1LC_1LE0LB_0LF---_1RA1RB": dict(
        stage="finite", route="nonhalt", work="lean",
        why="Mirrored start of the Pascal table: every theorem there is about the table, so it applies after exchanging the tape sides; the 2-cell-letter invariant holds for 10^9 steps.",
        next="Port Pascal.lean, Lucas.lean and Absorb.lean with the tape sides exchanged, then close the same two cases as the Pascal machine."),
    "1RB1RC_1RC1RB_1LD0RA_1LE1LD_1LF0LC_0LA---": dict(
        stage="finite", route="nonhalt", work="lean",
        why="Mirrored start of the Pascal table: every theorem there is about the table, so it applies after exchanging the tape sides; the 2-cell-letter invariant holds for 10^9 steps.",
        next="Port Pascal.lean, Lucas.lean and Absorb.lean with the tape sides exchanged, then close the same two cases as the Pascal machine."),
    "1RB0RE_1RC0RC_1LD---_0LB1LE_1RF0LD_1RA1RF": dict(
        stage="finite", route="nonhalt", work="lean",
        why="Slowed-down twin of the Pascal machine: Lean (Twin.lean) proves it follows that machine step for step up to a break and neither halts if no break comes.",
        next="Once the Pascal machine is proved non-halting, prove that no break comes (the twin's halt F> 0 0 1 1 is not the Pascal machine's)."),
    "1RB1LB_1LC0RD_0LE1LA_0RF1RA_1LE0LA_---0RB": dict(
        stage="finite", route="nonhalt", work="lean",
        why="Rule 102 machine: Lean proves the round trip is rule 102 for every length, its Lucas closed form, and that the danger pattern y 10 y^n 0 halts (PR 348).",
        next="Show the run never builds the danger pattern: a gap reaches all y only if it is a row of Pascal's triangle mod 2, so bound which gaps the defect jumps create."),
    # Number-theory tier A: no number theory needed.
    "1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC": dict(
        stage="finite", route="nonhalt", work="lean",
        why="Wall stack: the stack rules are proved in Lean (PR 344); a negative count needs a 2-adic coincidence, and the reachable walls get at most 10% of the way there.",
        next="Prove an invariant on the stack (each counter far above the one below, e.g. at least 5 times), which with the Lean stack rules gives non-halting."),
    # F02 pair: one inequality on a proved model.
    "1RB0LE_0LC0RA_1LE0RD_0RB---_0LF0LD_1LA0LF": dict(
        stage="finite", route="nonhalt", work="lean",
        why="Binary counter with doublers: a tape with one defect cannot halt, and no halt in 100,000 rounds (and to 2^18264 steps for the variant pair).",
        next="Prove that every travelling defect disappears before the next round (one inequality on the irregular digits), then the round map in Lean."),
    "1RB0LF_1LC1RC_0RA0LD_0LE1RE_0RF0LC_1RC---": dict(
        stage="finite", route="nonhalt", work="lean",
        why="Binary counter with doublers, variant of 1RB0LE_0LC0RA_1LE0RD_0RB---_0LF0LD_1LA0LF: a tape with one defect cannot halt.",
        next="Prove that every travelling defect disappears before the next round, as for its variant."),
    # R08, the four leftmost-zone machines. The zone reduction and the two-zone cascade are proved (halts_iff_zone,
    # Cascade.lean, Window.lean; Shield.lean for 1RB0RB_1RC1RA_0LD1LC_0RA1LE_1LF0LC_---1LA), so what is left is the
    # orbit of an explicit, pseudo-random cascade of one-bit cells.
    "1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA": dict(
        stage="number", route="either", work="research",
        why="Leftmost-zone machine: Lean proves the zone reduction (the block of words enters only mod 3), halts iff the zone orbit halts, and that the orbit is a cascade of one-bit cells; windows of the cascade give no halt in 1.5·10^39 steps. The disturbance from the new zone reaches the old zone only after about 10^860 sweeps (extrapolated), and nothing predicts what it does there.",
        next=R08_NEXT),
    "1RB0RB_1LC1RA_1LF0LD_0LE1LD_1RA1LC_---1LA": dict(
        stage="number", route="either", work="research",
        why="One of the four leftmost-zone machines (see 1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA): the zone reduction and the two-zone cascade are proved in Lean.",
        next=R08_NEXT),
    "1RB0RB_1RC1RA_0LD1LC_0RA1LE_1LF0LC_---1LA": dict(
        stage="number", route="either", work="research",
        why="One of the four leftmost-zone machines (see 1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA): the zone reduction and the two-zone cascade are proved in Lean. Lean also proves the stranded block shields the old zone (Shield.lean).",
        next=R08_NEXT),
    "1RB1LD_1RC0RC_1LD1RB_1LF0LE_0LA1LE_---1LB": dict(
        stage="number", route="either", work="research",
        why="One of the four leftmost-zone machines (see 1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA): the zone reduction and the two-zone cascade are proved in Lean.",
        next=R08_NEXT),
}

# The recommended attacks, each a group of machines one piece of work would settle. 'pick' selects members.
ATTACKS = [
    dict(key="pr60", title="Finish compiling busycoq PR 60",
         pick=lambda r: r["stage"] == "outside",
         route="halt", work="compute",
         what="Two complete Rocq halting proofs (credited to Yeyito on the bbchallenge wiki). The framework files compile and sample jobs pass; what is left "
              "is about 555 core-hours of native_compute jobs, now running in shards. A finished run moves both machines "
              "to decided.",
         need="Core-hours (a large machine would finish it in days)."),
    dict(key="vampire", title="Prove the reported vampire-family halts",
         pick=lambda r: r["stage"] == "reported",
         route="halt", work="compute",
         what="Seven machines on four orbits. Lean already proves each halts iff its orbit of an explicit map reaches a "
              "halting context, and Thomas Reus's repository reports the halts at Bell 7.3·10^11 to 2.0·10^12. Left: "
              "list the contexts up to the halt (one long orbit.c run per orbit), and a chunked 2-adic check written "
              "in Lean with a soundness proof, evaluated by native_decide.",
         need="One large-memory machine for the orbit runs (the numbers reach 7·10^11 bits) and the Lean evaluation."),
    dict(key="pascal", title="Close the Pascal machines' last two cases",
         pick=lambda r: r["m"] in ("1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF", "1RB0LE_1RC1RB_1RD0RA_0RE---_1LF1LA_1LA1LF",
                                   "1RB1RA_1LC0RF_1LD1LC_1LE0LB_0LF---_1RA1RB", "1RB1RC_1RC1RB_1LD0RA_1LE1LD_1LF0LC_0LA---",
                                   "1RB0RE_1RC0RC_1LD---_0LB1LE_1RF0LD_1RA1RF"),
         route="nonhalt", work="lean",
         what="Lean proves a bounce is a row of Pascal's triangle mod 2 and covers every right turn except an even head "
              "block meeting a walled zone and the crossing phase. Closing those makes the observed 2-cell-letter "
              "invariant a theorem: the two same-start machines never halt, the two mirrored starts follow by porting, "
              "and the slowed-down twin needs one more no-break argument.",
         need=""),
    dict(key="r02", title="Automaton search on the clock-and-word maps (R02)",
         pick=lambda r: r["fam"] == "R02",
         route="nonhalt", work="search",
         what="The clock lemma is in Lean for six tables. Left is one finite-state question per machine: a regular "
              "language of words that the word map P keeps and that never triggers the halting rebuild. A SAT search on "
              "the word alone is far smaller than the whole-tape search that failed.",
         need="Solver time (many CPU-hours of SAT, easy to parallelise)."),
    dict(key="wallstack", title="Stack invariant for the wall-stack machine",
         pick=lambda r: r["m"] == "1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC",
         route="nonhalt", work="lean",
         what="Ranked first of the 40 map-reduced machines because no number theory is needed: the stack rules are in "
              "Lean, and an invariant that keeps each counter far above the one below would finish it.",
         need=""),
    dict(key="countdown", title="Halt hunts on the countdown counters (R04, R11)",
         pick=lambda r: r["fam"] in ("R04", "R11"),
         route="halt", work="compute",
         what="Base-4 and ternary odometers with countdown timers. Short-timer tapes of this shape are proved to halt, "
              "and this kind of family gave half the decisions of the week of 13 November. Exact odometer jumps (the "
              "PR 83 / 89 method) to the first top-level overflow; the collapse pair has an exact cycle law already.",
         need="Long CPU runs, one machine each."),
    dict(key="r08", title="Front speed of the cascade for the four R08 machines",
         pick=lambda r: r["m"] in ("1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA", "1RB0RB_1LC1RA_1LF0LD_0LE1LD_1RA1LC_---1LA",
                                   "1RB0RB_1RC1RA_0LD1LC_0RA1LE_1LF0LC_---1LA", "1RB1LD_1RC0RC_1LD1RB_1LF0LE_0LA1LE_---1LB"),
         route="either", work="research",
         what="The leftmost-zone reduction and the two-zone cascade are proved in Lean; halting is one explicit cascade "
              "of one-bit cells. A bound on the speed of the front (measured: 3.3 cells per doubling) would give huge "
              "no-halt bounds; deciding needs a new idea about the old zone once the front reaches it.",
         need=""),
    dict(key="xor", title="Rule 102 machine: no danger pattern",
         pick=lambda r: r["m"] == "1RB1LB_1LC0RD_0LE1LA_0RF1RA_1LE0LA_---0RB",
         route="nonhalt", work="lean",
         what="The round trip is rule 102 in Lean and the danger pattern is proved to halt. A gap can reach all y only if "
              "it is a row of Pascal's triangle mod 2, so what is left is to bound the gaps that the defect jumps make.",
         need=""),
    dict(key="r07", title="Rebuild maps and the wall invariant (R07)",
         pick=lambda r: r["fam"] == "R07",
         route="either", work="lean",
         what="Up/down counters and two binary counters with rebuilds. The rebuilds are explicit closed maps (checked, "
              "not proved); prove them in Lean and extend the PR 57/58 wall invariant to rebuilds that read only part of "
              "the counter. What remains after that is a number-theoretic inequality.",
         need=""),
    dict(key="doublers", title="Binary counters with doublers: defects die out",
         pick=lambda r: r["m"] in ("1RB0LE_0LC0RA_1LE0RD_0RB---_0LF0LD_1LA0LF", "1RB0LF_1LC1RC_0RA0LD_0LE1RE_0RF0LC_1RC---"),
         route="nonhalt", work="lean",
         what="A tape with one travelling defect cannot halt. Prove that every defect disappears before the next round "
              "(one inequality on irregular digits) and the pair is non-halting.",
         need=""),
]


GENERIC_NEXT = {
    "decode": "Decode the macro rules: find the configurations that recur at the tape ends (tools/py word view and "
              "invariant finder), write them as shift rules for the symbolic prover to check in Lean, and locate where "
              "the halting configuration could come from",
    "model": "Find the rule that decides halting inside the proved macro model, prove it in Lean, and run the model "
             "exactly (accelerated) to test it",
    "number": "None beyond number theory; run the proved map far with big integers in case it halts",
    "cryptid": "None beyond number theory; run the proved map far with big integers in case it halts",
}


def load(path):
    with open(os.path.join(REPO, path)) as f:
        return json.load(f)


def strip(s):
    s = re.sub(r"<sup>([^<]*)</sup>", r"^\1", s or "")
    s = re.sub(r"<[^>]+>", "", s)
    return s.replace("&middot;", "·").replace("&times;", "×").replace("&amp;", "&").strip()


NEXT_HEAD = re.compile(r"^## (Next steps|Open, and next steps|Open, next steps|Open: what remains)\s*$", re.M | re.I)


def readme_next(folder):
    """The first item of the README's next-steps section, as plain text (None if there is none)."""
    p = os.path.join(REPO, folder, "README.md")
    if not os.path.exists(p):
        return None
    with open(p) as f:
        md = f.read()
    m = NEXT_HEAD.search(md)
    if not m:
        return None
    body = md[m.end():].split("\n## ")[0].strip()
    items = re.split(r"\n(?=\s*(?:[-*]|\d+\.)\s)|\n\s*\n", body)
    for it in items:
        t = re.sub(r"^\s*(?:[-*]|\d+\.)\s+", "", it.strip())
        t = re.sub(r"\[([^\]]+)\]\([^)]+\)", r"\1", t)
        t = re.sub(r"\s+", " ", t.replace("`", "").replace("**", "")).strip()
        if len(t) > 20 and not t.startswith("|"):
            if len(t) > 420:
                t = t[:417].rsplit(" ", 1)[0] + " ..."
            return t
    return None


def index_rows():
    triage = load("holdouts/triage.json")
    known = {k: v for k, v in load("holdouts/known.json").items() if not k.startswith("_")}
    spec_by = {s["machine"]: s for _, s in build_pages.specs()}
    return build_pages.index_rows(triage, known, spec_by), spec_by


def spec_for(r, spec_by):
    s = spec_by.get(r["m"])
    if s:
        return s
    p = os.path.join(REPO, r["f"], "status.json")
    if os.path.exists(p):
        with open(p) as f:
            return json.load(f)
    return {}


def rank():
    rows, spec_by = index_rows()
    fams = load("holdouts/families.json")
    fam_by_id = {f["id"]: f for f in fams["families"]}
    set_of = {}
    for f in fams["families"] + fams["residual"]:
        for m in f["machines"]:
            set_of[m["m"]] = m.get("set", "")
    collatz = {x["m"]: x for x in load("tools/collatz/triage.json")}
    numth = {x["m"]: x for x in load("tools/number-theory/ranking.json")}

    undecided = [r for r in rows if r["st"] in ("open", "cryptid", "pr")]
    und_set = {}
    for r in undecided:
        und_set.setdefault(set_of.get(r["m"], ""), []).append(r["m"])

    out = []
    for r in undecided:
        M = r["m"]
        s = spec_for(r, spec_by)
        claims = s.get("claims", [])
        kern = sum(1 for c in claims if c.get("level") == "kernel")
        fam = r["fm"] or ""
        fam_info = fam_by_id.get(fam, {})
        stage, route, work = FAMILY_DEFAULT.get(fam, ("decode", "either", "decode"))
        why, nxt = "", ""
        summary = strip(r["sum"] or r["k"])
        ct = collatz.get(M)
        nt = numth.get(M)

        if fam not in FAMILY_DEFAULT:  # residual F01-F11
            low = summary.lower()
            if re.search(r"halts iff|halts if and only if", low) and r["mt"]:
                stage, route, work = "number", "either", "research"
            elif kern >= 6 or r["mt"]:
                stage, route, work = "model", "either", "lean"
            else:
                stage, route, work = "decode", "either", "decode"
        if fam == "R05":
            stage = "model"
        if ct:
            stage = COLLATZ.get(ct.get("bucket"), stage)
            if ct.get("bucket") == "hunt" and "reports a halt" in (ct.get("odds") or ""):
                stage, route, work = "reported", "halt", "compute"
                why = "Vampire family: " + strip(ct.get("odds"))
            elif ct.get("bucket") == "hunt" and ct.get("outlook") == "probviously-nonhalting":
                stage = "number"
            elif ct.get("bucket") == "hunt":
                route, work = "halt", "compute"
            elif ct.get("bucket") == "prove-map":
                work = "lean"
                if ct.get("outlook") == "probviously-nonhalting":
                    stage = "number"
            elif ct.get("bucket") == "external":
                route = "halt"
            nxt = strip(ct.get("next"))
        if nt and not nxt:
            nxt = strip(nt.get("next"))
            if nt.get("tier") in ("A", "B") and stage == "number":
                stage = "model"
        if r["st"] == "pr":
            stage, route, work = "outside", "halt", "compute"
            nxt = ("Finish the native_compute jobs of busycoq PR 60 for this machine (the framework compiles and "
                   "sample jobs pass; the two machines need about 555 core-hours together), then record the decision.")
        crypt = bool(r["cr"]) or (r["dm"] or {}).get("k") == "cryptid"
        if crypt and stage in ("number", "decode", "model") and r["st"] != "pr":
            stage = "cryptid"

        o = OVERRIDES.get(M)
        if o:
            stage, route, work = o["stage"], o["route"], o["work"]
            why, nxt = o.get("why", why), o.get("next", nxt)

        if not nxt:
            nxt = readme_next(r["f"]) or ""
        if not nxt:
            nxt = fam_info.get("short") or GENERIC_NEXT.get(stage, GENERIC_NEXT["decode"])
        nxt = nxt.rstrip(".") + "."
        nxt = nxt[0].upper() + nxt[1:]
        if not why:
            why = summary

        base = STAGES[stage][0]
        progress = max(0, min(kern - 3, 9)) * 0.8  # kernel claims beyond the generated three
        if r["mt"] == 1:
            progress += 3
        elif r["mt"] == 2:
            progress += 1.5
        if r["bl"] and r["bl"] > 7:
            progress += 1.5
        if (r["dm"] or {}).get("h") == "iff":
            progress += 1
        progress = min(progress, 10)
        penalty = 3 if crypt and stage not in ("outside", "reported", "cryptid") else 0
        mates = len(und_set.get(set_of.get(M, ""), [])) if set_of.get(M) else 1
        together = 2 if mates >= 4 else (1 if mates >= 2 else 0)
        score = round(max(1, min(99, base + progress + together - penalty)), 1)

        out.append({
            "m": M, "id": r["id"], "fam": fam, "famname": fam_info.get("name", ""), "set": set_of.get(M, ""),
            "mates": mates, "stage": stage, "score": score, "route": route, "work": work,
            "kernel": kern, "map": ["", "iff", "conditional"][r["mt"]], "bound": r["bl"],
            "cryptid": crypt, "name": r["n"], "tc": r["tc"], "why": why, "next": nxt,
            "x": r["x"], "p": r["p"], "folder": r["f"],
        })

    out.sort(key=lambda x: (-x["score"], ORDER.index(x["stage"]), x["m"]))
    for i, x in enumerate(out, 1):
        x["rank"] = i

    attacks = []
    for a in ATTACKS:
        ms = [x for x in out if a["pick"](x)]
        attacks.append({"key": a["key"], "title": a["title"], "route": a["route"], "work": a["work"],
                        "what": a["what"], "need": a["need"], "machines": [x["m"] for x in ms],
                        "best": min((x["rank"] for x in ms), default=None)})
    attacks.sort(key=lambda a: (a["best"] or 10**6, -len(a["machines"])))
    return out, attacks


def write_md(out, attacks):
    from collections import Counter
    c = Counter(x["stage"] for x in out)
    L = [f"# Ranking the undecided holdouts by closeness to a decision ({ASOF})", "",
         f"All **{len(out)}** holdouts that are undecided here (open, cryptid, or covered only by an outside proof not yet "
         "compiled), ranked by how close each is to being decided and what the next concrete step is, so that new "
         "compute and proof work goes to the likeliest wins. Written by [`rank.py`](rank.py) from what the repository "
         "records about each machine; machine-readable in [`ranking.json`](ranking.json); sortable page: "
         "[`pages/holdouts/ranking.html`](../pages/holdouts/ranking.html). The score is a judgement, not a probability "
         "and not a result.", "",
         "## How the score is made", "",
         "Each machine is put on one rung of a ladder of *what is left*, which sets the base score, and then gets up to "
         "10 points for work already proved (kernel-checked Lean claims beyond the three every folder starts with, a "
         "halts-iff map, a Lean no-halt bound past 10^7 steps) and up to 2 for undecided machines on the same table set "
         "(one proof often carries over). Cryptids off the halting route lose 3. The rung comes from the machine's "
         "family (`families.json`), the Collatz triage bucket (`tools/collatz/triage.json`), the number-theory tier "
         "(`tools/number-theory/ranking.json`) and, for 15 machines, a judgement read from their README after the "
         "latest pull requests (`OVERRIDES` in `rank.py`).", "",
         "| rung | base | machines | meaning |", "|---|---:|---:|---|"]
    for k, (b, label, mean) in STAGES.items():
        L.append(f"| {label} | {b} | {c.get(k, 0)} | {mean} |")
    L += ["", "## Top 10 recommended attacks", "",
          "Each attack is one piece of work that would settle the machines listed with it. Ordered by the best-ranked "
          "machine it settles, then by how many it settles.", ""]
    for i, a in enumerate(attacks, 1):
        L.append(f"{i}. **{a['title']}** ({len(a['machines'])} machine{'s' if len(a['machines']) != 1 else ''}, "
                 f"{ROUTE[a['route']]}, {WORK[a['work']]}). {a['what']}" + (f" *Resource:* {a['need']}" if a["need"] else ""))
        for m in a["machines"]:
            L.append(f"   - [`{m}`]({m}/README.md)" if os.path.isdir(os.path.join(HERE, m)) else f"   - `{m}`")
    L += ["", "## The 40 closest machines", "", "| rank | machine | score | what is left | route | next step |",
          "|---:|---|---:|---|---|---|"]
    for x in out[:40]:
        L.append(f"| {x['rank']} | `{x['m']}` | {x['score']} | {STAGES[x['stage']][1]} | {ROUTE[x['route']]} | "
                 f"{x['next'].replace('|', '/')} |")
    L += ["", f"The other {len(out) - 40} are in the page and in `ranking.json`.", ""]
    with open(os.path.join(HERE, "RANKING.md"), "w") as f:
        f.write("\n".join(L))


CSS = r"""
.wrap{max-width:1400px}
.ladder{display:grid;gap:6px}
.lrow{display:grid;grid-template-columns:minmax(0,15rem) minmax(0,1fr) 3rem;gap:10px;align-items:center;font-size:.85rem}
.lrow .bar{height:14px;background:var(--link);border-radius:3px;min-width:2px}
.lrow .num{font:500 .8rem var(--mono);text-align:right;color:var(--muted)}
.attacks{display:grid;gap:12px;grid-template-columns:repeat(auto-fit,minmax(320px,1fr))}
.att{border:1px solid var(--rule);border-radius:8px;padding:12px;display:grid;gap:8px;align-content:start;background:var(--paper)}
.att h3 b{font-family:var(--mono);color:var(--muted);margin-right:6px}
.att p{font-size:.88rem}
.att .ml{font-family:var(--mono);font-size:.7rem;display:grid;gap:2px;overflow-wrap:anywhere}
.att .ml a{color:var(--link)}
.att .rs{font-size:.82rem;color:var(--muted)}
.tw{overflow-x:auto;border:1px solid var(--rule);border-radius:8px}
table{border-collapse:collapse;width:100%;font-size:.82rem;background:var(--surface)}
th,td{padding:6px 8px;border-bottom:1px solid var(--rule);text-align:left;vertical-align:top}
th{position:sticky;top:0;background:var(--sunk);font:700 .7rem var(--mono);text-transform:uppercase;letter-spacing:.05em;cursor:pointer;white-space:nowrap;user-select:none}
th[aria-sort=ascending]::after{content:" ▲"} th[aria-sort=descending]::after{content:" ▼"}
td.m{font-family:var(--mono);font-size:.72rem;min-width:22rem;overflow-wrap:anywhere}
td.n{text-align:right;width:1%;font-family:var(--mono);white-space:nowrap}
td.nx{min-width:22rem;max-width:42rem}
td.wy{min-width:18rem;max-width:34rem;color:var(--muted)}
.sc{display:inline-block;min-width:2.6rem;padding:1px 6px;border-radius:4px;color:#fff;font:700 .75rem var(--mono);text-align:center}
.cols{font-size:.85rem;color:var(--muted)}
.hide-why td.wy,.hide-why th.wy{display:none}
select{padding:6px 8px;border:1px solid var(--rule);border-radius:6px;background:var(--paper);color:var(--ink);font:13px var(--body)}
@media (max-width:640px){.lrow{grid-template-columns:minmax(0,1fr) 2.6rem}.lrow .bar{grid-column:1/-1;grid-row:2}}
"""

BODY = r"""
<header style="display:grid;gap:10px">
 <p class="crumb"><a href="../index.html">Busy Beaver Explorer</a> / <a href="index.html">holdouts</a> / closest to solved</p>
 <h1>Which holdouts are closest to being solved</h1>
 <p>Every one of the __N__ holdouts still undecided here (__ASOF__), ranked by how close it is to a decision and what
 the next concrete step is, so new compute and proof work goes to the likeliest wins. A machine's score starts from
 what is left to do (the rungs below) and gains up to 10 points for work already proved in Lean and 2 for undecided
 machines on the same table, which one proof often settles together. The score is a judgement computed from what the
 repository records, <b>not a probability and not a result</b>.</p>
 <p>See also the <a href="families.html">families</a>, the <a href="collatz-family.html">Collatz triage</a>, the
 <a href="number-theory.html">number-theory bucket</a> and the <a href="index.html">holdout map</a>.</p>
</header>

<section class="panel">
 <h2>Top 10 recommended attacks</h2>
 <p>Each card is one piece of work that would settle the machines listed on it.</p>
 <div class="attacks" id="attacks"></div>
</section>

<section class="panel">
 <h2>What is left, machine by machine</h2>
 <div class="ladder" id="ladder"></div>
</section>

<section class="panel">
 <h2>The ranking</h2>
 <div class="controls">
  <input type="search" id="q" placeholder="Search a machine, id, family or step" aria-label="search the ranking">
  <select id="fs" aria-label="what is left"><option value="">every rung</option></select>
  <select id="fr" aria-label="route"><option value="">any route</option><option value="halt">halting</option><option value="nonhalt">non-halting</option><option value="either">either</option></select>
  <button class="chip" id="whytog" aria-pressed="true">show why</button>
 </div>
 <p class="cols">Click a column heading to sort. "Proved" counts kernel-checked Lean claims; "same table" is the number of
 undecided machines on the machine's table set (tables one transition apart, up to renaming and mirroring).</p>
 <p class="crumb" id="cnt" aria-live="polite"></p>
 <div class="tw" id="tw"><table id="tbl"><thead><tr>
  <th data-k="rank" aria-sort="ascending">#</th><th data-k="m">machine</th><th data-k="score">score</th><th data-k="stage">what is left</th>
  <th data-k="route">route</th><th data-k="work">work</th><th data-k="fam">family</th><th data-k="kernel">proved</th><th data-k="mates">same table</th>
  <th data-k="next">next step</th><th data-k="why" class="wy">why</th></tr></thead><tbody></tbody></table></div>
</section>

<footer>Generated by <code>holdouts/rank.py</code> from the index rows, every <code>status.json</code>,
<code>holdouts/families.json</code>, <code>tools/collatz/triage.json</code> and <code>tools/number-theory/ranking.json</code>;
the method is in <a href="https://github.com/fractal-geometry-explorer/busy-beaver-explorer/blob/main/holdouts/RANKING.md">holdouts/RANKING.md</a>.
Source: <a href="https://github.com/fractal-geometry-explorer/busy-beaver-explorer">github.com/fractal-geometry-explorer/busy-beaver-explorer</a>.</footer>
</main>
<script type="application/json" id="data">__DATA__</script>
<script>
const $ = id => document.getElementById(id);
const D = JSON.parse($("data").textContent);
const esc = s => String(s ?? "").replace(/[&<>"]/g, c => ({"&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;"})[c]);
const ORDER = D.stages.map(s => s[0]);
const SN = Object.fromEntries(D.stages.map(s => [s[0], s[2]]));
const SM = Object.fromEntries(D.stages.map(s => [s[0], s[3]]));
const byM = Object.fromEntries(D.rows.map(r => [r.m, r]));
function scColor(v) { const t = Math.max(0, Math.min(1, v / 95)); return `hsl(${Math.round(215 - 75 * t)} ${Math.round(35 + 30 * t)}% ${Math.round(46 - 10 * t)}%)`; }
$("attacks").innerHTML = D.attacks.map((a, i) => `<div class="att"><h3><b>${i + 1}</b>${esc(a.title)}</h3>
 <p class="rs">${a.machines.length} machine${a.machines.length === 1 ? "" : "s"} · ${esc(D.route[a.route])} · ${esc(D.work[a.work])}</p>
 <p>${esc(a.what)}</p>${a.need ? `<p class="rs"><b>Resource:</b> ${esc(a.need)}</p>` : ""}
 <details><summary>machines</summary><div class="ml">${a.machines.map(m => `<a href="${esc(byM[m].x)}">${esc(m)}</a>`).join("")}</div></details></div>`).join("");
const counts = {}; for (const r of D.rows) counts[r.stage] = (counts[r.stage] || 0) + 1;
const mx = Math.max(...Object.values(counts));
$("ladder").innerHTML = D.stages.map(([k, b, l, mean]) => `<div class="lrow" title="${esc(mean)}"><span><b>${esc(l)}</b> <span class="cols">base ${b}</span></span>
 <span class="bar" style="width:${100 * (counts[k] || 0) / mx}%"></span><span class="num">${counts[k] || 0}</span></div>`).join("");
for (const [k, , l] of D.stages) $("fs").insertAdjacentHTML("beforeend", `<option value="${k}">${esc(l)}</option>`);
let sortK = "rank", sortD = 1, q = "";
const key = (r, k) => k === "stage" ? ORDER.indexOf(r.stage) : r[k];
function table() {
  const fs = $("fs").value, fr = $("fr").value;
  const vs = D.rows.filter(r => (!fs || r.stage === fs) && (!fr || r.route === fr) &&
    (!q || (r.m + " " + r.id + " " + r.fam + " " + r.next + " " + r.name).toLowerCase().includes(q)))
    .sort((a, b) => { const x = key(a, sortK), y = key(b, sortK); return x < y ? -sortD : x > y ? sortD : a.rank - b.rank; });
  $("tbl").querySelector("tbody").innerHTML = vs.map(r => `<tr><td class="n">${r.rank}</td>
   <td class="m"><a href="${esc(r.x)}">${esc(r.m)}</a>${r.name ? `<br><b>${esc(r.name)}</b>` : ""}<br><span class="cols">bbchallenge ${r.id}</span></td>
   <td class="n"><span class="sc" style="background:${scColor(r.score)}">${r.score}</span></td>
   <td title="${esc(SM[r.stage])}">${esc(SN[r.stage])}</td><td>${esc(D.route[r.route])}</td><td>${esc(D.work[r.work])}</td>
   <td title="${esc(r.famname)}">${esc(r.fam)}</td><td class="n">${r.kernel}${r.map ? `<br><span class="cols">map ${esc(r.map)}</span>` : ""}</td>
   <td class="n">${r.mates}</td><td class="nx">${esc(r.next)}</td><td class="wy">${esc(r.why)}</td></tr>`).join("");
  $("cnt").textContent = `${vs.length} of ${D.rows.length} machines shown.`;
  for (const th of document.querySelectorAll("th")) th.setAttribute("aria-sort", th.dataset.k === sortK ? (sortD > 0 ? "ascending" : "descending") : "none");
}
for (const th of document.querySelectorAll("th")) th.onclick = () => { const k = th.dataset.k; sortD = sortK === k ? -sortD : (["score", "kernel", "mates"].includes(k) ? -1 : 1); sortK = k; table(); };
$("q").oninput = e => { q = e.target.value.trim().toLowerCase(); table(); };
$("fs").onchange = table; $("fr").onchange = table;
$("whytog").onclick = () => { const on = $("whytog").getAttribute("aria-pressed") !== "true"; $("whytog").setAttribute("aria-pressed", on); $("tw").classList.toggle("hide-why", !on); };
table();
</script>
</body>
</html>
"""


def write_page(out, attacks):
    data = {"stages": [[k, b, l, m] for k, (b, l, m) in STAGES.items()], "route": ROUTE, "work": WORK,
            "attacks": attacks,
            "rows": [{k: x[k] for k in ("rank", "m", "id", "score", "stage", "route", "work", "fam", "famname",
                                        "kernel", "map", "mates", "next", "why", "name", "x")} for x in out]}
    head = (build_overview.HEAD.replace("__TITLE__", "Holdouts closest to solved")
            .replace("__DESC__", "The undecided BB(6) holdouts ranked by how close each is to a decision, with the next concrete step for each and the top recommended attacks.")
            .replace("__CSS__", CSS))
    page = head + BODY.replace("__N__", str(len(out))).replace("__ASOF__", ASOF).replace(
        "__DATA__", json.dumps(data, ensure_ascii=False, separators=(",", ":")).replace("</", "<\\/"))
    with open(os.path.join(REPO, "pages", "holdouts", "ranking.html"), "w") as f:
        f.write(page)


def main():
    out, attacks = rank()
    with open(os.path.join(HERE, "ranking.json"), "w") as f:
        json.dump({"_about": "Undecided holdouts ranked by closeness to a decision; written by holdouts/rank.py "
                             "(see RANKING.md). score: judgement from recorded facts, not a probability.",
                   "asof": ASOF, "stages": {k: {"base": b, "label": l, "meaning": m} for k, (b, l, m) in STAGES.items()},
                   "attacks": attacks,
                   "machines": [{k: v for k, v in x.items() if k not in ("x", "p")} for x in out]},
                  f, indent=1, ensure_ascii=False)
        f.write("\n")
    write_md(out, attacks)
    write_page(out, attacks)
    print(f"{len(out)} machines ranked; top: " + ", ".join(f"{x['m']} ({x['score']})" for x in out[:5]))


if __name__ == "__main__":
    main()
