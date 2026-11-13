"""Write README.md and status.json for one machine of the wall-counter family 1RB0RC_1LC0RD_0LD0LC_1RE0LA_*.

usage: python3 family_status.py MACHINE STATS.json

STATS.json is written by `walls.py` (the counts from one long run).  The generated "shape" section of the explainer
and the bounded-run claims are kept; the rest is replaced.
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
HOLD = os.path.join(HERE, "..", "..")
FAMILY = ["1RB0RC_1LC0RD_0LD0LC_1RE0LA_0LE1RF_0RA---", "1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0LB---",
          "1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0RD---", "1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_1LB---",
          "1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA1RF_0RE---"]
LEAD = "1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0RD---"


def fmt(n):
    return f"{n:,}"


def sup(n):
    """10^k for a power of ten, else the number with commas."""
    s = str(n)
    if s.startswith("1") and set(s[1:]) <= {"0"} and len(s) > 4:
        return f"10<sup>{len(s) - 1}</sup>"
    return fmt(n)


def code(s):
    return "<code>" + s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;") + "</code>"


def merger_claim(st):
    col = st["col"]          # outcome -> number of (pair, gap) cases, from py/collisions.py
    n = sum(col.values())
    other = {k: v for k, v in col.items() if k not in ("STD", "HALT")}
    rest = ("; " + ", ".join(f"{v} stopped unresolved ({k})" for k, v in other.items())) if other else ""
    if col.get("HALT"):
        return {"level": "trusted", "title": "Some mergers halt",
                "text": f"Of {n} merger cases run symbolically (36 pairs of wall shapes, gaps of 0 to 2 blocks), {col['HALT']} "
                        f"end in a halt{rest}. Whether such a merger ever occurs from blank tape is the question.",
                "where": "<code>py/collisions.py</code>"}
    return {"level": "trusted", "title": "The mergers tried end without a halt",
            "text": "A symbolic run (head, literal cells and repeated blocks with variable counts, any tape R beyond) from "
                    "<code>0^&infin; D&gt; (1000)^(x+3) W₁ (1000)^g W₂ (1000)^(y+6) W₃ (1000)^(z+4) R</code>, for each of the 36 "
                    f"pairs of shapes W₁, W₂ and each gap g = 0, 1, 2: {col.get('STD', 0)} of the {n} cases return to the "
                    f"ordinary form without a halt{rest}, and none halts. It is evidence, not a proof: mergers deeper in the "
                    "tape have another wall near on the left, and the edge events (a wall reaching the right end, the "
                    "overflow) are not covered.",
            "where": "<code>py/collisions.py</code>"}


def write(machine, st):
    folder = os.path.join(HOLD, machine)
    spec = json.load(open(os.path.join(folder, "status.json")))
    tbl = machine.split("_")
    erow, frow = tbl[4], tbl[5]
    e1 = st["e1"]
    if machine == FAMILY[0]:
        f_role = ("Here E's 1-transition (<code>1RF</code>) is part of every sweep, and F always reads a 0 there "
                  f"(<code>F0 → 0RA</code>): in {sup(st['steps'])} steps F was entered {fmt(e1)} times and never read a 1.")
    else:
        f_role = (f"State F is reached only through E reading a 1, which an ordinary sweep never does: in "
                  f"{sup(st['steps'])} steps it happened {fmt(e1)} times, never in an ordinary sweep or carry (their Lean "
                  f"proofs never pass through F) but in the rare events, and each time F read a 0 (<code>F0 → {frow[:3]}</code>).")
    others = [m for m in FAMILY if m != machine]
    sample = st["sample"]
    spec["generated"] = False
    spec["family"] = "wall counter (base 5, drifting walls)"
    spec["summary"] = ("A base-5 counter: the tape is runs of the block 1000 split by walls that each cycle through five "
                       "shapes; a bouncer sweeps from the left end to the first wall, walls drift right and merge, and "
                       "the right end grows only when every digit overflows.")
    spec["decision"] = "open"
    spec["verdict"] = [
        "<b>The question is open.</b> The machine is a base-5 counter written as walls in a sea of <code>1000</code> "
        "blocks (described below; its one-sweep and carry rules are proved in Lean). It can halt only during a rare "
        "event, the merger of two walls; every merger type tried symbolically (both walls in any of their six shapes, "
        "0 to 2 blocks apart) ends without halting, and the C simulator finds no halt in the first "
        f"{sup(st['steps'])} steps. A proof would have to cover every merger and edge event; that has not been done."]
    keep = [c for c in spec["claims"] if c["level"] in ("kernel", "native") or c["title"].startswith("No halt in the first 10<sup>9")]
    claims = keep + [
        {"level": "kernel", "title": "The sweep and carry rules",
         "text": "With the head in state D on the first 1 at the left end, <code>0^&infin; D&gt; (1000)^(x+1) W (1000)^(y+1) R</code>, "
                 "one sweep moves the first wall W one step along its cycle <code>1001 → 1001100 → 100110 → 10011 → 10010 → 1001</code>, "
                 "for every x, y and every tape R (four theorems, one per shape that does not carry). From <code>10011</code> the sweep "
                 "carries: it also moves the second wall one step (four theorems, one per shape of the second wall that does not carry "
                 "on). The step counts are linear in x.",
         "where": "<code>sweep_w0</code> &hellip; <code>sweep_w4</code>, <code>carry_w0</code> &hellip; <code>carry_w4</code>, <code>lean/Walls.lean</code>"},
        {"level": "trusted", "title": f"No halt in the first {sup(st['steps'])} steps",
         "text": f"The C simulator ({code('tools/c/tm.h')}) runs {sup(st['steps'])} steps without a halt; at the end the tape has "
                 f"{st['walls_end']} walls. Along the way the counter overflowed {st['overflows']} times (every wall in shape "
                 f"<code>10011</code> at once: the carry runs off the right end and the tape grows there) and walls merged "
                 f"{st['collisions']} times.",
         "where": "<code>py/walls.py</code> in the folder of " + LEAD.replace("---", "") + "&hellip;"},
        {"level": "trusted", "title": "Where F comes in", "text": f_role, "where": "<code>py/walls.py</code>"},
        merger_claim(st),
        {"level": "computed", "title": "n-gram CPS fails", "text": "The n-gram closed position set decider of the Coq-BB5 paper finds "
         "a (spurious) path to the halt for windows of 3 to 7 cells with or without history, and for the lead machine of the "
         "family up to 40 cells: windows cannot tell how the walls are spaced.", "where": "<code>tools/c/ngramcps.c</code>"},
        {"level": "open", "title": "Does it halt from blank tape?",
         "text": "Not known. It would halt only if some merger of walls (or edge event) put E on a 1 followed by a 1. "
                 "The mergers tried never do, which suggests it never halts; a proof needs a closed description of every "
                 "configuration between samples (a regular language over walls and gaps), which is the next thing to try.",
         "where": ""},
    ]
    spec["claims"] = claims
    for c in spec["claims"]:
        if c["level"] == "computed":
            c["level"] = "trusted"
    spec["explainer"]["lede"] = (
        "Nobody knows, but the machine has a clear structure: it is a <b>base-5 counter</b>. The tape is long runs of the "
        "block <code>1000</code> broken by short <em>walls</em>; each wall is one digit, and its shape is the digit's value. "
        "A head bouncing between the left end and the first wall counts the sweeps.")
    spec["explainer"]["facts"] = [
        {"level": "trusted", "value": sup(st["steps"]) + " steps", "text": "No halt in the C simulator."},
        {"level": "kernel", "value": "8 rules", "text": "One sweep and one carry, for every size, proved in Lean."},
        {"level": "heuristic", "value": "base 5", "text": "Each wall cycles through five shapes."},
    ]
    shape = [s for s in spec["explainer"]["sections"] if s["id"] == "shape"]
    secs = [
        {"id": "walls", "eyebrow": "Macro structure", "heading": "Blocks and walls",
         "html": [
             "<p>Stop the machine each time its head is back at the left end of the tape, in state D on a 1. The tape always "
             "reads the same way: runs of the four-cell block <code>1000</code>, separated by short <em>walls</em>. Written "
             "<code>c</code> for the block and the walls by their cells, here is the tape of " + code(machine) + f" at step {fmt(sample['step'])}:</p>",
             "<p><code>" + sample["text"] + "</code></p>",
             "<p>A wall is always one of five words, <code>1001</code>, <code>1001100</code>, <code>100110</code>, <code>10011</code>, "
             "<code>10010</code>, or a single <code>0</code> (a digit that has not started counting yet, see below), and the tape "
             "ends on the right with <code>1001</code>. In the middle of a merger, described below, a wall can briefly be a "
             "longer word.</p>"]},
        {"id": "sweeps", "eyebrow": "Macro structure", "heading": "One sweep moves one digit",
         "html": [
             "<p>From the left end the head runs right over the first run of blocks, turning each <code>1000</code> into "
             "<code>0101</code> in four steps, and stops at the first wall. It changes the wall's shape and walks back, "
             "zigzagging six steps per block and turning <code>0101</code> back into <code>1000</code>. The run in front "
             "grows by one block, so the sweeps get longer and the left side of the tape grows like the square root of "
             "the time: that is the bouncer half of the growth shape.</p>",
             "<p>The wall's shape goes round a cycle of five: <code>1001 → 1001100 → 100110 → 10011 → 10010 → 1001</code>. "
             "The step from <code>10011</code> to <code>10010</code> is the <b>carry</b>: on that sweep the head does not "
             "turn at the first wall but goes on to the second and moves it one step too (and if that one is also at "
             "<code>10011</code>, on to the third). So the walls are the digits of the number of sweeps written in base 5, "
             "the first wall the lowest digit. Lean proves these rules for runs of any length (<code>lean/Walls.lean</code>).</p>",
             "<p>When every wall is at <code>10011</code> the carry runs through all of them to the right end: the tape grows "
             "there by three cells, every wall becomes a single <code>0</code>, and a new lowest digit is born at the left end. "
             "A <code>0</code> wall becomes <code>1001</code> the first time a carry reaches it, and stops the carry. So the "
             "counter gains a digit at each overflow, the overflows come about five times further apart each time, and the "
             f"right end of the tape grows like a logarithm of the time. In {sup(st['steps'])} steps there were {st['overflows']} overflows.</p>"]},
        {"id": "mergers", "eyebrow": "Emergent behavior", "heading": "Drifting walls and mergers",
         "html": [
             "<p>A plain counter would be easy to prove non-halting. This one is not plain, because the walls move. Each time "
             "a wall goes round its cycle it shifts two blocks to the right, so a low digit drifts right faster than the "
             "digit after it and the run between them shrinks. When it is used up the two walls <b>merge</b>: for a few "
             "sweeps the wall is a longer word, then one ordinary wall is left and a new lowest digit is born at the left end. In "
             f"{sup(st['steps'])} steps walls merged {st['collisions']} times.</p>",
             "<p>When a merger happens, and with which shapes, depends on the whole history of the counter: it is the "
             "kind of arithmetic that makes these machines hard. " + f_role + "</p>",
             "<p>The variants of this family share states A to D and differ only in E and F, that is, only in what a merger "
             "does: " + ", ".join(code(m) for m in others) + ". Every merger tried by symbolic simulation (36 pairs of "
             "shapes, gaps of 0 to 2 blocks) ends in the ordinary form without a halt, which points to a machine that "
             "never halts. Turning that into a proof means describing every configuration, mergers and edge events "
             "included, by a finite set of patterns that the machine maps into itself.</p>"]},
    ]
    spec["explainer"]["sections"] = secs + shape
    spec["check"] = [c for c in spec["check"] if "check.sh" in c or "lean.sh" in c] + [
        "python3 holdouts/" + LEAD + "/py/wall_rules.py " + machine + "   # writes lean/Walls.lean",
        "python3 holdouts/" + LEAD + "/py/walls.py " + machine + " 1000000000   # the counts"]
    json.dump(spec, open(os.path.join(folder, "status.json"), "w"), indent=1, ensure_ascii=False)
    open(os.path.join(folder, "status.json"), "a").write("\n")
    readme(machine, spec, st, f_role, others)


def strip(h):
    import re
    h = re.sub(r"<sup>([^<]*)</sup>", r"^\1", h)
    return re.sub(r"<[^>]+>", "", h).replace("&gt;", ">").replace("&lt;", "<").replace("&amp;", "&").replace("&infin;", "∞").replace("&hellip;", "…")


def readme(machine, spec, st, f_role, others):
    folder = os.path.join(HOLD, machine)
    old = open(os.path.join(folder, "README.md")).read()
    table = old[old.index("| state |"):old.index("## Status")].strip()
    sample = st["sample"]
    lines = [f"# {machine}", "",
             f"bbchallenge id {spec.get('id', st['id'])}. One of the six-state holdouts. **A base-5 counter of drifting walls**; "
             "whether it halts is open.", "", table, "",
             "## What it does", "",
             "Sample the run each time the head is at the left end in state D reading a 1. The tape is then runs of the "
             "block `1000` (written `c`) separated by **walls**, each one of the five words `1001`, `1001100`, `100110`, `10011`, `10010` or a single `0`, and ends with `1001`:", "",
             f"    step {fmt(sample['step'])}:  {strip(sample['text'])}", "",
             "- **A sweep.** The head crosses the first run rightwards (`1000` becomes `0101`, 4 steps a block), changes the "
             "first wall, and zigzags back (6 steps a block, `0101` back to `1000`). The first run grows by a block a sweep, "
             "so the left side of the tape grows like √t (the *sqrt* side of the triage).",
             "- **Digits.** A wall cycles `1001 → 1001100 → 100110 → 10011 → 10010 → 1001`; the step out of `10011` carries "
             "into the next wall. The walls are the base-5 digits of the number of sweeps, lowest first. The right end moves "
             f"only when every digit is at `10011` (an overflow): every wall becomes a single `0` (a digit that turns into `1001` "
             f"at the next carry that reaches it) and a new lowest digit is born at the left end, so overflows come about five times "
             f"further apart each time: logarithmic growth (the *exp* side). {st['overflows']} overflows in {fmt(st['steps'])} steps.",
             "- **Drift and mergers.** A wall shifts right by two blocks per cycle, so lower digits catch up with higher ones; "
             f"when the run between two walls is used up they merge into one ({st['collisions']} mergers in {fmt(st['steps'])} steps).",
             f"- **Halting.** The only halt is F reading a 1. {strip(f_role)}", "",
             "The family shares states A–D and differs in E and F (that is, in what a merger does): "
             + ", ".join(f"`{m}`" for m in others) + ". The lead machine's folder (`" + LEAD + "`) holds the family's scripts.", "",
             "## What is proved, computed, conjectured", ""]
    for c in spec["claims"]:
        t = strip(c['title'])
        lines.append(f"- **{c['level']}**: {t}{'' if t.endswith('?') else '.'} {strip(c['text'])}" + (f" ({strip(c['where'])})" if c["where"] else ""))
    lines += ["", "## Notes for later", "",
              "A non-halting proof looks within reach but is more than a day of work: describe the configurations at the "
              "sample points as walls and gaps (gaps as exact small values or a symbolic n + k), prove the sweep, carry, "
              "merger and edge rules for every combination that can occur (the merger runs of `py/collisions.py` are the "
              "start), and show the set is closed. A closed-tape-language search over macro tokens (blocks and walls instead "
              "of cells) is the other route; windows of cells (n-gram CPS up to 40) are not enough.", "",
              "## Pages", "",
              f"- [`pages/holdouts/{machine}/explainer.html`](../../pages/holdouts/{machine}/explainer.html)",
              f"- [`pages/holdouts/{machine}/proof-status.html`](../../pages/holdouts/{machine}/proof-status.html)", "",
              "## Check", "", "```sh", f". /etc/profile.d/lean.sh && holdouts/{machine}/lean/check.sh",
              f"python3 holdouts/{LEAD}/py/walls.py {machine} 1000000000", "```", ""]
    open(os.path.join(folder, "README.md"), "w").write("\n".join(lines))


if __name__ == "__main__":
    write(sys.argv[1], json.load(open(sys.argv[2])))
