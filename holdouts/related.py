"""Which holdouts are related to which, checked by running them, and the "Related machines" text of their pages.

usage: python3 holdouts/related.py compute [N]     run the checks (N steps a machine, default 10^7; about 20 minutes
                                                   on 4 cores, 400 MB a job) and write holdouts/related.json
       python3 holdouts/related.py apply           write the section into every status.json and README.md concerned
       python3 holdouts/related.py check           exit 1 if `apply` would change a file

Four relations, kept apart because they mean different things for the halting question:

* SAME TABLE, ANOTHER START. Renaming the states, and possibly exchanging left and right, turns one table into the
  other, but the renaming does not keep the start state A. The comparison of the tables is exact (all 720 renamings,
  both orientations). The two runs are runs of one table from two configurations. `tools/c/cfgmatch.c` then looks
  for a configuration common to the two runs, up to a shift of the tape. If there is none in N steps, nothing links
  the two halting questions so far.

* SAME RUN. The tables differ and are not renamings of each other, yet tape and head are identical at every step
  (`tools/c/lockstep.c`, exact). Some pairs part for a few steps and rejoin; those are listed with the number of
  differing steps. Candidates: pairs with equal tapes at two or more of seven checkpoints (`tools/c/tapehash.c`).

* SLOWED-DOWN COPY. With some of the states identified, the configurations of one machine are configurations of the
  other, in the same order, at a constant ratio of step counts. The candidates, with their state maps, are in
  SLOWED.

* SAME TAPES, ANOTHER PACE. Whatever the states, a tenth or more of the configurations of one run have the tape and
  head of a configuration of the other, in the same order and up to the end of the run. Candidates: pairs with 20
  or more common tapes at the moments the head reaches a new cell (`tools/c/tapehash.c`).

Everything about runs is an observation over N steps, not a proof. Where `lean/Twin.lean` exists in a folder
(written by holdouts/twin_lock.py), Lean proves that a pair stays together up to its first "break".
"""
import html
import itertools
import json
import os
import subprocess
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(HERE)
DATA = os.path.join(HERE, "related.json")
S = "ABCDEF"

# (slow machine, fast machine, the state of the fast machine each state of the slow one is read as; '-' none)
SLOWED = [
    ("1RB0RE_1RC0RC_1LD---_0LB1LE_1RF0LD_1RA1RF", "1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF", "AB-CEF"),
]
# The six holdouts with folders at the top of the repository: (README, explainer page), from holdouts/M/.
TOP = {
    "1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LD1RE": ("../../bb6-holdout/README.md", "../../closing-gap-rule-map.html"),
    "1RB1RA_1RC1LB_1LD0RA_---0LE_1LC0LF_1RE0LB": ("../../bb6-1RB1RA_1RC1LB/README.md",
                                                  "../../1RB1RA_1RC1LB/explainer.html"),
    "1RB1RA_1LC1LD_1LD0LB_1RE0RF_---1RD_1RA1RB": ("../../bb6-1RB1RA_1LC1LD/README.md",
                                                  "../../1RB1RA_1LC1LD/explainer.html"),
    "1RB1RA_1RC1LB_1LD0RA_1LB0LE_1LF1LD_---0LD": ("../../bb6-1RB1RA_1RC1LB_1LD0RA_1LB0LE/README.md",
                                                  "../../1RB1RA_1RC1LB_1LD0RA_1LB0LE/explainer.html"),
    "1RB0LF_1RC0LB_1RD1RB_1RE1RF_1LA---_0RC1LA": ("../../bb6-1RB0LF_1RC0LB/README.md",
                                                  "../../1RB0LF_1RC0LB/explainer.html"),
    "1RB1RF_1LC0LB_1RE0LD_1LB0RF_0RA0RC_1RE---": ("../../bb6-1RB1RF_1LC0LB/README.md",
                                                  "../../1RB1RF_1LC0LB/explainer.html"),
}


# ---------------------------------------------------------------------------------------------- the tables

def holdouts():
    """The 608 machines of bbchallenge's list, from the triage."""
    with open(os.path.join(HERE, "triage.json")) as f:
        return [row["machine"] for row in json.load(f)]


def parse(m):
    return [[None if row[i] == "-" else (row[i], row[i + 1], S.index(row[i + 2])) for i in (0, 3)]
            for row in m.split("_")]


def rename(table, perm, mirror):
    """The table with state s called perm[s], and left and right exchanged if `mirror`."""
    out = [None] * 6
    for s in range(6):
        out[perm[s]] = [None if t is None else (t[0], ("L" if t[1] == "R" else "R") if mirror else t[1], perm[t[2]])
                        for t in table[s]]
    return out


def text(table):
    return "_".join("".join("---" if t is None else t[0] + t[1] + S[t[2]] for t in row) for row in table)


PERMS = list(itertools.permutations(range(6)))


def table_classes(machines):
    """The sets of machines with one table up to renaming and mirroring, and for each pair the renaming."""
    canon = {}
    for m in machines:
        t = parse(m)
        canon.setdefault(min(text(rename(t, p, mir)) for p in PERMS for mir in (0, 1)), []).append(m)
    classes = []
    for members in canon.values():
        if len(members) < 2:
            continue
        maps = []
        for a, b in itertools.combinations(members, 2):
            ta, tb = parse(a), parse(b)
            found = [(p, mir) for p in PERMS for mir in (0, 1) if rename(ta, p, mir) == tb]
            assert len(found) == 1, (a, b, found)          # no table of the list has a symmetry
            p, mir = found[0]
            assert p[0] != 0                               # a renaming that kept A would make them one machine
            maps.append({"from": a, "to": b, "states": "".join(S[x] for x in p), "mirror": bool(mir)})
        classes.append({"machines": members, "maps": maps})
    return classes


# ---------------------------------------------------------------------------------------------- the runs

def build(tmp, name):
    exe = os.path.join(tmp, name)
    subprocess.run(["gcc", "-O2", "-o", exe, os.path.join(REPO, "tools", "c", name + ".c")], check=True)
    return exe


def cfgmatch(exe, a, b, states, mirror, n, absolute=False):
    out = subprocess.run([exe, a, b, states, str(int(mirror)), str(n)] + (["abs"] if absolute else []),
                         check=True, capture_output=True, text=True).stdout.split()
    res = {"matches": int(next(w for w in out if w.startswith("matches=")).split("=")[1])}
    pairs = [tuple(int(x) for x in w.strip("()").split(",")) for w in out if w.startswith("(")]
    if pairs:
        res["last"] = list(pairs[-1])
    for w in out:
        for key in ("monotone", "maxgap1", "maxgap2"):
            if w.startswith(key + "="):
                res[key] = int(w.split("=")[1])
    return res


def screen(exe, machines, n):
    """Candidate pairs, from hashes of each run (tools/c/tapehash.c).

    Returns (lock, pace): pairs with the same tape and head at two or more checkpoints, and (a, b, mirror) with
    20 or more common tapes among the first 3000 moments the head reaches a new cell."""
    with ThreadPoolExecutor(os.cpu_count() or 2) as pool:
        outs = list(pool.map(lambda m: subprocess.run([exe, m, str(n)], check=True, capture_output=True,
                                                      text=True).stdout, machines))
    at, plain, mirrored = {}, {}, {}
    for m, out in zip(machines, outs):
        for line in out.splitlines():
            w = line.split()
            if w[0] == "L":
                at.setdefault((w[1], w[2]), []).append(m)
            else:
                plain.setdefault(w[2], set()).add(m)
                mirrored.setdefault(w[3], set()).add(m)
    lock, pace = {}, {}
    for ms in at.values():
        for pair in itertools.combinations(sorted(ms), 2):
            lock[pair] = lock.get(pair, 0) + 1
    for h, ms in plain.items():
        for pair in itertools.combinations(sorted(ms), 2):
            pace[pair + (0,)] = pace.get(pair + (0,), 0) + 1
        for b in mirrored.get(h, ()):
            for a in ms:
                if a < b:
                    pace[(a, b, 1)] = pace.get((a, b, 1), 0) + 1
    return sorted(p for p, k in lock.items() if k >= 2), sorted(p for p, k in pace.items() if k >= 20)


def compute(n):
    machines = holdouts()
    classes = table_classes(machines)
    with tempfile.TemporaryDirectory() as tmp:
        cm, ls, th = build(tmp, "cfgmatch"), build(tmp, "lockstep"), build(tmp, "tapehash")
        lock, pace = screen(th, machines, n)
        with ThreadPoolExecutor(os.cpu_count() or 2) as pool:
            # one table, two starts: is there a common configuration?
            maps = [m for c in classes for m in c["maps"]]
            for m, r in zip(maps, pool.map(lambda m: cfgmatch(cm, m["from"], m["to"], m["states"], m["mirror"], n),
                                           maps)):
                m["shared_configurations"] = r["matches"]
            # the same tape and head step by step (at most 1000 steps apart counts as the same run)
            same = []
            for (a, b), out in zip(lock, pool.map(lambda p: subprocess.run([ls, p[0], p[1], str(n)], check=True,
                                                                           capture_output=True, text=True).stdout,
                                                  lock)):
                r = json.loads(out)
                if r["differing"] <= 1000:
                    same.append({"machines": [a, b], "differing_steps": r["differing"], "first": r["first"],
                                 "last": r["last"], "episodes": r["episodes"], "max_cells": r["maxcells"],
                                 "state_pairs": sorted(r["pairs"]), "unused": [r["unused1"], r["unused2"]]})
            # a slowed-down copy, state for state
            slowed = []
            for slow, fast, states in SLOWED:
                r = cfgmatch(cm, slow, fast, states, 0, n, absolute=True)
                slowed.append({"slow": slow, "fast": fast, "states": states, "matches": r["matches"],
                               "last": r["last"], "in_order": bool(r["monotone"]),
                               "longest_gap": [r["maxgap1"], r["maxgap2"]]})
            # the same tapes at another pace, whatever the states: a tenth of the run or more, to its end, in order
            done = {tuple(sorted(r["machines"])) for r in same} | {tuple(sorted((x[0], x[1]))) for x in SLOWED}
            pace = [p for p in pace if (p[0], p[1]) not in done]
            tapes = []
            for (a, b, mir), r in zip(pace, pool.map(lambda p: cfgmatch(cm, p[0], p[1], "blind", p[2], n), pace)):
                if r["matches"] * 10 >= n and r.get("monotone") and max(r["last"]) * 10 >= 9 * n:
                    tapes.append({"machines": [a, b], "mirror": bool(mir), "matches": r["matches"],
                                  "last": r["last"]})
    with open(DATA, "w") as f:
        json.dump({"steps": n, "same_table": classes, "same_run": same, "slowed": slowed, "same_tapes": tapes},
                  f, indent=1)
        f.write("\n")
    bad = [m for m in maps if m["shared_configurations"]]
    print(f"{len(classes)} tables shared by {sum(len(c['machines']) for c in classes)} machines, {len(maps)} pairs, "
          f"{len(bad)} with a common configuration in {n} steps; {len(same)} pairs with the same run; "
          f"{len(tapes)} pairs with the same tapes at another pace")


# ---------------------------------------------------------------------------------------------- the text

def fmt(n):
    return f"{n:,}"


def power(n):
    e = len(str(n)) - 1
    return (f"10^{e}", f"10<sup>{e}</sup>") if n == 10 ** e else (fmt(n), fmt(n))


class Out:
    """One text, written as Markdown (README) and as HTML (pages)."""

    def __init__(self, md):
        self.md = md

    def link(self, m):
        readme, page = TOP.get(m, (f"../{m}/README.md", f"../{m}/explainer.html"))
        return f"[`{m}`]({readme})" if self.md else f'<a href="{page}">{m}</a>'

    def b(self, s):
        return f"**{s}**" if self.md else f"<b>{s}</b>"

    def code(self, s):
        return f"`{s}`" if self.md else f"<code>{html.escape(s)}</code>"

    def n(self, steps):
        return power(steps)[0 if self.md else 1]


def arrows(states):
    return ", ".join(f"{S[i]}→{c}" for i, c in enumerate(states))


def invert(states):
    return "".join(S[states.index(c)] for c in S)


def relations(data):
    """machine -> list of (kind, record, index of the machine in the record)."""
    rel = {}
    for r in data["same_run"]:
        for i, m in enumerate(r["machines"]):
            rel.setdefault(m, []).append(("run", r, i))
    for r in data["slowed"]:
        rel.setdefault(r["slow"], []).append(("slow", r, 0))
        rel.setdefault(r["fast"], []).append(("slow", r, 1))
    for r in data.get("same_tapes", []):
        for i, m in enumerate(r["machines"]):
            rel.setdefault(m, []).append(("tapes", r, i))
    for c in data["same_table"]:
        for mp in c["maps"]:
            rel.setdefault(mp["from"], []).append(("table", mp, 0))
            rel.setdefault(mp["to"], []).append(("table", mp, 1))
    return rel


def lean_twin(machine, other, o, slowed=False):
    """What lean/Twin.lean proves about the pair, if one of the two folders has it."""
    for m in (machine, other):
        if os.path.isfile(os.path.join(HERE, m, "lean", "Twin.lean")):
            where = o.code("lean/Twin.lean") + (" here" if m == machine else " in the other machine's folder")
            together = ("each step of the faster machine is matched by one or three steps of the slower one" if slowed
                        else "the two runs have the same tape, the same head position and paired states")
            name = "sim_or_break" if slowed else "lock_or_break"
            return (f" Lean proves ({where}, {o.code(name)}, {o.code('not_halts_of_noBreak')}) that {together} up "
                    f"to the first break, a configuration where the paired states act differently, and that "
                    f"neither machine halts if no break ever comes. A halt of either machine is itself a break, "
                    f"and the halting transitions of the two do not correspond, so the two are not known to halt "
                    f"together.")
    return " If the agreement lasts for ever neither machine halts; that it lasts is not proved."


def paragraphs(machine, rels, steps, o):
    """The paragraphs of the section for one machine."""
    ps = []
    n = o.n(steps)
    tapes = [(r, i) for kind, r, i in rels if kind == "tapes"]
    tables = [(r, i) for kind, r, i in rels if kind == "table"]
    for kind, r, i in rels:
        if kind in ("tapes", "table"):
            continue
        if kind == "run":
            other = r["machines"][1 - i]
            pairs = [p if i == 0 else p[2] + "–" + p[0] for p in r["state_pairs"]]
            pairs = sorted(p.replace("-", "–") for p in pairs)
            one_to_one = len({p[0] for p in pairs}) == len(pairs) == len({p[2] for p in pairs})
            unused = ("this machine never uses " + (", ".join(r["unused"][i]) or "none") +
                      " and the other never uses " + (", ".join(r["unused"][1 - i]) or "none"))
            if r["differing_steps"] == 0:
                ps.append(
                    o.b(f"Same run as {o.link(other)} (observed, not proved).") +
                    f" At every one of the first {n} steps from blank tape the two machines have the same tape "
                    f"and the head on the same cell. Their tables differ, and no renaming of the states turns one "
                    f"into the other. While they run, the states pair up as {', '.join(pairs)} (this machine "
                    f"first)" + ("" if one_to_one else ", which is not one to one") +
                    f". Transitions not used in these steps: {unused}." + lean_twin(machine, other, o))
            else:
                ps.append(
                    o.b(f"Almost the same run as {o.link(other)} (observed, not proved).") +
                    f" Tape and head are the same at all but {fmt(r['differing_steps'])} of the first {n} steps "
                    f"from blank tape. The two runs part {r['episodes']} times, each time for a step or two and by "
                    f"{'one cell' if r['max_cells'] == 1 else 'at most ' + str(r['max_cells']) + ' cells'}, first at "
                    f"step {fmt(r['first'])} and last at step {fmt(r['last'])}, and come together again. The tables "
                    f"differ and are not renamings of each other. While the runs agree, the states pair up as "
                    f"{', '.join(pairs)} (this machine first).")
        elif kind == "slow":
            other = r["fast"] if i == 0 else r["slow"]
            ident = ", ".join(f"{S[k]} as {c}" for k, c in enumerate(r["states"]) if c != "-")
            ratio = r["last"][0] / r["last"][1]
            if i == 0:
                ps.append(
                    o.b(f"A slowed-down copy of {o.link(other)} (observed, not proved).") +
                    f" Read this machine's states {ident} of the other machine. Then {fmt(r['matches'])} of this "
                    f"machine's first {n} configurations (tape, head position and state) are configurations of the "
                    f"other machine, in the same order. The last one is step {fmt(r['last'][0])} here and step "
                    f"{fmt(r['last'][1])} there, so this machine takes about {ratio:.1f} times as many steps. At "
                    f"most {r['longest_gap'][0]} steps pass here between two such configurations. The tables are "
                    f"not renamings of each other." + lean_twin(machine, other, o, True))
            else:
                ps.append(
                    o.b(f"{o.link(other)} is a slowed-down copy of this machine (observed, not proved).") +
                    f" Read that machine's states {ident} of this machine. Then {fmt(r['matches'])} of its first "
                    f"{n} configurations (tape, head position and state) are configurations of this machine, in "
                    f"the same order. The last one is step {fmt(r['last'][0])} there and step {fmt(r['last'][1])} "
                    f"here, so it takes about {ratio:.1f} times as many steps. The tables are not renamings of "
                    f"each other." + lean_twin(machine, other, o, True))
    if tables:
        items, shared = [], 0
        for r, i in tables:
            other = r["to"] if i == 0 else r["from"]
            states = r["states"] if i == 0 else invert(r["states"])
            start = invert(states)[0]                 # the state of this machine that the other's A is
            shared += r["shared_configurations"]
            items.append(f"{o.link(other)}: rename {arrows(states)}" +
                         (" and exchange left and right" if r["mirror"] else "") +
                         f"; it is this table started in state {start}" + (", in a mirror" if r["mirror"] else "") +
                         (f"; {fmt(r['shared_configurations'])} common configurations"
                          if r["shared_configurations"] else ""))
        many = len(items) > 1
        head = (o.b(f"Same table as {'the machines' if many else 'the machine'} below, started in another state.") +
                f" Renaming the states as shown turns this machine's table into the other one, the halting "
                f"transition included. The other machine starts in its own state A, which is not this machine's "
                f"A: its run from blank tape is the run of this table started in another state. ")
        if shared == 0:
            head += (f"These are different runs: in the first {n} steps of each, no configuration of this machine's "
                     f"run occurs in {'any of the others' if many else 'the other'}, even up to a shift of the "
                     f"tape. So each of these holdouts is its own halting question, and settling one does not "
                     f"settle another.")
        else:
            head += f"Common configurations in the first {n} steps of each, up to a shift of the tape, are listed."
        if o.md:
            ps.append(head + "\n\n" + "\n".join("- " + it for it in items))
        else:
            ps.append(head + "</p><ul>" + "".join(f"<li>{it}</li>" for it in items) + "</ul><p>")
    if tapes:
        items = []
        for r, i in tapes:
            other = r["machines"][1 - i]
            here, there = r["last"][i], r["last"][1 - i]
            items.append(f"{o.link(other)}{' (in a mirror)' if r['mirror'] else ''}: {fmt(r['matches'])} "
                         f"configurations, the last at step {fmt(here)} here and step {fmt(there)} there")
        head = (o.b("Same tapes at another pace (observed, not proved).") +
                f" Leave the states aside and compare only the tape and the place of the head. Then a large part of "
                f"the first {n} configurations of this machine are configurations of the machines below, in the "
                f"same order and up to the end of the run. The steps at which they occur differ, the tables are "
                f"not renamings of each other, and equal tapes with different states may be continued "
                f"differently, so this does not tie the halting questions together.")
        if o.md:
            ps.append(head + "\n\n" + "\n".join("- " + it for it in items))
        else:
            ps.append(head + "</p><ul>" + "".join(f"<li>{it}</li>" for it in items) + "</ul><p>")
    return ps


INTRO = ("Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; "
         "everything about runs was checked on the first {n} steps of each machine and is an observation, not a "
         "proof ({tools}).")
BEGIN, END = "<!-- related machines: written by holdouts/related.py -->", "<!-- end of related machines -->"
SECTION_ID = "related-machines"
CLAIM_TITLE = "Related holdouts"


def claim_text(rels, steps):
    o = Out(False)
    n = o.n(steps)
    parts = []
    for kind, r, i in rels:
        if kind == "run":
            other = r["machines"][1 - i]
            parts.append(f"The same tape and head as {other} at " +
                         ("every one" if not r["differing_steps"] else f"all but {r['differing_steps']}") +
                         f" of the first {n} steps (the tables differ).")
        elif kind == "slow":
            parts.append(f"{r['slow']} goes through {fmt(r['matches'])} configurations of {r['fast']} in its first "
                         f"{n} steps, in order, about {r['last'][0] / r['last'][1]:.1f} times slower.")
        elif kind == "tapes":
            continue
        else:
            other = r["to"] if i == 0 else r["from"]
            parts.append(f"The same table as {other} up to renaming" + (" and mirroring" if r["mirror"] else "") +
                         f", started in another state; {'no' if not r['shared_configurations'] else r['shared_configurations']}"
                         f" common configuration in the first {n} steps of each.")
    k = sum(1 for kind, r, i in rels if kind == "tapes")
    if k:
        parts.append(f"The same tapes at another pace, whatever the states, as {k} other holdout{'s' if k > 1 else ''} "
                     f"(listed on the explainer page).")
    return " ".join(parts)


def dump_like(raw, obj):
    """Serialize as the file was (the folders do not all use the same options)."""
    old = json.loads(raw)
    for kw in (dict(indent=1, ensure_ascii=False), dict(indent=1), dict(indent=2, ensure_ascii=False),
               dict(indent=2)):
        for end in ("\n", ""):
            if json.dumps(old, **kw) + end == raw:
                return json.dumps(obj, **kw) + end
    return json.dumps(obj, indent=1, ensure_ascii=False) + "\n"


_data = None


def data():
    global _data
    if _data is None:
        with open(DATA) as f:
            d = json.load(f)
        _data = (d["steps"], relations(d))
    return _data


def with_related(machine, spec):
    """The status spec with the section and the claim for the machine (without them if it has no relation)."""
    steps, rel = data()
    if machine not in rel:
        if "explainer" in spec and any(x.get("id") == SECTION_ID for x in spec["explainer"].get("sections", [])):
            spec = dict(spec, explainer=dict(spec["explainer"], sections=[
                x for x in spec["explainer"]["sections"] if x.get("id") != SECTION_ID]))
        if any(c.get("title") == CLAIM_TITLE for c in spec.get("claims", [])):
            spec = dict(spec, claims=[c for c in spec["claims"] if c.get("title") != CLAIM_TITLE])
        return spec
    rels = rel[machine]
    o = Out(False)
    tools = "<code>holdouts/related.py</code>, <code>holdouts/related.json</code>"
    section = {"id": SECTION_ID, "eyebrow": "Family", "heading": "Related machines",
               "html": ["<p>" + INTRO.format(n=o.n(steps), tools=tools) + "</p>"] +
                       [("<p>" + p + "</p>").replace("<p></p>", "") for p in paragraphs(machine, rels, steps, o)]}
    spec = dict(spec)
    spec["explainer"] = dict(spec.get("explainer", {}))
    spec["explainer"]["sections"] = [x for x in spec["explainer"].get("sections", [])
                                     if x.get("id") != SECTION_ID] + [section]
    claim = {"level": "trusted", "title": CLAIM_TITLE, "text": claim_text(rels, steps),
             "where": "<code>holdouts/related.json</code>, written by <code>holdouts/related.py compute</code> "
                      "(<code>tools/c/cfgmatch.c</code>, <code>tools/c/lockstep.c</code>)"}
    spec["claims"] = [c for c in spec.get("claims", []) if c.get("title") != CLAIM_TITLE] + [claim]
    return spec


def readme_with(machine, raw):
    """The README with the section for the machine (without it if it has no relation)."""
    steps, rel = data()
    if machine not in rel:
        if BEGIN in raw:
            head, rest = raw.split(BEGIN, 1)
            tail = rest.split(END, 1)[1].lstrip("\n")
            return head.rstrip("\n") + "\n" + (("\n" + tail) if tail else "")
        return raw
    o = Out(True)
    block = "\n\n".join([BEGIN, "## Related machines",
                         INTRO.format(n=o.n(steps), tools="`holdouts/related.py`, `holdouts/related.json`")] +
                        paragraphs(machine, rel[machine], steps, o) + [END]) + "\n"
    if BEGIN in raw:
        head, rest = raw.split(BEGIN, 1)
        tail = rest.split(END, 1)[1].lstrip("\n")
        return head + block + (("\n" + tail) if tail else "")
    return raw.rstrip("\n") + "\n\n" + block


def new_files(machine):
    """(path, old text, new text) for the status.json and README.md of one machine."""
    d = os.path.join(HERE, machine)
    out = []
    path = os.path.join(d, "status.json")
    with open(path) as f:
        raw = f.read()
    out.append((path, raw, dump_like(raw, with_related(machine, json.loads(raw)))))
    path = os.path.join(d, "README.md")
    with open(path) as f:
        raw = f.read()
    out.append((path, raw, readme_with(machine, raw)))
    return out


def apply(write):
    changed = []
    for machine in sorted(os.listdir(HERE)):
        if not os.path.isfile(os.path.join(HERE, machine, "status.json")):
            continue
        for path, old, new in new_files(machine):
            if old != new:
                changed.append(os.path.relpath(path, REPO))
                if write:
                    with open(path, "w") as f:
                        f.write(new)
    return changed


def main(argv):
    cmd = argv[0] if argv else ""
    if cmd == "compute":
        compute(int(argv[1]) if len(argv) > 1 else 10 ** 7)
    elif cmd == "apply":
        print(f"{len(apply(True))} files written")
    elif cmd == "check":
        changed = apply(False)
        print("\n".join(changed) or "current")
        sys.exit(1 if changed else 0)
    else:
        sys.exit(__doc__)


if __name__ == "__main__":
    main(sys.argv[1:])
